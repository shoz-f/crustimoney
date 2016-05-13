package crustimoney;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Keyword;
import clojure.lang.PersistentHashMap;
import clojure.lang.Symbol;
import clojure.lang.Var;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

// TODO
// - rule rewriting with ?, + and *
// - left recursion detection
// - packrat configuration (configure minimal pack length, limit rats by max number per rule, etc)
// - check grammar for errors
// - support cuts?

// We want to parse some text input, using the datastructure-based
// grammar directly. This needs to be done in such a way that we do
// not build a (too) large stack of function/method calls. Thus, we
// require a structure/object that keeps track of the state while
// parsing, and some functions on this state to advance the state.
//
// The State class below is a structure that does just that. In this
// case it is implemented in Java, to leverage mutability for speed,
// but the model we will use works just as well in a functional,
// immutable fashion.
//
// Let's define our class State.
public class State {

  // We store our grammar in the State object, because we constantly
  // need it when parsing. A grammar is a mapping from keywords to
  // grammar rules. There are three type of rules.
  //
  // A rule can be a keyword, to refer to anothor grammar rule. A rule
  // can be a terminal, such as a String or a regular expression,
  // which are used to define the tokens.
  //
  // A rule can also be a List, having a sequence of grammar rules
  // that must be parsed succesively. Multiple sequences can be
  // defined inside this List, separated by a slash. If the first
  // sequence fails to parse, the second will be tried, and so on.
  private final Map<Keyword, Object> grammar;

  // In order to know where our grammar starts, we keep track of
  // the keyword pointing to the first grammar rule.
  private final Keyword start;

  // Of course, we also keep track of the input text. During parsing,
  // this object does not change. However, one of the features of this
  // parser is to incrementially change the input, therefore it is not
  // declared final.
  private String input;

  // Now that we have defined our static values, we come to the heart
  // of the parsing algorithm: the steps. The state in which the
  // parser is at any point in time, is tracked inside this list. This
  // list grows and shrinks during parsing, and contains Step objects.
  //
  // Later we'll discuss what a Step contains and how this steps list
  // is used, but for now it it sufficient to know that a Step
  // contains a grammar rule and the position it is at regarding the
  // input text.
  //
  // We create an ArrayList here, because we need random access a lot
  // while parsing.
  private final List<Step> steps = new ArrayList<>();

  // We also keep track of errors during parsing. The errors Set
  // contains the errors that were found at the errorsPos integer
  // below. Whenever an error is found, it is added to the Set.
  // However, the set is cleared whenever this error was found
  // on a different position than the errorsPos field.
  private final Set<String> errors = new HashSet<>();
  private int errorsPos = -1;

  // We also want to know whether the algorithm finds that it is
  // done parsing, either successfully or not.
  private boolean done = false;

  // To speed up the parsing process, this parser implements the
  // packrat pattern. The rats Map maps previously and successfully
  // parsed Step objects to the Step objects that followed that Step.
  // How this rats Map is used, is discussed further on in the
  // `advance` and `backward` methods.
  private final Map<Step, List<Step>> rats = new HashMap<>();

  // As previously stated, the parser uses a position number to keep
  // track of where it is (or was) in the input. A more human friendly
  // representation is the combination of a line number and the column
  // number. The lines TreeMap below acts as a cache whenever this
  // representation is requested through the `posToLineColumn` method.
  //
  // The Map maps position numbers that are at a new line, to the line
  // number they start. For instance, position 0 always maps to line
  // 1.
  private final TreeMap<Integer, Integer> lines = new TreeMap<>();


  // Now that we have our fields defined, we need to define what a
  // Step actually represents.
  public static class Step {
    // The core of a Step is declaring that a grammar rule will or is
    // parsed at a certain position in the input. Again, this grammar
    // rule can be a Keyword, a terminal or a List. The position
    // number does not change during parsing. However, since
    // incremental parsing is supported, the pos field may change
    // between parses, therefore it is not declared final.
    private final Object rule;
    private int pos;

    // Whenever the grammar rule object is a List, the Step also keeps
    // track of where the parsing is (or was) in that List. We will
    // see later how this works exactly.
    //
    // Because of this ruleIndex field, the List rule object is never
    // changed, which is important for the hashCode and equals
    // implementation of Step.
    private int ruleIndex;

    // If a Step is parsed successfully, the end position is recorded
    // as well.
    //
    // Recording this position has two benefits. Firstly, we need to
    // know whether a Step is successfully parsed already whenever we
    // backtrack (we will see this later on). Secondly, we need this
    // end position for the incremental parsing.
    private int endPos = -1;

    // If the grammar rule of a Step is a terminal, and it is parsed
    // succesfully, its value is recorded inside the Step as well.
    private String value = null;

    // Creating a new Step is private to the parser. It only requires
    // the core fields of a Step: the grammar rule and the position.
    private Step(final Object rule, final int pos) {
      this.rule = rule;
      this.pos = pos;
      // If the rule is a List, we start recording the position in
      // this List.
      this.ruleIndex = rule instanceof List ? 0 : -1;
    }

    // The Step objects are also what is returned as the parsing
    // result, if successful. Therefore, we need some accessors that
    // allow read-only access to the Step contents.
    public Object rule() {
      return rule;
    }

    public int pos() {
      return pos;
    }

    public int endPos() {
      return endPos;
    }

    public String value() {
      return value;
    }

    public int ruleIndex() {
      return ruleIndex;
    }

    // The parser can ask a Step whether it is done already, which is
    // important when we backtrack. We know that a Step is done when
    // the `endPos` field has been set, but this gives us a nice
    // indirection.
    private boolean isDone() {
      return endPos != -1;
    }

    // A toString implementation for debugging is always a good thing
    // to have. This implementation returns a concise representation
    // of the Step.
    public String toString() {
      return rule
        + (ruleIndex != -1 ? ":"+ ruleIndex : "")
        + "@" + pos
        + (isDone() ? "-" + endPos : "")
        + (value != null ? "="+ value : "");
    }

    // As we have seen, Step objects are also used as keys inside a
    // Map. In our case, in the `rats` map. Since the grammar rule
    // object is the only stable field in a Step, we base our hash
    // code on that rule only.
    public int hashCode() {
      return rule.hashCode();
    }

    // The equals implementation then takes the start position in
    // consideration as well. The other fields are ignored, which is
    // perfect for the packrat implementation further on.
    public boolean equals(final Object obj) {
      if (obj instanceof Step) {
        final Step other = (Step)obj;
        return obj == other || (other.rule.equals(this.rule) && other.pos == this.pos);
      } else {
        return false;
      }
    }
  }

  // Now we know what to keep track of and what a Step in the `steps`
  // list represents. Creating a new parser State, requires the static
  // parts of the State: the grammar, the start keyword and the
  // (initial) input. Only those fields are set, and a new State has
  // been created.
  public State(final Map<Keyword, Object> grammar, final Keyword start, final String input) {
    this.grammar = grammar;
    this.start = start;
    this.input = input;
    steps.add(new Step(start, 0));
  }

  // While this parser uses some Clojure data types (Keyword and
  // Symbol), it can be used from Java as well. This constructor takes
  // Strings for the grammar and start keyword. Those Strings should
  // contain valid Clojure code that represents the grammar. After the
  // Strings are converted, they are passed to the other contstructor
  // we defined above.
  public State(final String grammar, final String start, final String input) {
    this((Map<Keyword, Object>)safeReadClj(grammar), (Keyword)safeReadClj(start), input);
  }

  // When a State has been created, we can start to parse! At its
  // core, parsing is nothing more that calling the `advance` method
  // (discussed later), until the `done` boolean is set to true. But
  // because of the incremental parsing, there is a bit more to it.
  // Follow allong.
  public void parse() {
    // First, we clear our packrat cache from the last time, in the
    // rare case it had not been cleared already.
    rats.clear();

    // Now we are going to fill our packrat cache with the Steps list
    // from a former parsing session, if available.
    //
    // We iterate through the steps, and if the step is done (i.e.
    // successfully parsed the last time) and the Step's grammar rule
    // is a Keyword (to limit the size of the cache a bit), we use the
    // step as the key for the cache. All the steps that follow that
    // step, that fall within the range of the step (pos and endPos
    // wise), are added as to the cache value.
    //
    // Having this cache set up is great for incremental parsing.
    for (int i = 0; i < steps.size(); i++) {
      final Step step = steps.get(i);
      if (step.rule instanceof Keyword && step.isDone()) {
        final List<Step> pack = new LinkedList<>();
        for (int j = i + 1; j < steps.size(); j++) {
          final Step other = steps.get(j);
          if (other.pos >= step.pos && other.endPos <= step.endPos) {
            pack.add(other);
          } else {
            break;
          }
        }
        if (!pack.isEmpty()) {
          rats.put(step, pack);
        }
      }
    }

    // Now that we have (possibly) used the steps from the former
    // parsing session, we can clear the steps. The first step to be
    // parsed, is added. It starts with the Keyword that was defined
    // as the starting rule, and at position 0.
    steps.clear();
    steps.add(new Step(start, 0));

    // We also clear out the errors from the former parsing session,
    // just like the lines position cache.
    errors.clear();
    errorsPos = -1;
    lines.clear();

    // We reset the done boolean to false, and we start to loop over
    // the `advance` method again, until it is set to true again.
    done = false;
    while (!isDone()) {
      advance();
    }

    // We are done parsing, successfully or not, so we clean our
    // packrat cache, as this can consume a lot of memory.
    rats.clear();
  }

  // Before we get to what `advance` is about, we show how an
  // incremental change affects the steps list.
  //
  // The user can specify a String that is inserted at a certain
  // position in the original input, overwriting a certain amount of
  // existing characters.
  //
  // This method makes sure that all the steps that are within the
  // range of the change are removed. Also, the positions of all the
  // steps that are after the range of the change, are shifted to
  // reflect the increase or decrease of the input lenght caused by
  // the change.
  //
  // As you have seen already, the steps that are left after this
  // method has run, are used at the beginning of the `parse` method,
  // to fill the packrat cache.
  public void increment(final String part, final int replaceAt, final int replaceLength) {
    // First, set the new input.
    input = input.substring(0, replaceAt) + part + input.substring(replaceAt + replaceLength);

    // Next, we calculate the amount the positions of the steps after
    // the change need to be shifted.
    final int shiftAmount = part.length() - replaceLength;

    // Now we can iterate over the current steps.
    final Iterator<Step> iterator = steps.iterator();
    while (iterator.hasNext()) {
      final Step step = iterator.next();

      // If the step is after the changed area, we keep the step and
      // we shift it, when necessary.
      if (step.pos > replaceAt + replaceLength) {
        if (shiftAmount != 0) {
          step.pos += shiftAmount;
          step.endPos += shiftAmount;
        }

      // Otherwise, if the step is not before the changed area,
      // we remove the step.
      } else if (!(step.endPos < replaceAt)) {
        iterator.remove();
      }
    }
  }

  // Now we get to one of the three methods that perform the parsing.
  // To advance the current state to the next state, we take a look at
  // the step that is at the end of the steps list. This is the step
  // we will try to process. How it is processed, depends on the type
  // of the grammar rule. Follow along:
  public void advance() {
    // We get the last step in the steps list.
    final Step lastStep = steps.get(steps.size() - 1);
    final Object rule = lastStep.rule;
    final int pos = lastStep.pos;

    // First, we check if this step is already known in the packrat
    // cache. If it is, we know exactly which steps will follow the
    // current last step, so we can add those already, potentially
    // skipping a lot of redundant processing.
    final List<Step> pack = rats.get(lastStep);
    if (pack != null) {
      steps.addAll(pack); // TODO optimize that last terminal is parsed again

    // Otherwise, if the rule is a List, we simply take the first item
    // of that list, and add that as a step.
    } else if (rule instanceof List) {
      steps.add(new Step(((List)rule).get(0), pos));

    // Otherwise, if the rule is a Keyword, we look up the
    // corresponding rule in the grammar and add that as a step.
    } else if (rule instanceof Keyword) {
      steps.add(new Step(grammar.get(rule), pos));

    // Now we get to the terminals. All of them try to match the
    // terminal on the input at the position of the step.
    //
    // If it is successful, we will backtrack over the steps list, in
    // order to find the next rule that needs to be parsed. This is
    // implemented in the `forward` method.
    //
    // If the match fails, we will also backtrack over the steps list,
    // but now to find the next sequence rule that offers an
    // alternative. This is implemented in the `backward` method.
    //
    // The first terminal parsing logic is for a regular expressions.
    } else if (rule instanceof Pattern) {
      final Matcher matcher = ((Pattern)rule).matcher(input); // optimize?
      if (matcher.find(pos) && matcher.start() == pos) {
        forward(matcher.group());
      } else {
        backward(String.format("Expected match of '%s'", rule));
      }

    // The next terminal parsing logic is for Strings.
    } else if (rule instanceof String) {
      final String stringRule = (String)rule;
      if (input.startsWith(stringRule, pos)) {
        forward(stringRule);
      } else {
        backward(String.format("Expected string '%s'", rule));
      }

    // The next terminal parsing logic is for characters.
    } else if (rule instanceof Character) {
      if (input.charAt(pos) == ((Character)rule).charValue()) {
        forward(rule.toString());
      } else {
        backward(String.format("Expected character '%s'", rule));
      }

    // And the last logic is for Symbol objects, which are considered
    // to be Strings.
    } else if (rule instanceof Symbol) {
      final String symbolRule = rule.toString();
      if (input.startsWith(symbolRule, pos)) {
        forward(symbolRule);
      } else {
        backward(String.format("Expected string '%s'", rule));
      }
    }
  }

  // So lets discuss what happens when we backtrack "forward", i.e. on
  // a successful match of a terminal rule.
  //
  // A successful match yields a value, which is given to this method.
  // The current step (the last step in the steps list), is given this
  // value.
  //
  // Next, we need to find the next rule to parse. Follow along below:
  private void forward(final String value) {
    // First we get the current (last) step.
    final int lastIndex = steps.size() - 1;
    final Step lastStep = steps.get(lastIndex);

    // Now we can calculate the new position of the step that will
    // follow the current last step.
    final int newPos = value != null ? lastStep.pos + value.length() : lastStep.pos;

    // And we assign the parsed value to the current step.
    lastStep.value = value;

    // We start iterating over the steps list, starting at the end. If
    // the rule of that step is a List, we check whether it contains a
    // next rule that needs to be parsed. That means that it has to
    // have an element at the Step's `ruleIndex`+1, and that element
    // should not be a slash (the alternatives divider).
    //
    // If the list rule fits this profile, the `ruleIndex` of the step
    // is increased by one, and the grammar rule at that index in the
    // list is added as the next step.
    //
    // While backtracking, we mark all the steps that we iterate over
    // as successful, by setting the end position.
    int i = lastIndex;
    for (; i >= 0; i--) {
      final Step step = steps.get(i);
      final Object rule = step.rule;
      if (rule instanceof List) {
        final List listRule = (List)rule;
        if (listRule.size() > step.ruleIndex+1 &&
            !listRule.get(step.ruleIndex+1).equals(SLASH)) {
          step.ruleIndex += 1;
          steps.add(new Step(listRule.get(step.ruleIndex), newPos));
          break;
        }
      }
      if (step.endPos == -1) {
        step.endPos = newPos - 1;
      }
    }

    // If we have checked all the steps, and none of the list rules
    // fits above criteria, we have walked the entire grammar.
    //
    // If the length of the input is equal to the new parse position
    // calculated earlier, we know we are done. Otherwise, we expected
    // EOF (end of file), and we will try to backtrack "backward".
    //
    // Otherwise, a Step has been added to the list, and the next
    // `advance` invocation will use this newly added step.
    if (i == -1) {
      if (newPos != input.length()) {
        backward("Expected EOF");
      } else {
        errors.clear();
        done = true;
      }
    }
  }

  // What then does backtracking "backward" mean? It is similar to
  // backtracking forward, in that we iterate over the steps list,
  // starting at the end, trying to find a sequence (a List) that
  // offers an alternative.
  private void backward(final String error) {
    // First we get the current (last) step.
    final int lastIndex = steps.size() - 1;
    final Step lastStep = steps.get(lastIndex);
    final int pos = lastStep.pos;

    // And we register the given error at the current position
    updateErrors(error, pos);

    // While backtracking, we will put all the successfully parsed
    // steps in the packrat cache. This structure keeps track of what
    // will be put into the cache.
    final LinkedList<Step> pack = new LinkedList<>();

    // We start iterating over the steps list, from the end, and try
    // to find a step that has a List as its grammar rule. If that
    // list has a slash, at its `ruleIndex` or higher, we set the rule
    // index to the index of that slash.
    //
    // All the steps we encounter during iterating are added to the
    // packrat cache value, if they were succesfully parsed already.
    int i = lastIndex;
    for (; i >= 0; i--) {
      final Step step = steps.get(i);
      final Object rule = step.rule;
      if (rule instanceof List && !step.isDone()) {
        final List listRule = (List)rule;
        final int ai = listRule.subList(step.ruleIndex, listRule.size()).indexOf(SLASH);
        if (ai >= 0) {
          step.ruleIndex += ai;
          break;
        }
      }

      if (step.isDone()) {
        pack.addFirst(step);
      }
    }

    // If we could not find a step with a sequence (List) rule that
    // had an alternative left, we are done parsing. This parsing
    // session will then be unsuccessful.
    //
    // Otherwise, we add the packrat cache value to the packrat cache,
    // and remove the steps after the one offering an alternative.
    if (i == -1) {
      done = true;
    } else {
      // Remove the steps we backtracked over.
      for (int j = lastIndex; j > i; j--) {
        steps.remove(j);
      }

      // Add the pack to the packrat cache, with each element being
      // the packrat key step.
      for (int r = 0; r < pack.size()-1; r++) {
        rats.put(pack.get(r), pack.subList(r+1, pack.size()));
      }

      // Now we try to move forward again, which will use the
      // alternative sequence of the step we just altered.
      forward(null);
    }
  }

  // Now you have seen everything there is concerning the core of the
  // parsing algorithm. Next we need some accessor methods to get to
  // the parsed data, in an immutable fashion.
  public boolean isDone() {
    return done;
  }

  public boolean hasErrors() {
    return !errors.isEmpty();
  }

  public List<Step> steps() {
    return Collections.unmodifiableList(steps);
  }

  public Set<String> errors() {
    return Collections.unmodifiableSet(errors);
  }

  public int errorsPos() {
    return errorsPos;
  }

  // The last thing we offer the clients of this parser, is to convert
  // a input position to its line and column number.
  public int[] posToLineColumn(final int pos) {
    // First we fill the cache, if not done so already. This fills the
    // TreeMap we talked about in the beginning.
    if (lines.isEmpty()) {
      fillLines();
    }

    // Now we get the position key that is exactly or directly below
    // the given position. This way we know that the column is the
    // given position minus the found position key (which is where a
    // line starts). The value of the key is the actual line that is
    // started at that key position.
    final Entry<Integer, Integer> floor = lines.floorEntry(pos);
    final int column = pos - floor.getKey() + 1;
    final int line = floor.getValue();

    return new int[] {line, column};
  }

  // Next up are some helper functions and definitions.
  private void fillLines() {
    int line = 1;
    char c1 = 0;
    char c2 = 0;
    for (int p = 0; p < input.length(); p++) {
      c1 = input.charAt(p);
      c2 = p + 1 < input.length() ? input.charAt(p+1) : 0;

      if (c1 == '\r' && c2 == '\n') {
        line++;
        p++;
        lines.put(p+1, line);
      } else if (c1 == '\r' || c1 == '\n') {
        line++;
        lines.put(p+1, line);
      }
    }
    lines.put(0, 1);
  }

  private void updateErrors(final String error, final int atPos) {
    if (atPos != errorsPos) {
      errors.clear();
    }
    errorsPos = atPos;
    errors.add(error);
  }

  private static Object safeReadClj(final String grammar) {
    return WITH_BINDINGS.invoke(BINDINGS, READ_STRING, grammar);
  }


  public String toString() {
    return "[State: steps="+ steps +" errors="+ errors +"@"+ errorsPos +"]";
  }

  public static final Symbol SLASH = Symbol.intern("/");
  private static final Var READ_EVAL = (Var)Clojure.var("clojure.core", "*read-eval*");
  private static final IFn READ_STRING = Clojure.var("clojure.core", "read-string");
  private static final IFn WITH_BINDINGS = Clojure.var("clojure.core", "with-bindings*");
  private static final PersistentHashMap BINDINGS = PersistentHashMap.create(READ_EVAL, false);
}
