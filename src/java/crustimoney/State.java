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
// - literate programming?
// - expand error messages with what they did encounter?

/**
 * We want to parse some text input, using the datastructure-based
 * grammar directly. This needs to be done in such a way that we do
 * not build a (too) large stack of function/method calls. Thus, we
 * require a structure/object that keeps track of the state while
 * parsing, and some functions on this state to advance the state.
 *
 * The State class below is a structure that does just that. In this
 * case it is implemented in Java, to leverage mutability for speed,
 * but the model we will use works just as well in a functional,
 * immutable fashion.
 *
 * Let's define our class State.
 */
public class State {

  /**
   * We store our grammar in the State object, because we constantly
   * need it when parsing. A grammar is a mapping from keywords to
   * grammar rules. There are three type of rules.
   *
   * A rule can be a keyword, to refer to anothor grammar rule. A rule
   * can be a terminal, such as a String or a regular expression,
   * which are used to define the tokens.
   *
   * A rule can also be a List, having a sequence of grammar rules
   * that must be parsed succesively. Multiple sequences can be
   * defined inside this List, separated by a slash. If the first
   * sequence fails to parse, the second will be tried, and so on.
   */
  private final Map<Keyword, Object> grammar;

  /**
   * In order to know where our grammar starts, we keep track of
   * the keyword pointing to the first grammar rule.
   */
  private final Keyword start;

  /**
   * Of course, we also keep track of the input text. During parsing,
   * this object does not change. However, one of the features of this
   * parser is to incrementially change the input, therefore it is not
   * declared final.
   */
  private String input;

  /**
   * Now that we have defined our static values, we come to the heart
   * of the parsing algorithm: the steps. The state in which the
   * parser is at any point in time, is tracked inside this list. This
   * list grows and shrinks during parsing, and contains Step objects.
   *
   * Later we'll discuss what a Step contains and how this steps list
   * is used, but for now it it sufficient to know that a Step
   * contains a grammar rule and the position it is at regarding the
   * input text.
   */
  private final List<Step> steps = new ArrayList<>();

  /**
   * We also keep track of errors during parsing. The errors Set
   * contains the errors that were found at the errorsPos integer
   * below. Whenever an error is found, it is added to the Set.
   * However, the set is cleared whenever this error was found
   * on a different position than the errorsPos field.
   */
  private final Set<String> errors = new HashSet<>();
  private int errorsPos = -1;

  /**
   * We also want to know whether the algorithm finds that it is
   * done parsing, either successfully or not.
   */
  private boolean done = false;

  /**
   * To speed up the parsing process, this parser implements the
   * packrat pattern. The rats Map maps previously and successfully
   * parsed Step objects to the Step objects that followed that Step.
   * How this rats Map is used, is discussed further on in the
   * `advance` and `backward` methods.
   */
  private final Map<Step, List<Step>> rats = new HashMap<>();

  /**
   * As previously stated, the parser uses a position number to keep
   * track of where it is (or was) in the input. A more human friendly
   * representation is the combination of a line number and the column
   * number. The lines TreeMap below acts as a cache whenever this
   * representation is requested through the `posToLineColumn` method.
   *
   * The Map maps position numbers that are at a new line, to the line
   * number they start. For instance, position 0 always maps to line
   * 1.
   */
  private final TreeMap<Integer, Integer> lines = new TreeMap<>();


  /**
   * Now that we have our fields defined, we need to define what a
   * Step actually represents.
   */
  public static class Step {

    /**
     * The core of a Step is declaring that a grammar rule will or is
     * parsed at a certain position in the input. Again, this grammar
     * rule can be a Keyword, a terminal or a List. The position
     * number does not change during parsing. However, since
     * incremental parsing is supported, the pos field may change
     * between parses, therefore it is not declared final.
     */
    private final Object rule;
    private int pos;

    /**
     * Whenever the grammar rule object is a List, the Step also keeps
     * track of where the parsing is (or was) in that List. We will
     * see later how this works exactly.
     *
     * Because of this ruleIndex field, the List rule object is never
     * changed, which is important for the hashCode and equals
     * implementation of Step.
     */
    private int ruleIndex;

    /**
     * If a Step is parsed successfully, the end position is recorded
     * as well. Actually, the endPos is the next position of where the
     * next token is parsed.
     *
     * Recording this position has two benefits. Firstly, we need to
     * know whether a Step is successfully parsed already whenever we
     * backtrack (we will see this later on). Secondly, we need this
     * end position for the incremental parsing.
     */
    private int endPos = -1;

    /**
     * If the grammar rule of a Step is a terminal, and it is parsed
     * succesfully, its value is recorded inside the Step as well.
     */
    private String value = null;

    /**
     * Creating a new Step is private to the parser. It only requires
     * the core fields of a Step: the grammar rule and the position.
     */
    private Step(final Object rule, final int pos) {
      this.rule = rule;
      this.pos = pos;
      // If the rule is a List, we start recording the position in
      // this List.
      this.ruleIndex = rule instanceof List ? 0 : -1;
    }

    /**
     * The Step objects are also what is returned as the parsing
     * result, if successful. Therefore, we need some accessors that
     * allow read-only access to the Step contents.
     */
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

    /**
     * The parser can ask a Step whether it is done already, which is
     * important when we backtrack. We know that a Step is done when
     * the `endPos` field has been set, but this gives us a nice
     * indirection.
     */
    private boolean isDone() {
      return endPos != -1;
    }

    /**
     * A toString implementation for debugging is always a good thing
     * to have. This implementation returns a concise representation
     * of the Step.
     */
    public String toString() {
      return rule
        + (ruleIndex != -1 ? ":"+ ruleIndex : "")
        + "@" + pos
        + (isDone() ? "-" + endPos : "")
        + (value != null ? "="+ value : "");
    }

    /**
     * As we have seen, Step objects are also used as keys inside a
     * Map. In our case, in the `rats` map. Since the grammar rule
     * object is the only stable field in a Step, we base our hash
     * code on that rule only.
     */
    public int hashCode() {
      return rule.hashCode();
    }

    /**
     * The equals implementation then takes the start position in
     * consideration as well. The other fields are ignored, which is
     * perfect for the packrat implementation further on.
     */
    public boolean equals(final Object obj) {
      if (obj instanceof Step) {
        final Step other = (Step)obj;
        return obj == other || (other.rule.equals(this.rule) && other.pos == this.pos);
      } else {
        return false;
      }
    }
  }

  /**
   * Now we know what to keep track of and what a Step in the `steps`
   * list represents. Creating a new parser State, requires the static
   * parts of the State: the grammar, the start keyword and the
   * (initial) input. Only those fields are set, and a new State has
   * been created.
   */
  public State(final Map<Keyword, Object> grammar, final Keyword start, final String input) {
    this.grammar = grammar;
    this.start = start;
    this.input = input;
  }

  /**
   * While this parser uses some Clojure data types (Keyword and
   * Symbol), it can be used from Java as well. This constructor takes
   * Strings for the grammar and start keyword. Those Strings should
   * contain valid Clojure code that represents the grammar. After the
   * Strings are converted, they are passed to the other contstructor
   * we defined above.
   */
  public State(final String grammar, final String start, final String input) {
    this((Map<Keyword, Object>)safeReadClj(grammar), (Keyword)safeReadClj(start), input);
  }

  /**
   * When a State has been created, we can start to parse! At its
   * core, parsing is nothing more that calling the `advance` method
   * (discussed later), until the `done` boolean is set to true. But
   * because of the incremental parsing, there is a bit more to it.
   * Follow allong.
   */
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

  public void increment(final String part, final int replaceAt, final int replaceLength) {
    input = input.substring(0, replaceAt) + part + input.substring(replaceAt + replaceLength);

    final int shiftAmount = part.length() - replaceLength;
    final Iterator<Step> iterator = steps.iterator();
    while (iterator.hasNext()) {
      final Step step = iterator.next();
      if (step.pos > replaceAt + replaceLength) {
        if (shiftAmount != 0) {
          step.pos += shiftAmount;
          step.endPos += shiftAmount;
        }
      } else if (!(step.endPos <= replaceAt)) {
        iterator.remove();
      }
    }
  }

  public void advance() {
    final Step lastStep = steps.get(steps.size() - 1);
    final Object rule = lastStep.rule;
    final int pos = lastStep.pos;

    final List<Step> pack = rats.get(lastStep);
    if (pack != null) {
      steps.addAll(pack); // optimize that last terminal is parsed again
    } else if (rule instanceof List) {
      steps.add(new Step(((List)rule).get(0), pos));
    } else if (rule instanceof Keyword) {
      steps.add(new Step(grammar.get(rule), pos));
    } else if (rule instanceof Pattern) {
      final Matcher matcher = ((Pattern)rule).matcher(input); // optimize?
      if (matcher.find(pos) && matcher.start() == pos) {
        forward(matcher.group());
      } else {
        backward(String.format("Expected match of '%s'", rule));
      }
    } else if (rule instanceof String) {
      final String stringRule = (String)rule;
      if (input.startsWith(stringRule, pos)) {
        forward(stringRule);
      } else {
        backward(String.format("Expected string '%s'", rule));
      }
    } else if (rule instanceof Character) {
      if (input.charAt(pos) == ((Character)rule).charValue()) {
        forward(rule.toString());
      } else {
        backward(String.format("Expected character '%s'", rule));
      }
    } else if (rule instanceof Symbol) {
      final String symbolRule = rule.toString();
      if (input.startsWith(symbolRule, pos)) {
        forward(symbolRule);
      } else {
        backward(String.format("Expected string '%s'", rule));
      }
    }
  }

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

  public int[] posToLineColumn(final int pos) {
    if (lines.isEmpty()) {
      fillLines();
    }

    final Entry<Integer, Integer> floor = lines.floorEntry(pos);
    final int column = pos - floor.getKey() + 1;
    final int line = floor.getValue();

    return new int[] {line, column};
  }

  private void forward(final String value) {
    final int lastIndex = steps.size() - 1;
    final Step lastStep = steps.get(lastIndex);
    final int newPos = value != null ? lastStep.pos + value.length() : lastStep.pos;
    lastStep.value = value;

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
        step.endPos = newPos;
      }
    }

    if (i == -1) {
      if (newPos != input.length()) {
        backward("Expected EOF");
      } else {
        errors.clear();
        done = true;
      }
    }
  }

  private void backward(final String error) {
    final int lastIndex = steps.size() - 1;
    final Step lastStep = steps.get(lastIndex);
    final int pos = lastStep.pos;

    updateErrors(error, pos);

    final LinkedList<Step> pack = new LinkedList<>();

    int i = lastIndex;
    for (; i >= 0; i--) {
      final Step step = steps.get(i);
      final Object rule = step.rule;
      if (rule instanceof List && !step.isDone()) {
        final List listRule = (List)rule;
        final int ai = listRule.subList(step.ruleIndex, listRule.size()).indexOf(SLASH);
        if (ai >= 0) {
          step.ruleIndex += ai;
          forward(null);
          break;
        }
      }

      if (step.isDone()) {
        pack.addFirst(step);
      }
      steps.remove(i);
    }

    if (i == -1) {
      done = true;
    } else {
      for (i = 0; i < pack.size()-1; i++) {
        rats.put(pack.get(i), pack.subList(i+1, pack.size()));
      }
    }
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

  public String toString() {
    return "[State: steps="+ steps +" errors="+ errors +"@"+ errorsPos +"]";
  }

  public static final Symbol SLASH = Symbol.intern("/");
  private static final Var READ_EVAL = (Var)Clojure.var("clojure.core", "*read-eval*");
  private static final IFn READ_STRING = Clojure.var("clojure.core", "read-string");
  private static final IFn WITH_BINDINGS = Clojure.var("clojure.core", "with-bindings*");
  private static final PersistentHashMap BINDINGS = PersistentHashMap.create(READ_EVAL, false);
}
