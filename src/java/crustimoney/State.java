package crustimoney;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Keyword;
import clojure.lang.PersistentVector;
import clojure.lang.Var;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

// TODO
// - pos to line and column (automatic for error set)
// - result export(s) and transformations
// - step-by-step parsing / debugging (a better API that is)?
// - rule rewriting with ?, + and *
// - left recursion detection
// - packrat configuration (configure minimal pack length, limit rats by max number per rule, etc)
// - have it use EDN (as a dep, for both Java and Clojure API)
// - check grammar for errors
// - support cuts?
// - add interrupt? (or have API clients use advance themselves for their own control)

public class State {

  private final IFn SLASH;

  private final Map<Keyword, Object> grammar;
  private final Keyword start;
  private String input;
  private final List<Step> steps = new ArrayList<>();
  private final Set<String> errors = new HashSet<>();
  private int errorsPos = -1;
  private boolean done = false;

  public final Map<Step, List<Step>> rats = new HashMap<>();

  private static class Step {
    public final Object rule;
    public int pos;
    public String value = null;
    public int ruleIndex;
    public int endPos = -1;

    public Step(final Object rule, final int pos) {
      this.rule = rule;
      this.pos = pos;
      this.ruleIndex = rule instanceof List ? 0 : -1;
    }

    public boolean isDone() {
      return endPos != -1;
    }

    public String toString() {
      return rule
        + (ruleIndex != -1 ? ":"+ ruleIndex : "")
        + "@" + pos
        + (isDone() ? "-" + endPos : "")
        + (value != null ? "="+ value : "");
    }

    public int hashCode() {
      return rule.hashCode();
    }

    public boolean equals(final Object obj) {
      if (obj instanceof Step) {
        final Step other = (Step)obj;
        return other.rule.equals(this.rule) && other.pos == this.pos;
      } else {
        return false;
      }
    }
  }

  public State(final Map<Keyword, Object> grammar, final Keyword start, final String input) {
    this.grammar = grammar;
    this.start = start;
    this.input = input;
    steps.add(new Step(start, 0));

    SLASH = (IFn)((Var)Clojure.var("clojure.core", "/")).deref();
  }

  public static State parse(final Map<Keyword, Object> grammar, final Keyword start, final String input) {
    final State state = new State(grammar, start, input);
    while (!state.isDone()) {
      state.advance();
    }
    //rats.clear();
    return state;
  }

  public void reparse(final String part, final int replaceAt, final int replaceLength) {
    input = input.substring(0, replaceAt) + part + input.substring(replaceAt + replaceLength);

    rats.clear();

    for (int i = 0; i < steps.size(); i++) {
      final Step rat = steps.get(i);
      if (rat.pos > replaceAt + replaceLength || rat.endPos <= replaceAt) {
        if (rat.rule instanceof Keyword) {
          final List<Step> pack = new LinkedList<>();
          for (int j = i + 1; j < steps.size(); j++) {
            final Step other = steps.get(j);
            if (other.pos >= rat.pos && other.endPos <= rat.endPos) {
              pack.add(other);
            } else {
              break;
            }
          }
          if (!pack.isEmpty()) {
            rats.put(rat, pack);
          }
        }
      }
    }

    final int shiftAmount = part.length() - replaceLength;
    if (shiftAmount != 0) {
      final Set<Step> shift = new HashSet<>();
      for (final Entry<Step, List<Step>> entry : rats.entrySet()) {
        final Step rat = entry.getKey();
        final List<Step> pack = entry.getValue();
        if (rat.pos > replaceAt + replaceLength) {
          shift.add(rat);
          shift.addAll(pack);
        }
      }
      for (final Step step : shift) {
        step.pos += shiftAmount;
        step.endPos += shiftAmount;
      }
    }

    steps.clear();
    steps.add(new Step(start, 0));
    errors.clear();
    errorsPos = -1;
    done = false;
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
    }
  }

  public boolean isDone() {
    return done;
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

  public String toString() {
    return "[State: steps="+ steps +" errors="+ errors +"@"+ errorsPos +"]";
  }
}
