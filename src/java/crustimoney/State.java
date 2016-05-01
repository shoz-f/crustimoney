package crustimoney;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Keyword;
import clojure.lang.PersistentVector;
import clojure.lang.Var;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class State {

  private final IFn SLASH;

  private final Map<Keyword, Object> grammar;
  private final String input;
  private final List<Step> steps = new ArrayList<>();
  private final Set<String> errors = new HashSet<>();
  private int errorsPos = -1;
  private boolean done = false;

  public final Map<Step, List<Step>> rats = new HashMap<>();

  private static class Step {
    public final Object rule;
    public final int pos;
    public String value = null;
    public boolean success = false;
    public int ruleIndex;

    public Step(final Object rule, final int pos) {
      this.rule = rule;
      this.pos = pos;
      this.ruleIndex = rule instanceof List ? 0 : -1;
    }

    public String toString() {
      return rule
        + (ruleIndex != -1 ? ":"+ ruleIndex : "")
        + (success ? "!" : "")
        + "@" + pos
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
    this.input = input;
    steps.add(new Step(start, 0));

    SLASH = (IFn)((Var)Clojure.var("clojure.core", "/")).deref();
  }

  public static State parse(final Map<Keyword, Object> grammar, final Keyword start, final String input) {
    final State state = new State(grammar, start, input);
    while (!state.isDone()) {
      state.advance();
    }
    return state;
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
      step.success = true;
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
      if (rule instanceof List && !step.success) {
        final List listRule = (List)rule;
        final int ai = listRule.subList(step.ruleIndex, listRule.size()).indexOf(SLASH);
        if (ai >= 0) {
          step.ruleIndex += ai;
          forward(null);
          break;
        }
      }

      if (step.success) {
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
