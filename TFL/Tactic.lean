import Mathlib.Tactic

syntax "quiet" tactic : tactic
macro_rules
| `(tactic| quiet $t:tactic ) => `(tactic| set_option linter.unusedSimpArgs false in $t:tactic )
