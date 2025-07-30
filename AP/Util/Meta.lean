import Mathlib.Tactic

syntax:min term atomic(" #" ws) term:min : term

macro_rules
| `($f $args* # $a) => `($f $args* $a)
| `($f # $a) => `($f $a)

macro "nm " args:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| rename_i $args*)