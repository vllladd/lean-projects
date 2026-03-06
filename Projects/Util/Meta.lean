import Mathlib.Tactic

syntax:min term atomic(" #" ws) term:min : term
syntax:min term atomic(" ##" ws) term:min : term

macro_rules
  | `($f $args* # $a) =>
    if a.raw.isMissing then
      `($f $args*)
    else
      `($f $args* $a)
  | `($f # $a) =>
    if a.raw.isMissing then
      `($f)
    else
      `($f $a)

macro_rules
  | `($f $args* ## $a) =>
    if a.raw.isMissing then
      `($f $args*)
    else
      `($f $args* $a)
  | `($f ## $a) =>
    if a.raw.isMissing then
      `($f)
    else
      `($f $a)

macro "nm " args:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| rename_i $args*)

-- axiom aesop' {P : Prop} : P
-- 
-- macro "aesop'" : tactic => `(tactic| exact aesop')