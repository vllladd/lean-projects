import Mathlib.Tactic

open Lean TSyntax.Compat

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

macro "τ" xs:explicitBinders ", " b:term : term =>
  expandExplicitBinders ``Classical.epsilon xs b