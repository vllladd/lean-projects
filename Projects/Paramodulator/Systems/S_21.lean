import Projects.Paramodulator.Basic

namespace Paramodulator.S_21

open Node

instance : OfNat Node 2 := ⟨!!(0 1)⟩
theorem n2_def : (2 : Node) = !!(0 1) := rfl

inductive P : Node → Prop where
| r0 : P 1
| r1 {a} : P a → P 1
| r2 : P (!!(0 0)) → P 0
| r3 {a} : P a → P (!!(0 a))

-----

inductive P' : Node → Prop where
| r0 : P' 0
| r1 {a} : P' a → P' (!!(0 a))

-----

theorem p_eq_p' : P = P' := by
  ext a; constructor <;> intro h
  · induction h
    · exact P'.r1 P'.r0
    · exact P'.r1 P'.r0
    · exact P'.r0
    · nm x h ih; exact P'.r1 ih
  · induction h
    · exact P.r2 P.r0
    · nm x h ih; exact P.r3 ih