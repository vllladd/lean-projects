import Projects.Paramodulator.Basic

namespace Paramodulator.S_61

open Node

instance : OfNat Node 2 := ⟨!!(1 0)⟩
theorem n2_def : (2 : Node) = !!(1 0) := rfl

instance : OfNat Node 3 := ⟨!!(2 1)⟩
theorem n3_def : (3 : Node) = !!(2 1) := rfl

inductive P : Node → Prop where
| r0 : P (!!(2 1))
| r1 {a} : P a → P (!!((a 0) 3))
| r2 {a b} : P (!!(1 a)) → P b → P a

-----

inductive P' : Node → Prop where
| r0 : P' 3
| r1 {a} : P' a → P' (!!((a 0) 3))

-----

theorem p_eq_p' : P = P' := by
  ext a; constructor <;> intro h
  · induction h
    · exact P'.r0
    · nm x h ih; exact P'.r1 ih
    · nm x y h₁ h₂ ih₁ ih₂; cases ih₁; nm h₃; cases h₃
  · induction h
    · exact P.r0
    · nm x h ih; exact P.r1 ih