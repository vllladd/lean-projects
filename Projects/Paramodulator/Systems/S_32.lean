import Projects.Paramodulator.Basic

namespace Paramodulator.S_32

open Node

instance : OfNat Node 2 := ⟨!!(1 0)⟩
theorem n2_def : (2 : Node) = !!(1 0) := rfl

instance : OfNat Node 3 := ⟨!!(0 1)⟩
theorem n3_def : (3 : Node) = !!(0 1) := rfl

inductive P : Node → Prop where
| r0 : P 1
| r1 {a} : P (!!(a 0)) → P (!!(a (0 ((((a ((0 a) (0 a))) a) (0 a)) 1))))
| r2 : P 0 → P 1
| r3 {a} : P (!!(0 a)) → P (!!(0 a)) → P 1 → P a

-----

instance : OfNat Node 4 := ⟨!!(1 1)⟩
theorem n4_def : (4 : Node) = !!(1 1) := rfl

instance : OfNat Node 5 := ⟨!!(0 4)⟩
theorem n5_def : (5 : Node) = !!(0 4) := rfl

instance : OfNat Node 6 := ⟨!!(5 0)⟩
theorem n6_def : (6 : Node) = !!(5 0) := rfl

instance : OfNat Node 7 := ⟨!!(6 1)⟩
theorem n7_def : (7 : Node) = !!(6 1) := rfl

instance : OfNat Node 8 := ⟨!!(7 1)⟩
theorem n8_def : (8 : Node) = !!(7 1) := rfl

instance : OfNat Node 9 := ⟨!!(0 8)⟩
theorem n9_def : (9 : Node) = !!(0 8) := rfl

instance : OfNat Node 10 := ⟨!!(0 9)⟩
theorem n10_def : (10 : Node) = !!(0 9) := rfl

-----

theorem p_eq : P = (· ∈ ({0, 1, 8, 9, 10} : Set _)) := by
  ext a; simp; constructor <;> intro h
  · induction h <;> try simp [one_def]
    · nm x h ih; simp [one_def] at ih; rcases ih with rfl | ih | ih | ih
      · right; right; rfl
      · simp [n8_def] at ih
      · simp [n9_def] at ih
      · simp [n10_def] at ih
    · nm x h₁ h₂ h₃ ih₁ ih₂ ih₃; simp [one_def] at ih₁
      rcases ih₁ with rfl | ih | ih | ih
      · simp
      · simp [n8_def] at ih
      · simp [n9_def] at ih; simp [ih]
      · simp [n10_def] at ih; simp [ih]
  · have h₀ := P.r0; have h₁ := P.r3 h₀ h₀ h₀; have h₂ : P 10 := P.r1 h₀
    have h₃ : P 9 := P.r3 h₂ h₂ h₀; have h₄ : P 8 := P.r3 h₃ h₃ h₀; grind