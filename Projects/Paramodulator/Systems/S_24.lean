import Projects.Paramodulator.Basic

namespace Paramodulator.S_24

open Node

instance : OfNat Node 2 := ⟨!!(0 1)⟩
theorem n2_def : (2 : Node) = !!(0 1) := rfl

instance : OfNat Node 3 := ⟨!!(1 1)⟩
theorem n3_def : (3 : Node) = !!(1 1) := rfl

inductive P : Node → Prop where
| r0 : P (!!(3 (2 ((1 ((2 0) 1)) (2 0)))))
| r1 {a} : P a → P (!!((a 0) a))
| r2 {a b} : P (!!(a (1 b))) → P b
| r3 : P 0 → P 2
| r4 {a} : P a →  P (!!(a 2))
| r5 {a b} : P (!!(((a (0 a)) a) b)) → P a → P 3 → P a → P a → P b
| r6 {a} : P a → P 2 → P (!!(0 a))

-----

instance : OfNat Node 4 := ⟨!!(2 0)⟩
theorem n4_def : (4 : Node) = !!(2 0) := rfl

instance : OfNat Node 5 := ⟨!!(4 1)⟩
theorem n5_def : (5 : Node) = !!(4 1) := rfl

instance : OfNat Node 6 := ⟨!!(1 5)⟩
theorem n6_def : (6 : Node) = !!(1 5) := rfl

instance : OfNat Node 7 := ⟨!!(6 4)⟩
theorem n7_def : (7 : Node) = !!(6 4) := rfl

instance : OfNat Node 8 := ⟨!!(2 7)⟩
theorem n8_def : (8 : Node) = !!(2 7) := rfl

instance : OfNat Node 9 := ⟨!!(3 8)⟩
theorem n9_def : (9 : Node) = !!(3 8) := rfl

inductive P' : Node → Prop where
| r0 : P' 9
| r1 {a} : P' a → P' (!!((a 0) a))
| r2 {a} : P' a → P' (!!(a 2))

-----

inductive PD : Node → Type where
| r0 : PD (!!(3 (2 ((1 ((2 0) 1)) (2 0)))))
| r1 {a} : PD a → PD (!!((a 0) a))
| r2 {a b} : PD (!!(a (1 b))) → PD b
| r3 : PD 0 → PD 2
| r4 {a} : PD a →  PD (!!(a 2))
| r5 {a b} : PD (!!(((a (0 a)) a) b)) → PD a → PD 3 → PD a → PD a → PD b
| r6 {a} : PD a → PD 2 → PD (!!(0 a))

theorem p_iff_nonempty_pd {a} : P a ↔ Nonempty (PD a) := by
  constructor <;> intro h
  · induction h
    · constructor; exact PD.r0
    · nm x h ih; obtain ⟨ih⟩ := ih; constructor; exact PD.r1 ih
    · nm x y h ih; obtain ⟨ih⟩ := ih; constructor; exact PD.r2 ih
    · nm h ih; obtain ⟨ih⟩ := ih; constructor; exact PD.r3 ih
    · nm x h ih; obtain ⟨ih⟩ := ih; constructor; exact PD.r4 ih
    · nm x y h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ H₁ H₂; obtain ⟨h₆⟩ := h₆; obtain ⟨h₇⟩ := h₇
      obtain ⟨h₈⟩ := h₈; constructor; apply PD.r5 <;> assumption
    · nm x h₁ h₂ ih₁ ih₂; obtain ⟨ih₁⟩ := ih₁; obtain ⟨ih₂⟩ := ih₂
      constructor; apply PD.r6 <;> assumption
  · obtain ⟨h⟩ := h; induction h
    · exact P.r0
    · apply P.r1; assumption
    · apply P.r2 <;> assumption
    · apply P.r3; assumption
    · apply P.r4; assumption
    · apply P.r5 <;> assumption
    · apply P.r6 <;> assumption

theorem p_9 : P 9 := .r0

theorem not_pd_0_2_3_rl1 {a} (h : PD a) :
a ≠ 0 ∧ a ≠ 2 ∧ a ≠ 3 ∧ ∀ ⦃x y⦄, a ≠ (!!(x (1 y))) := by
  generalize hn : sizeOf h = n
  induction n using Nat.strong_induction_on generalizing a
  nm n ih; subst hn; split_ands; on_goal 4 => intro x y
  · rintro rfl; cases h <;> grind
  · rintro rfl; cases h <;> try grind;; nm h₁ h₂
    specialize @ih (sizeOf h₁) # by unfold PD._sizeOf_inst PD._sizeOf_1; simp;; grind
  · rintro rfl; cases h <;> try grind
  · rintro rfl; cases h <;> try grind;; nm h
    cases h <;> (try grind) <;> nm h
    · specialize @ih (sizeOf h) # by unfold PD._sizeOf_inst PD._sizeOf_1; simp; omega;; grind
    cases h <;> try grind;; nm h₁ h₂
    specialize @ih (sizeOf h₁) # by unfold PD._sizeOf_inst PD._sizeOf_1; simp; omega;; grind

theorem not_p_0_2_3_rl1 {a}
(h : P a) : a ≠ 0 ∧ a ≠ 2 ∧ a ≠ 3 ∧ ∀ x y, a ≠ (!!(x (1 y))) := by
  rw [p_iff_nonempty_pd] at h; obtain ⟨h⟩ := h; exact not_pd_0_2_3_rl1 h

theorem not_p_0 : ¬P 0 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_2 : ¬P 2 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_3 : ¬P 3 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_rl1 {a b} : ¬P (!!(a (1 b))) := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem p_eq_p' : P = P' := by
  ext a; constructor <;> intro h
  · induction h
    · exact P'.r0
    · nm x h ih; exact P'.r1 ih
    · nm h₁ h₂ h₃ ih; cases not_p_rl1 h₃
    · nm h ih; cases not_p_0 h
    · nm x h ih; exact P'.r2 ih
    · nm x y h₁ h₂ h₃ h₄ h₅ ih₁ ih₂ ih₃ ih₄ ih₅; cases not_p_3 h₃
    · nm x h₁ h₂ ih₁ ih₂; cases not_p_2 h₂
  · induction h
    · exact P.r0
    · nm x h ih; exact P.r1 ih
    · nm x h ih; exact P.r4 ih