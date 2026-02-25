import AP.Util.Finset

inductive Node where
| nil : Node
| pair : Node → Node → Node
deriving DecidableEq

namespace System

open Node

instance : Zero Node := ⟨nil⟩
theorem zero_def : (0 : Node) = nil := rfl

instance : One Node := ⟨pair 0 0⟩
theorem one_def : (1 : Node) = pair 0 0 := rfl

declare_syntax_cat node

syntax num : node
syntax ident : node
syntax "(" node node ")" : node
syntax "!!" node : term

macro_rules
  | `(!!($a:node $b:node)) => `(pair (!!$a) (!!$b))
  | `(!!$a:num) => `($a)
  | `(!!$a:ident) => `($a)

@[simp] theorem sizeOf_zero : sizeOf (0 : Node) = 1 := rfl
@[simp] theorem sizeOf_one : sizeOf (1 : Node) = 3 := rfl

-- #check 0 #exit

-----

instance : OfNat Node 2 := ⟨!!(0 1)⟩
theorem n2_def : (2 : Node) = !!(0 1) := rfl

instance : OfNat Node 3 := ⟨!!(1 1)⟩
theorem n3_def : (3 : Node) = !!(1 1) := rfl

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

inductive P : Node → Prop where
| r0 : P (!!(3 (2 ((1 ((2 0) 1)) (2 0)))))
| r1 {a} : P a → P (!!((a 0) a))
| r2 {a b} : P (!!(a (1 b))) → P b
| r3 : P 0 → P 2
| r4 {a} : P a →  P (!!(a 2))
| r5 {a b} : P (!!(((a (0 a)) a) b)) → P a → P 3 → P a → P a → P b
| r6 {a} : P a → P 2 → P (!!(0 a))

inductive P' : Node → Type where
| r0 : P' (!!(3 (2 ((1 ((2 0) 1)) (2 0)))))
| r1 {a} : P' a → P' (!!((a 0) a))
| r2 {a b} : P' (!!(a (1 b))) → P' b
| r3 : P' 0 → P' 2
| r4 {a} : P' a →  P' (!!(a 2))
| r5 {a b} : P' (!!(((a (0 a)) a) b)) → P' a → P' 3 → P' a → P' a → P' b
| r6 {a} : P' a → P' 2 → P' (!!(0 a))

theorem p_iff_nonempty_p' {a} : P a ↔ Nonempty (P' a) := by
  constructor <;> intro h
  ·
    induction h
    ·
      constructor
      exact P'.r0
    ·
      nm x h ih
      obtain ⟨ih⟩ := ih
      constructor
      exact P'.r1 ih
    ·
      nm x y h ih
      obtain ⟨ih⟩ := ih
      constructor
      exact P'.r2 ih
    ·
      nm h ih
      obtain ⟨ih⟩ := ih
      constructor
      exact P'.r3 ih
    ·
      nm x h ih
      obtain ⟨ih⟩ := ih
      constructor
      exact P'.r4 ih
    ·
      nm x y h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ H₁ H₂
      obtain ⟨h₆⟩ := h₆
      obtain ⟨h₇⟩ := h₇
      obtain ⟨h₈⟩ := h₈
      constructor
      apply P'.r5 <;> assumption
    ·
      nm x h₁ h₂ ih₁ ih₂
      obtain ⟨ih₁⟩ := ih₁
      obtain ⟨ih₂⟩ := ih₂
      constructor
      apply P'.r6 <;> assumption
  ·
    obtain ⟨h⟩ := h
    induction h
    ·
      exact P.r0
    ·
      apply P.r1; assumption
    ·
      apply P.r2 <;> assumption
    ·
      apply P.r3; assumption
    ·
      apply P.r4; assumption
    ·
      apply P.r5 <;> assumption
    ·
      apply P.r6 <;> assumption

theorem p_9 : P 9 := .r0

theorem not_p'_0_2_3_rl1 {a} (h : P' a) :
a ≠ 0 ∧ a ≠ 2 ∧ a ≠ 3 ∧ ∀ ⦃x y⦄, a ≠ (!!(x (1 y))) := by
  generalize hn : sizeOf h = n
  induction n using Nat.strong_induction_on generalizing a
  nm n ih
  subst hn
  
  cases h
  ·
    simp [one_def, n2_def, n3_def]
  ·
    nm x h
    simp [one_def, n2_def, n3_def]
    constructor
    ·
      rintro rfl
      simp
    ·
      rintro a b rfl rfl
      cases h
      ·
        nm h
        simp [one_def, n2_def, n3_def] at ih
        specialize ih (sizeOf h) (by omega) h rfl
        simp at ih
      ·
        nm x h
        simp [one_def, n2_def, n3_def] at h ih
        specialize ih (sizeOf h) (by omega) h rfl
        simp at ih
      ·
        nm h
        simp [one_def, n2_def, n3_def] at h ih
        cases h
        ·
          nm x h
          specialize ih (sizeOf h) _ h rfl
          on_goal 2 => simp [one_def] at ih
          clear ih
          suffices : sizeOf h < sizeOf h.r2.r4; omega
          simp
          omega
        ·
          sorry
        ·
          sorry
      ·
        sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry

theorem not_p_0_2_3_rl1 {a}
(h : P a) : a ≠ 0 ∧ a ≠ 2 ∧ a ≠ 3 ∧ ∀ x y, a ≠ (!!(x (1 y))) := by
  rw [p_iff_nonempty_p'] at h; obtain ⟨h⟩ := h; exact not_p'_0_2_3_rl1 h

theorem not_p_0 : ¬P 0 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_2 : ¬P 2 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_3 : ¬P 3 := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h

theorem not_p_rl_1 {a b} : ¬P (!!(a (1 b))) := by
  intro h; replace h := not_p_0_2_3_rl1 h; simp at h