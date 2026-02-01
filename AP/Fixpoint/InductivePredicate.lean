import AP.Fixpoint.KnasterTarski

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}

@[scoped grind =]
def IndPred (F : (α → Prop) → α → Prop) : α → Prop :=
  infPrefix F

@[simp, scoped grind =]
def IndPredAnd (F : (α → Prop) → α → Prop) (p : α → Prop) : α → Prop :=
  F (λ x => IndPred F x ∧ p x)

-- #check 0 #exit

-----

variable {F : (α → Prop) → α → Prop}
variable {p : α → Prop} {x : α}

@[scoped grind ·]
theorem IndPred.ctor (hf : Monotone F) (h : F (IndPred F) x) : IndPred F x := by
  revert x h; change F _ ≤ _; grind

@[scoped grind ·]
theorem IndPred.cases' (hf : Monotone F) (h : IndPred F x) : F (IndPred F) x := by
  revert x h; change _ ≤ F _; grind

theorem IndPred.cases {P : Prop} (hf : Monotone F)
(h₁ : IndPred F x) (h₂ : F (IndPred F) x → P) : P := by
  grind

theorem apply_indPred_eq (hf : Monotone F) : F (IndPred F) = IndPred F := by
  grind

theorem IndPred.ind' (hf : Monotone F)
(h₁ : IndPred F x) (h₂ : ∀ ⦃y⦄, F p y → p y) : p x := by
  revert x h₁; change _ ≤ p at h₂ ⊢; grind

@[scoped grind →]
theorem monotone_and (hf : Monotone F) : Monotone (IndPredAnd F) := by
  intro p₁ p₂ h₁; apply hf; intro x h₂; specialize h₁ x; tauto

@[simp]
theorem infPrefix_pi_const {P : Prop} :
infPrefix (λ (_ : α → Prop) (_ : α) => P) = λ _ => P := by
  ext x; induction P using prop_ind <;> simp [infPrefix, PreFixpoint]
  · intro p h; specialize h x; simp at h; exact h
  · use ⊥; simp; rfl

-- end Fixpoint

-- namespace Fixpoint

-- variable {α : Type*}

-- #check 0 #exit

-- example : ¬∀ {α : Type} {F : (α → Prop) → α → Prop}
-- (hf : Monotone F), infPrefix (IndPredAnd F) = IndPred F := by
--   push_neg
--   use ℕ
--   use λ _ _ => False
--   simp [Monotone]
--   apply ne_of_congr (· 0)
--   simp
--   push_neg
--   right
--   split_ands
--   ·
--     unfold IndPredAnd
--     simp
--   simp [IndPred]

-- #check 0 #exit

-- theorem IndPred.ind (hf : Monotone F) (h₁ : IndPred F x)
-- (h₂ : ∀ ⦃y⦄, IndPred F y → F p y → p y) : p x := by

-- #check 0 #exit

-----

namespace Aux₁

@[simp, scoped grind =]
def EvenAux (p : ℕ → Prop) (n : ℕ) : Prop :=
  n = 0 ∨ ∃ k, p k ∧ k + 2 = n

@[scoped grind =]
def Even' : ℕ → Prop :=
  IndPred EvenAux

@[simp, scoped grind ·]
theorem monotone_evenAux : Monotone EvenAux := by
  intro p₁ p₂ h n; simp; tauto

@[simp, scoped grind ·]
theorem even'_zero : Even' 0 := by
  apply IndPred.ctor <;> simp

@[scoped grind →]
theorem even'_add_two {n} (h : Even' n) : Even' (n + 2) := by
  apply IndPred.ctor <;> simp; exact h

@[scoped grind →]
theorem even'_cases {n} (h : Even' n) : n = 0 ∨ ∃ k, Even' k ∧ k + 2 = n :=
  h.cases' # by simp

-- #check 0 #exit

end Aux₁