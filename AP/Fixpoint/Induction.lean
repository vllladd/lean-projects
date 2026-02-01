import AP.Fixpoint.KnasterTarski

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}

@[scoped grind =]
def IndPred (F : (α → Prop) → α → Prop) : α → Prop :=
  infPrefix F

@[scoped grind =]
def IndPredAndFn (F : (α → Prop) → α → Prop) (p : α → Prop) : α → Prop :=
  F # λ x => IndPred F x ∧ p x

@[scoped grind =]
def IndPredAnd (F : (α → Prop) → α → Prop) : α → Prop :=
  IndPred # IndPredAndFn F

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
theorem monotone_indPredAndFn (hf : Monotone F) : Monotone (IndPredAndFn F) := by
  intro p₁ p₂ h₁; apply hf; intro x h₂; specialize h₁ x; tauto

@[scoped grind →]
theorem indPredAnd_le_indPred (hf : Monotone F) : IndPredAnd F ≤ IndPred F := by
  apply sInf_le; simp [PreFixpoint, IndPredAndFn]; grind

@[scoped grind →]
theorem indPredAnd_eq_indPred (hf : Monotone F) : IndPredAnd F = IndPred F := by
  apply le_antisymm; grind
  have h₁ : IndPredAnd F = IndPredAndFn F (IndPredAnd F)
  · exact apply_indPred_eq (by grind) |>.symm
  unfold IndPredAndFn at h₁
  intro x h
  apply h.ind' hf
  change _ ≤ IndPredAnd F
  nth_rw 2 [h₁]
  apply hf
  intro x
  simp [imp_and]
  revert x; change _ ≤ IndPred F
  grind

theorem IndPred.ind (hf : Monotone F) (h₁ : IndPred F x)
(h₂ : ∀ ⦃y⦄, IndPredAndFn F p y → p y) : p x := by
  rw [←indPredAnd_eq_indPred hf] at h₁; exact h₁.ind' (by grind) h₂

private theorem IndPred.casesAux₁ {P : Prop} (hf : Monotone F)
(h₁ : IndPred F x) (h₂ : F (IndPred F) x → P) : P := by
  apply h₁.ind hf; intros; apply h₂; rwa [apply_indPred_eq hf]

theorem eq_of_ctor_and_ind_eq_aux₁ {p q : α → Prop} (hf : Monotone F) (h₁ : ∀ ⦃x⦄, F q x → q x)
(h₂ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, p x → (∀ ⦃y⦄, F (λ x => p x ∧ p₁ x) y → p₁ y) → p₁ x)
(h : p x) : q x := by
  apply h₂ h; intro y hy; apply h₁; revert y hy; apply hf; tauto

theorem eq_of_ctor_and_ind_eq {p q : α → Prop}
(hf : Monotone F) (h₁ : ∀ ⦃x⦄, F p x → p x) (h₂ : ∀ ⦃x⦄, F q x → q x)
(h₃ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, p x → (∀ ⦃y⦄, F (λ x => p x ∧ p₁ x) y → p₁ y) → p₁ x)
(h₄ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, q x → (∀ ⦃y⦄, F (λ x => q x ∧ p₁ x) y → p₁ y) → p₁ x) : p = q := by
  ext; constructor
  · exact eq_of_ctor_and_ind_eq_aux₁ (p := p) (q := q) hf h₂ h₃
  · exact eq_of_ctor_and_ind_eq_aux₁ (p := q) (q := p) hf h₁ h₄

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

theorem even'_ind {p : ℕ → Prop} {n} (h₁ : Even' n)
(h₂ : p 0) (h₃ : ∀ n, Even' n → p n → p (n + 2)) : p n := by
  apply h₁.ind (by simp); simp [IndPredAndFn]; rw [←Even']; grind

theorem even'_eq_even : Even' = Even := by
  ext n; constructor <;> intro h; apply even'_ind h <;> grind
  rw [Nat.even_iff_exi] at h; obtain ⟨n, rfl⟩ := h; induction n <;> grind

end Aux₁