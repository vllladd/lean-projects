import AP.Fixpoint.KnasterTarski

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}

@[scoped grind =]
def CoindPred (F : (α → Prop) → α → Prop) : α → Prop :=
  supPostfix F

@[scoped grind =]
def CoindPredAndFn (F : (α → Prop) → α → Prop) (p : α → Prop) : α → Prop :=
  F # λ x => CoindPred F x ∧ p x

@[scoped grind =]
def CoindPredAnd (F : (α → Prop) → α → Prop) : α → Prop :=
  CoindPred # CoindPredAndFn F

-----

variable {F : (α → Prop) → α → Prop}
variable {p : α → Prop} {x : α}

@[scoped grind ·]
theorem CoindPred.ctor (hf : Monotone F) (h : CoindPred F x) : F (CoindPred F) x := by
  revert x h; change _ ≤ F _; grind

@[scoped grind ·]
theorem CoindPred.cases' (hf : Monotone F) (h : F (CoindPred F) x) : CoindPred F x := by
  revert x h; change F _ ≤ _; grind

theorem CoindPred.cases {P : Prop} (hf : Monotone F)
(h₁ : F (CoindPred F) x) (h₂ : CoindPred F x → P) : P := by
  grind

theorem apply_coindPred_eq (hf : Monotone F) : F (CoindPred F) = CoindPred F := by
  grind

theorem CoindPred.coind' (hf : Monotone F)
(h₁ : p x) (h₂ : ∀ ⦃y⦄, p y → F p y) : CoindPred F x := by
  revert x h₁; change p ≤ _ at h₂ ⊢; grind

@[scoped grind →]
theorem monotone_coindPredAndFn (hf : Monotone F) : Monotone (CoindPredAndFn F) := by
  intro p₁ p₂ h₁; apply hf; intro x h₂; specialize h₁ x; tauto

@[scoped grind →]
theorem coindPred_le_coindPredAnd (hf : Monotone F) : CoindPred F ≤ CoindPredAnd F := by
  apply le_sSup; simp [PostFixpoint, CoindPredAndFn]; grind

@[scoped grind →]
theorem coindPredAnd_eq_coindPred (hf : Monotone F) : CoindPredAnd F = CoindPred F := by
  symm; apply le_antisymm; grind
  have h₁ : CoindPredAnd F = CoindPredAndFn F (CoindPredAnd F)
  · exact apply_coindPred_eq (by grind) |>.symm
  unfold CoindPredAndFn at h₁
  intro x h
  apply CoindPred.coind' hf h
  change CoindPredAnd F ≤ _
  nth_rw 1 [h₁]
  apply hf; intro; simp

theorem CoindPred.coind (hf : Monotone F) (h₁ : p x)
(h₂ : ∀ ⦃y⦄, p y → CoindPredAndFn F p y) : CoindPred F x := by
  rw [←coindPredAnd_eq_coindPred hf]; apply coind' (by grind) h₁ h₂

private theorem CoindPred.casesAux₁ {P : Prop} (hf : Monotone F)
(h₁ : F (CoindPred F) x) (h₂ : CoindPred F x → P) : P := by
  apply h₂; apply coind hf h₁; rw [apply_coindPred_eq hf]
  intro y; simp [CoindPredAndFn]
  nth_rw 1 [←apply_coindPred_eq hf]
  apply hf; simp

-- theorem eq_of_ctor_and_coind_eq_aux₁ {p q : α → Prop} (hf : Monotone F)
-- (h₁ : ∀ ⦃x⦄, p x → F q x)
-- (h₂ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, p₁ x → (∀ ⦃y⦄, p₁ y → F (λ x => q x ∧ p₁ x) y) → q x)
-- (h : p x) : q x := by
--   -- apply h₂ h; intro y hy; apply h₁; revert y hy; apply hf; tauto
--   
--   -- specialize h₁ h
--   
--   apply h₂ h
--   intro y hy
--   specialize h₁ hy
--   clear hy
--   revert y h₁
--   apply hf
-- 
-- #check 0 #exit
-- 
-- theorem eq_of_ctor_and_ind_eq {p q : α → Prop}
-- (hf : Monotone F) (h₁ : ∀ ⦃x⦄, F p x → p x) (h₂ : ∀ ⦃x⦄, F q x → q x)
-- (h₃ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, p x → (∀ ⦃y⦄, F (λ x => p x ∧ p₁ x) y → p₁ y) → p₁ x)
-- (h₄ : ∀ ⦃p₁ : α → Prop⦄ ⦃x⦄, q x → (∀ ⦃y⦄, F (λ x => q x ∧ p₁ x) y → p₁ y) → p₁ x) : p = q := by
--   ext; constructor
--   · exact eq_of_ctor_and_ind_eq_aux₁ (p := p) (q := q) hf h₂ h₃
--   · exact eq_of_ctor_and_ind_eq_aux₁ (p := q) (q := p) hf h₁ h₄
-- 
-- -----
-- 
-- namespace Aux₁
-- 
-- @[simp, scoped grind =]
-- def EvenAux (p : ℕ → Prop) (n : ℕ) : Prop :=
--   n = 0 ∨ ∃ k, p k ∧ k + 2 = n
-- 
-- @[scoped grind =]
-- def Even' : ℕ → Prop :=
--   CoindPred EvenAux
-- 
-- @[simp, scoped grind ·]
-- theorem monotone_evenAux : Monotone EvenAux := by
--   intro p₁ p₂ h n; simp; tauto
-- 
-- @[simp, scoped grind ·]
-- theorem even'_zero : Even' 0 := by
--   apply CoindPred.ctor <;> simp
-- 
-- @[scoped grind →]
-- theorem even'_add_two {n} (h : Even' n) : Even' (n + 2) := by
--   apply CoindPred.ctor <;> simp; exact h
-- 
-- @[scoped grind →]
-- theorem even'_cases {n} (h : Even' n) : n = 0 ∨ ∃ k, Even' k ∧ k + 2 = n :=
--   h.cases' # by simp
-- 
-- theorem even'_ind {p : ℕ → Prop} {n} (h₁ : Even' n)
-- (h₂ : p 0) (h₃ : ∀ n, Even' n → p n → p (n + 2)) : p n := by
--   apply h₁.ind (by simp); simp [CoindPredAndFn]; rw [←Even']; grind
-- 
-- theorem even'_eq_even : Even' = Even := by
--   ext n; constructor <;> intro h; apply even'_ind h <;> grind
--   rw [Nat.even_iff_exi] at h; obtain ⟨n, rfl⟩ := h; induction n <;> grind
-- 
-- end Aux₁