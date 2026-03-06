import Projects.Fixpoint.KnasterTarski

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}

@[scoped grind =]
def CoindPred (F : (α → Prop) → α → Prop) : α → Prop :=
  supPostfix F

@[scoped grind =]
def CoindPredOrFn (F : (α → Prop) → α → Prop) (p : α → Prop) : α → Prop :=
  F # λ x => CoindPred F x ∨ p x

@[scoped grind =]
def CoindPredOr (F : (α → Prop) → α → Prop) : α → Prop :=
  CoindPred # CoindPredOrFn F

-----

variable {F : (α → Prop) → α → Prop}
variable {p : α → Prop} {x : α}

@[scoped grind ·]
theorem CoindPred.ctor (hf : Monotone F) (h : F (CoindPred F) x) : CoindPred F x := by
  revert x h; change F _ ≤ _; grind

@[scoped grind ·]
theorem CoindPred.cases' (hf : Monotone F) (h : CoindPred F x) : F (CoindPred F) x := by
  revert x h; change _ ≤ F _; grind

theorem CoindPred.cases {P : Prop} (hf : Monotone F)
(h₁ : CoindPred F x) (h₂ : F (CoindPred F) x → P) : P := by
  grind

theorem apply_coindPred_eq (hf : Monotone F) : F (CoindPred F) = CoindPred F := by
  grind

theorem CoindPred.coind' (hf : Monotone F)
(h₁ : p x) (h₂ : ∀ ⦃y⦄, p y → F p y) : CoindPred F x := by
  revert x h₁; change p ≤ _ at h₂ ⊢; grind

@[scoped grind →]
theorem monotone_coindPredOrFn (hf : Monotone F) : Monotone (CoindPredOrFn F) := by
  intro p₁ p₂ h₁; apply hf; intro x h₂; specialize h₁ x; tauto

@[scoped grind →]
theorem coindPred_le_coindPredOr (hf : Monotone F) : CoindPred F ≤ CoindPredOr F := by
  apply le_sSup; simp [PostFixpoint, CoindPredOrFn]; grind

@[scoped grind →]
theorem coindPredOr_eq_coindPred (hf : Monotone F) : CoindPredOr F = CoindPred F := by
  symm; apply le_antisymm; grind
  have h₁ : CoindPredOr F = CoindPredOrFn F (CoindPredOr F)
  · exact apply_coindPred_eq (by grind) |>.symm
  unfold CoindPredOrFn at h₁
  intro x h
  apply CoindPred.coind' hf h
  change CoindPredOr F ≤ _
  nth_rw 1 [h₁]
  apply hf
  intro y
  simp [or_imp]
  rw [h₁]
  nth_rw 1 [←apply_coindPred_eq hf]
  apply hf
  tauto

theorem CoindPred.coind (hf : Monotone F)
(h₁ : p x) (h₂ : ∀ ⦃y⦄, p y → F p y) : CoindPredOr F x := by
  rw [coindPredOr_eq_coindPred hf]; apply coind' (by grind) h₁ h₂