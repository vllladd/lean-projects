import AP.Util0

-- set_option trace.Meta.synthInstance true

instance {f : Prop → Prop} [h₁ : Decidable # f True]
[h₂ : Decidable # f False] : Decidable # ∀ P, f P := by
  have h₁ : (∀ P, f P) ↔ f True ∧ f False := by
    constructor <;> intro h₁
    · simp [h₁]
    intro Q
    by_cases h₂ : Q <;> simp [h₂]
    · exact h₁.1
    · exact h₁.2
  by_cases h₂ : f True ∧ f False
  · apply isTrue; rwa [h₁]
  · apply isFalse; rwa [h₁]

instance {α β : Type} {f g : α → β} [h : Decidable # ∀ x, f x = g x] :
Decidable # f = g := by
  cases h with
  | isTrue h => apply isTrue; ext x; rw [h]
  | isFalse h => apply isFalse; contrapose! h; simp [h]

example : (λ P Q => ¬(P → Q)) = (λ P Q => P ∧ ¬Q) := by
  decide