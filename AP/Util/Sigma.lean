import AP.Util.Logic

namespace Sigma

@[simp]
theorem fst_comp_mk_eq_id {α : Type*} {β : α → Type*} {f : (i : α) → β i} :
((λ (x : Σ i, β i) => x.fst) ∘ (λ i => ⟨i, f i⟩)) = (λ i => i) := by
  ext x; simp