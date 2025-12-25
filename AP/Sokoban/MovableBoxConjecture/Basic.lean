import AP.Sokoban.MovableBoxConjecture.Defs

namespace Sokoban

open State

variable {s s₁ s₂ s₃ : State}

theorem State.AlwaysMovable.wf (h : s.AlwaysMovable) : sys.WF s := h.1

theorem boxes_ne_empty_of_alwaysMovable (h : s.AlwaysMovable) : s.boxes ≠ ∅ := by
  rcases h with ⟨h₁, h₂⟩
  specialize h₂ s (by rfl)
  choose s₁ h₂ h₃ using h₂
  contrapose! h₃
  symm; simp [h₃]
  rw [←Set'.size_eq_zero_iff] at h₃ ⊢; rw [←h₃]
  exact State.size_boxes_eq_of_reachable h₂

theorem alwaysMovable_iff_alt₁ : s.AlwaysMovable ↔ sys.WF s ∧ s.boxes ≠ ∅ ∧
∀ s₁, sys.Reachable s s₁ → ∃ s₂, sys.Reachable s₁ s₂ ∧ s₁.boxes ≠ s₂.boxes := by
  constructor
  · intro h
    use h.wf, boxes_ne_empty_of_alwaysMovable h, h.2
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, h₃⟩