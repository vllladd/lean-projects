import Projects.Sokoban.Card

namespace Sokoban

open Classical in noncomputable
def State.boxesReachable (s : State) : Set' PointZ :=
  s.points.filter # λ p => ∃ s', sys.Reachable s s' ∧ p ∈ s'.boxes

open Classical in noncomputable
def State.trBox (s : State) : PointZ :=
  s.boxesReachable.headMap! # λ p => p * ⟨-1, 1⟩

-----

open State

variable {s s₁ s₂ s₃ : State}

@[simp]
theorem boxes_subset_boxesReachable : s.boxes ⊆ s.boxesReachable := by
  intro p h; simp [boxesReachable]; use mem_points_of_mem_boxes h, s

@[simp]
theorem boxesReachable_eq_empty_iff [hs : sys.WF s] : s.boxesReachable = ∅ ↔ s.boxes = ∅ := by
  simp [boxesReachable]
  constructor
  · simp [Set'.ext_iff]
    intro h p
    by_cases h₁ : p ∈ s.points
    · apply h p h₁; rfl
    simp [boxes, h₁]
  intro h p h₁ s₁ h₂
  suffices h₃ : s₁.boxes = ∅; simp [h₃]
  rw [←Set'.size_eq_zero_iff] at h ⊢
  rwa [size_boxes_eq_of_reachable h₂]

theorem trBox_spec_aux [hs : sys.WF s] (h : s.boxes ≠ ∅) :
s.trBox ∈ s.boxesReachable ∧ ∀ p ∈ s.boxesReachable,
s.trBox.y ≤ p.y ∧ (s.trBox.y = p.y → p.x ≤ s.trBox.x) := by
  unfold trBox
  choose h₁ h₂ using s.boxesReachable.headMap!_spec (f := (· * ⟨-1, 1⟩)) (by simpa)
  use h₁
  clear h₁
  intro p hp
  specialize h₂ p hp
  clear hp
  generalize s.boxesReachable.headMap! (· * ⟨-1, 1⟩) = p₀ at h₂ ⊢
  rcases p₀, p with ⟨⟨x₀, y₀⟩, ⟨x, y⟩⟩
  simp at h₂ ⊢
  omega

@[simp]
theorem trBox_mem_iff [hs : sys.WF s] : s.trBox ∈ s.boxesReachable ↔ s.boxes ≠ ∅ := by
  simp [trBox]

@[simp]
theorem trBox_mem [hs : sys.WF s] (h : s.boxes ≠ ∅) : s.trBox ∈ s.boxesReachable := by
  simpa

theorem trBox_spec' [hs : sys.WF s] (h : s.boxes ≠ ∅) : ∀ p ∈ s.boxesReachable,
s.trBox.y ≤ p.y ∧ (s.trBox.y = p.y → p.x ≤ s.trBox.x) :=
  trBox_spec_aux h |>.2

theorem trBox_spec {p} [hs : sys.WF s] (h : s.boxes ≠ ∅) (hp : p ∈ s.boxesReachable) :
s.trBox.y ≤ p.y ∧ (s.trBox.y = p.y → p.x ≤ s.trBox.x) :=
  trBox_spec' h p hp