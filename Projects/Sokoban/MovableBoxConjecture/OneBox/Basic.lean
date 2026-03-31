import Projects.Sokoban.MovableBoxConjecture.OneBox.Defs

namespace Sokoban.MovableBoxConjecture1

open State MovableBoxConjecture

variable {s s₁ s₂ s₃ : State}
variable [H : MovableBoxConjecture1]
include H

theorem exi_stateCnd₀ : ∃ n s, stateCnd₀ n s := by
  choose s H using H.1; exact ⟨_, s, H, rfl⟩

theorem size₀_spec' : (∃ s, stateCnd₀ size₀ s) ∧
(∀ n, (∃ s, stateCnd₀ n s) → size₀ ≤ n) :=
  Nat.find!_spec' exi_stateCnd₀

theorem size₀_spec : ∃ s, stateCnd₀ size₀ s :=
  size₀_spec'.1

theorem size₀_le' {n} (h : ∃ s, stateCnd₀ n s) : size₀ ≤ n :=
  size₀_spec'|>.2 n h

theorem size₀_le {n s} (h : stateCnd₀ n s) : size₀ ≤ n :=
  size₀_le' ⟨_, h⟩

@[simp]
theorem state₀_spec : stateCnd₀ size₀ state₀ :=
  Classical.epsilon_spec size₀_spec

@[simp, instance]
theorem alwaysMovable1_state₀ : AlwaysMovable1 state₀ :=
  state₀_spec.1

omit H in @[simp]
theorem stateCnd₀_self : stateCnd₀ s.boxesReachable.size s ↔ AlwaysMovable1 s := by
  simp [stateCnd₀]

theorem state₀_size_boxesReachable_le (h : stateCnd₀ size₀ s) :
s.boxesReachable.size ≤ state₀.boxesReachable.size := by
  choose n h₁ using id h; rw [h₁]; apply size₀_le'; use state₀; simp

omit H in @[simp]
theorem size_boxes_of_alwaysMovable1 [hs : AlwaysMovable1 s] : s.boxes.size = 1 :=
  hs.2

@[simp]
theorem boxes_state₀_ne_empty : state₀.boxes ≠ ∅ := by
  rw [ne_eq, ←Set'.size_eq_zero_iff, size_boxes_of_alwaysMovable1]; simp

@[simp]
theorem trBox₁_mem : trBox₁ ∈ state₀.boxesReachable := by
  simp [trBox₁]

theorem trBox₁_spec {p} (h : p ∈ state₀.boxesReachable) :
trBox₁.y ≤ p.y ∧ (trBox₁.y = p.y → p.x ≤ trBox₁.x) :=
  trBox_spec (by simp) h

theorem state₁_spec : sys.Reachable state₀ state₁ ∧ state₁.boxes = .singleton trBox₁ := by
  apply Classical.epsilon_spec (p := λ s =>
    sys.Reachable state₀ s ∧ s.boxes = Set'.singleton trBox₁)
  have h₁ := trBox₁_mem
  rw [boxesReachable] at h₁
  simp at h₁
  obtain ⟨-, s₁, h₁, h₂⟩ := h₁
  use s₁, h₁
  have h₃ : s₁.boxes.size = 1
  · rw [size_boxes_eq_of_reachable h₁]; simp
  rw [Set'.size_eq_one_iff] at h₃
  obtain ⟨p, h₃, h₄⟩ := h₃
  ext p₁
  simp
  grind

@[simp]
theorem reachable_state₀_state₁ : sys.Reachable state₀ state₁ :=
  state₁_spec.1

@[simp]
theorem boxes_state₁ : state₁.boxes = .singleton trBox₁ :=
  state₁_spec.2

omit H in
theorem alwaysMovable1_of_reachable [hs : AlwaysMovable1 s]
(h : sys.Reachable s s₁) : AlwaysMovable1 s₁ := by
  cases hs; nm hs h₁; have hs₁ := alwaysMovable_of_reachable h
  constructor; rwa [size_boxes_eq_of_reachable h]

@[simp, instance]
theorem alwaysMovable1_state₁ : AlwaysMovable1 state₁ :=
  alwaysMovable1_of_reachable (s := state₀) # by simp

theorem state₂_spec : sys.Reachable state₁ state₂ ∧ state₂.boxes ≠ .singleton trBox₁ := by
  apply Classical.epsilon_spec (p := λ s =>
    sys.Reachable state₁ s ∧ s.boxes ≠ Set'.singleton trBox₁)
  have h₁ := alwaysMovable1_state₁.1.2
  specialize h₁ _ (by rfl)
  choose s₁ h₁ h₂ using h₁
  use s₁, h₁
  simp at h₂
  exact ne_symm' h₂

@[simp]
theorem reachable_state₁_state₂ : sys.Reachable state₁ state₂ :=
  state₂_spec.1

@[simp]
theorem boxes_state₂_ne : state₂.boxes ≠ .singleton trBox₁ :=
  state₂_spec.2

@[simp]
theorem reachable_state₀_state₂ : sys.Reachable state₀ state₂ :=
  reachable_state₀_state₁.trans reachable_state₁_state₂

@[simp]
theorem points_state₁ : state₁.points = state₀.points :=
  points_eq_of_reachable reachable_state₀_state₁

@[simp]
theorem points_state₂ : state₂.points = state₀.points :=
  points_eq_of_reachable reachable_state₀_state₂

@[simp]
theorem trBox₁_mem_points_state₀ : trBox₁ ∈ state₀.points :=
  mem_points_of_mem_boxesReachable # by simp

@[simp]
theorem boxesReachable_state₂_subset_boxesReachable_state₀ :
state₂.boxesReachable ⊆ state₀.boxesReachable :=
  boxesReachable_subseq_of_reachable # by simp

@[simp, instance]
theorem alwaysMovable1_state₂ : AlwaysMovable1 state₂ :=
  alwaysMovable1_of_reachable (s := state₀) # by simp

@[simp]
theorem size_boxesReachable_state₀ : state₀.boxesReachable.size = size₀ :=
  state₀_spec.2

theorem size₀_eq : size₀ = state₀.boxesReachable.size :=
  size_boxesReachable_state₀.symm

@[simp]
theorem size₀_le_of_alwaysMovable1 {s} [hs : AlwaysMovable1 s] :
size₀ ≤ s.boxesReachable.size := by
  apply size₀_le (s := s); use hs

@[simp]
theorem size_boxesReachable_state₁ : state₁.boxesReachable.size = size₀ := by
  apply le_antisymm _ # by simp;; rw [size₀_eq]
  apply size_boxesReachable_le_of_reachable; simp

@[simp]
theorem size_boxesReachable_state₂ : state₂.boxesReachable.size = size₀ := by
  apply le_antisymm _ # by simp;; rw [size₀_eq]
  apply size_boxesReachable_le_of_reachable; simp

@[simp]
theorem trBox₁_mem_boxesReachable_state₂ : trBox₁ ∈ state₂.boxesReachable := by
  by_contra h₁; have h₂ : state₂.boxesReachable ⊂ state₀.boxesReachable
  · exact Set'.ssubset_of trBox₁ (by simp) h₁ (by simp)
  replace h₂ := Set'.size_lt_of_ssubset h₂; simp at h₂

@[simp]
theorem not_trBox₁_mem_boxes_state₀ : trBox₁ ∉ state₂.boxes := by
  have h := boxes_state₂_ne; contrapose! h; simpa [Set'.eq_singleton_iff_size]

omit H in
theorem box_mem_boxes_of {s : State} (h : s.boxes.size ≠ 0) : s.box ∈ s.boxes := by
  simp [Set'.eq_empty_iff] at h; apply Classical.epsilon_spec h

omit H in @[simp high]
theorem box_mem_boxes_of_alwaysMovable1 {s : State}
[hs : AlwaysMovable1 s] : s.box ∈ s.boxes := by
  apply box_mem_boxes_of; simp

omit H in @[simp]
theorem singleton_box {s : State} [hs : AlwaysMovable1 s] :
Set'.singleton s.box = s.boxes := by
  simp [Set'.singleton_eq_iff_size]

omit H in
theorem boxes_eq_singleton_box {s : State} [hs : AlwaysMovable1 s] :
s.boxes = Set'.singleton s.box := singleton_box.symm

@[simp]
theorem box_state₁ : state₁.box = trBox₁ := by
  have h := box_mem_boxes_of_alwaysMovable1 (s := state₁); simp at h; exact h

@[simp]
theorem box_state₂_ne_trBox₁ : state₂.box ≠ trBox₁ := by
  have h := box_mem_boxes_of_alwaysMovable1 (s := state₂)
  intro h₁; rw [h₁] at h; simp at h

omit H in
theorem box_eq_of_mem_boxes {s p} [hs : AlwaysMovable1 s]
(h : p ∈ s.boxes) : s.box = p := by
  rw [boxes_eq_singleton_box, Set'.mem_singleton] at h; exact h.symm

theorem state₃_spec : state₃.box = trBox₁ ∧
∃ s', sys.Reachable state₂ s' ∧ s'.BoxPushed state₃ := by
  apply Classical.epsilon_spec (p := λ s => s.box = trBox₁ ∧
    ∃ s', sys.Reachable state₂ s' ∧ s'.BoxPushed s)
  have h := trBox₁_mem_boxesReachable_state₂
  rw [mem_boxesReachable_iff] at h
  choose sx h₁ h₂ using h
  have h₃ : sx.boxes ≠ state₂.boxes
  · intro h₃; simp [h₃] at h₂
  have hsx := alwaysMovable1_of_reachable h₁
  choose s₁ s₂ t H₁ H₂ H₃ H₄ H₅ using sys.exi_tr_of_pred_diff
    (p := (·.box = trBox₁)) h₁ (by simp) (box_eq_of_mem_boxes h₂)
  refine' ⟨s₂, H₅, s₁, H₁, ⟨_, H₂⟩, _⟩
  have hs₁ := alwaysMovable1_of_reachable H₁
  have hs₂ := alwaysMovable1_of_reachable # sys.reachable_of_tr H₂
  simp only [ne_def, boxes_eq_singleton_box, Set'.singleton_eq_iff]; grind

theorem state₃'_spec : sys.Reachable state₂ state₃' ∧ state₃'.BoxPushed state₃ :=
  Classical.epsilon_spec state₃_spec.2

@[simp]
theorem box_state₃ : state₃.box = trBox₁ :=
  state₃_spec.1

@[simp]
theorem reachable_state₂_state₃' : sys.Reachable state₂ state₃' :=
  state₃'_spec.1

@[simp]
theorem boxPushed_state₃'_state₃ : state₃'.BoxPushed state₃ :=
  state₃'_spec.2

@[simp, instance]
theorem alwaysMovable1_state₃' : AlwaysMovable1 state₃' :=
  alwaysMovable1_of_reachable reachable_state₂_state₃'

@[simp]
theorem reachable_state₃'_state₃ : sys.Reachable state₃' state₃ :=
  reachable_of_boxPushed # by simp

@[simp, instance]
theorem alwaysMovable1_state₃ : AlwaysMovable1 state₃ :=
  alwaysMovable1_of_reachable reachable_state₃'_state₃

omit H in
theorem player'_eq_box_of_boxPushed {s s'} [hs : AlwaysMovable1 s]
(h : s.BoxPushed s') : s'.player = s.box := by
  rw [box_eq_of_mem_boxes # player'_mem_boxes_of_boxPushed h]

theorem player_state₃_eq_box_state₃' : state₃.player = state₃'.box :=
  player'_eq_box_of_boxPushed # by simp