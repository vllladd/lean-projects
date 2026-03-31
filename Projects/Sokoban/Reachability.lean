import Projects.Sokoban.Card

namespace Sokoban

open Classical in noncomputable
def State.boxesReachable (s : State) : Set' PointZ :=
  s.points.filter # λ p => ∃ s', sys.Reachable s s' ∧ p ∈ s'.boxes

open Classical in noncomputable
def State.trBox (s : State) : PointZ :=
  s.boxesReachable.headMap! # λ p => p * ⟨-1, 1⟩

open Classical in noncomputable
def State.BoxPushed (s s' : State) : Prop :=
  (∃ p, sys.tr s p = some s') ∧ s'.boxes ≠ s.boxes

-- #check 0 #exit

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

theorem points_eq_of_reachable {s s'} (h : sys.Reachable s s') : s'.points = s.points := by
  induction h; rfl
  clear s'
  nm a b c m h₁ h₂ ih
  simp [tr_eq_some_iff] at h₁
  simp_all only
  obtain ⟨w, h⟩ := h₁
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right⟩ := right
  split at right
  next h =>
    obtain ⟨w_1, h_1⟩ := right
    obtain ⟨left_2, right⟩ := h_1
    obtain ⟨left_3, right⟩ := right
    obtain ⟨left_4, right⟩ := right
    subst right
    simp_all only [points_moveBox, points_movePlayer]
  next h =>
    subst right
    simp_all only [Bool.not_eq_true, points_movePlayer]

theorem mem_points_of_mem_boxesReachable {s : State} {p}
(h : p ∈ s.boxesReachable) : p ∈ s.points := by
  simp [boxesReachable] at h; exact h.1

theorem boxesReachable_subseq_of_reachable {s s' : State}
(h : sys.Reachable s s') : s'.boxesReachable ⊆ s.boxesReachable := by
  intro p; simp [boxesReachable]
  intro h₁ s₁ h₂ h₃
  split_ands; rwa [←points_eq_of_reachable h]
  use s₁, h.trans h₂

theorem size_boxesReachable_le_of_reachable {s s' : State}
(h : sys.Reachable s s') : s'.boxesReachable.size ≤ s.boxesReachable.size :=
  Set'.size_le_of_subset # boxesReachable_subseq_of_reachable h

theorem exi_tr_of_boxPushed {s s' : State}
(h : s.BoxPushed s') : ∃ p, sys.tr s p = some s' := h.1

theorem boxes_ne_of_boxPushed {s s' : State}
(h : s.BoxPushed s') : s'.boxes ≠ s.boxes := h.2

theorem reachable_of_boxPushed {s s' : State}
(h : s.BoxPushed s') : sys.Reachable s s' :=
  sys.reachable_of_tr # exi_tr_of_boxPushed h |>.choose_spec

theorem wf_of_boxPushed {s s'} [hs : sys.WF s] (h : s.BoxPushed s') : sys.WF s' :=
  sys.wf_of_reachable # reachable_of_boxPushed h

theorem player'_mem_boxes_of_tr_and_boxes_ne {s s' p} (h₁ : sys.tr s p = some s')
(h₂ : s'.boxes ≠ s.boxes) : s'.player ∈ s.boxes := by
  simp [tr_eq_some_iff] at h₁
  choose d₁ h₁ h₃ h₄ using h₁
  split_ifs at h₄ with h₅
  on_goal 2 => simp [←h₄] at h₂
  choose d₂ h₄ h₆ h₇ h₈ using h₄
  simpa [←h₈, boxes]

theorem player'_mem_boxes_of_boxPushed {s s' : State}
(h : s.BoxPushed s') : s'.player ∈ s.boxes := by
  rcases h with ⟨⟨p, h₁⟩, h₂⟩; exact player'_mem_boxes_of_tr_and_boxes_ne h₁ h₂

theorem mem_boxesReachable_iff {s : State} {p} :
p ∈ s.boxesReachable ↔ ∃ s', sys.Reachable s s' ∧ p ∈ s'.boxes := by
  simp [boxesReachable]; intro s' h₁ h₂
  rw [←points_eq_of_reachable h₁]
  exact mem_points_of_mem_boxes h₂

theorem exi_boxPushed_of_boxes_ne {s s'} (h₁ : sys.Reachable s s') (h₂ : s'.boxes ≠ s.boxes) :
∃ s₁ s₂, sys.Reachable s s₁ ∧ s₁.BoxPushed s₂ ∧ sys.Reachable s₂ s' := by
  choose s₁ s₂ t h₃ h₄ h₅ h₆ h₇ using sys.exi_tr_of_pred_diff
    (p := (·.boxes = s'.boxes)) h₁ (ne_symm' h₂) rfl
  refine' ⟨s₁, s₂, h₃, ⟨⟨_, h₄⟩, _⟩, h₅⟩; grind