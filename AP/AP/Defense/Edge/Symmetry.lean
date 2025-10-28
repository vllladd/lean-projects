import AP.AP.Defense.Edge.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def rotRight (e : Edge) : Edge where
  dir := e.dir.rotRight
  offset := if e.hor then -e.offset else e.offset

@[simp]
theorem points_rotRight : e.rotRight.points = rotRight.ft '' e.points := by
  ext p
  simp [rotRight, Edge.rotRight, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals
    revert h
    simp [hd, Point.ext_iff]
    constructor
    · intro h
      use ⟨p.y, -p.x⟩
      simp
      linarith
    · rintro ⟨⟨x₁, y₁⟩, h₁, h₂, h₃⟩
      linarith

@[simp]
theorem dist_rotRight {p} : e.rotRight.dist p = e.dist (rotRight.ft' p) := by
  simp [rotRight, Edge.rotRight, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

@[simp]
theorem rotRight_getBorderPoint₀ {p} :
e.rotRight.getBorderPoint₀ p = rotRight.ft (e.getBorderPoint₀ # rotRight.ft' p) := by
  simp [Edge.rotRight, rotRight, getBorderPoint₀, getBorderPoint]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd]

@[simp]
theorem rotRight_getBorderPoint_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoint p d = rotRight.ft (e.getBorderPoint (rotRight.ft' p) d) := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

@[simp]
theorem rotRight_getBorderPoints_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoints p d = (e.getBorderPoints (rotRight.ft' p) d).map rotRight.ft := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoints, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

@[simp] theorem dir_rotRight : e.rotRight.dir = e.dir.rotRight := rfl
@[simp] theorem vert_dir_of_hor [H : Fact e.hor] : e.dir.vert := H.1
@[simp] theorem not_hor_dir_of_hor [H : Fact e.hor] : ¬e.dir.hor := by simp
@[simp] theorem hor_dir_of_vert [H : Fact e.vert] : e.dir.hor := H.1
@[simp] theorem not_vert_dir_of_vert [H : Fact e.vert] : ¬e.dir.vert := by simp

@[simp] theorem offset_rotRight_eq_of_hor [H : Fact e.hor] :
e.rotRight.offset = -e.offset := by simp [Edge.rotRight]

@[simp] theorem offset_rotRight_eq_of_vert [H : Fact e.vert] :
e.rotRight.offset = e.offset := by simp [Edge.rotRight]

-- #check 0 #exit

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000000

theorem rotRight_defense_of_hor_fCase2 {e : Edge} {s : State} {p : PointZ}
[H : Fact e.hor] (h₁ : ¬p = s.aPos) (h₂ : p ∉ s.taken)
(h₃ : e.dist (rotRight.ft' s.aPos) = 2) : fCase2 s (rotRight.ft (e.getBorderPoint₀
(rotRight.ft' s.aPos))) (e.rotRight.getBorderPoints s.aPos) = some p ↔ fCase2 (rotRight.fs' s)
(e.getBorderPoint₀ (rotRight.ft' s.aPos)) (e.getBorderPoints (rotRight.ft' s.aPos)) =
some (rotRight.ft' p) := by
  unfold getBorderPoints
  simp [getBorderPoint₀, getBorderPoint]
  simp [fCase2, List.find?, ft'_eq_iff]
  split_ifs with h₄
  · -- aesop?
    --   aesop: internal error during proof reconstruction:
    --   goal 386 was not normalised
    sorry
  · sorry

#check 0 #exit

theorem rotRight_defense_of_hor [H : Fact e.hor] :
e.rotRight.defense = e.defense.sym rotRight := by
  simp [defense, Defense.sym]
  ext s p :2
  simp
  have h : ∀ p₁, rotRight.ft p₁ = p ↔ rotRight.ft' p = p₁
  · rcases p with ⟨x, y⟩; rintro ⟨x₁, y₁⟩
    simp [rotRight, Point.ext_iff]; constructor <;> intro h <;> constructor <;> linarith
  simp [h]; clear h
  simp [f, f']
  intro h₁ h₂
  split <;> nm x h₃ <;> clear x <;> try simp
  · simp [ft_eq_iff]
  · simp [ft'_eq_iff, ft_eq_iff]
  · simp [ft'_eq_iff, ft_eq_iff]
  · exact rotRight_defense_of_hor_fCase2 h₁ h₂ h₃
  · simp [ft'_eq_iff, ft_eq_iff]