import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def flipV (e : Edge) : Edge where
  dir := if e.hor then e.dir⁻¹ else e.dir
  offset := if e.hor then -e.offset else e.offset

@[simp]
theorem points_flipV : e.flipV.points = flipV.ft '' e.points := by
  ext p
  simp [flipV, Edge.flipV, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals
    revert h
    simp [hd, Point.ext_iff]
    constructor
    · intro h
      use ⟨p.x, -p.y⟩
      simp
      linarith
    · rintro ⟨⟨x₁, y₁⟩, h₁, h₂, h₃⟩
      linarith

@[simp]
theorem dist_flipV {p} : e.flipV.dist p = e.dist (flipV.ft' p) := by
  simp [flipV, Edge.flipV, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

@[simp] theorem dir_flipV : e.flipV.dir = if e.hor then e.dir⁻¹ else e.dir := rfl
@[simp] theorem offset_flipV : e.flipV.offset = if e.hor then -e.offset else e.offset := rfl

@[simp]
theorem getBorderPoint₀_flipV_of_hor {p} [H : Fact e.hor] :
e.flipV.getBorderPoint₀ p = flipV.ft (e.getBorderPoint₀ p) := by
  simp [getBorderPoint₀, getBorderPoint]

@[simp]
theorem getBorderPoint_flipV_of_hor [H : Fact e.hor] {p d} :
e.flipV.getBorderPoint p d = flipV.ft (e.getBorderPoint p d) := by
  simp [getBorderPoint]

@[simp]
theorem getBorderPoints_flipV_of_hor [H : Fact e.hor] {p d} :
e.flipV.getBorderPoints p d = (e.getBorderPoints p d).map flipV.ft := by
  simp [getBorderPoints]

@[simp]
theorem getBorderPoint₀_rot180_ft_of_hor {p} [H : Fact e.hor] :
e.getBorderPoint₀ (rot180.ft p) = flipH.ft (e.getBorderPoint₀ p) := by
  simp [getBorderPoint₀, getBorderPoint]

@[simp]
theorem getBorderPoint_rot180_ft_of_hor {p d} [H : Fact e.hor] :
e.getBorderPoint (rot180.ft p) d = flipH.ft (e.getBorderPoint p (-d)) := by
  simp [getBorderPoint, add_comm]

@[simp]
theorem flipV_flipV : e.flipV.flipV = e := by
  cases h : e.dir <;> ext <;> simp [h]

@[simp]
theorem rot180_points_eq_flipV_points_of_hor [H : Fact e.hor] :
rot180.ft '' e.points = flipV.ft '' e.points := by
  rcases e.dir_eq_or_eq_of_hor with h | h <;> ext p <;> simp [h, points, memPoints]

@[simp]
theorem dist_flipV_ft_eq_of_hor [H : Fact e.hor] {p} :
e.dist (flipV.ft p) = e.dist (-p) := by
  rcases e.dir_eq_or_eq_of_hor with h | h <;> simp [h, dist]

@[simp]
theorem dist_rot180_ft_eq_dist_flipV_ft_of_hor [H : Fact e.hor] {p} :
e.dist (rot180.ft p) = e.dist (-p) := by
  rcases e.dir_eq_or_eq_of_hor with h | h <;> simp [h, dist]

-- #check 0 #exit

theorem defense_flipV_of_up [H : Fact # e.dir = .up] :
e.flipV.defense = e.defense.sym rot180 := by
  simp [defense, Defense.sym, dist, neg_sub_comm]
  ext s p :2
  simp [ft_eq_iff, f, f']
  intro h₁ h₂
  split
  all_goals
    nm x h₃; clear x
    conv_rhs => rw [Equiv.option_eq_iff_map (e := rot180.ft)]
  · simp
  · sorry
  · sorry
  · sorry
  · sorry
  · simp