import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def rotRight (e : Edge) : Edge where
  dir := e.dir.rotRight
  offset := if e.hor then -e.offset else e.offset

protected def rotLeft (e : Edge) : Edge where
  dir := e.dir.rotLeft
  offset := if e.hor then e.offset else -e.offset

protected def rot180 (e : Edge) : Edge where
  dir := e.dir⁻¹
  offset := -e.offset

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
theorem points_rotLeft : e.rotLeft.points = rotLeft.ft '' e.points := by
  ext p
  unfold rotLeft rotRight
  simp [Edge.rotLeft, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals
    revert h
    simp [hd, Point.ext_iff]
    constructor
    · intro h
      use ⟨-p.y, p.x⟩
      simp
      linarith
    · rintro ⟨⟨x₁, y₁⟩, h₁, h₂, h₃⟩
      linarith

@[simp]
theorem dist_rotRight {p} : e.rotRight.dist p = e.dist (rotRight.ft' p) := by
  simp [rotRight, Edge.rotRight, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

@[simp]
theorem getBorderPoint_rotRight {p d} :
e.rotRight.getBorderPoint p d = rotRight.ft (e.getBorderPoint (rotRight.ft' p) d) := by
  cases h : e.dir <;> simp [Edge.rotRight, getBorderPoint, h] <;> ring_nf

@[simp]
theorem getBorderPoint₀_rotRight {p} :
e.rotRight.getBorderPoint₀ p = rotRight.ft (e.getBorderPoint₀ # rotRight.ft' p) := by
  simp [getBorderPoint₀]

@[simp]
theorem getBorderPoints_rotRight {p d} :
e.rotRight.getBorderPoints p d = (e.getBorderPoints (rotRight.ft' p) d).map rotRight.ft := by
  simp [getBorderPoints]

@[simp] theorem dir_rotRight : e.rotRight.dir = e.dir.rotRight := rfl

@[simp] theorem offset_rotRight_eq_of_hor [H : Fact e.hor] :
e.rotRight.offset = -e.offset := by simp [Edge.rotRight]

@[simp] theorem offset_rotRight_eq_of_vert [H : Fact e.vert] :
e.rotRight.offset = e.offset := by simp [Edge.rotRight]

@[simp]
theorem rotRight_rotLeft : e.rotLeft.rotRight = e := by
  cases h : e.dir <;> simp [Edge.rotRight, Edge.rotLeft, Edge.ext_iff, h]

@[simp]
theorem rotLeft_rotRight : e.rotRight.rotLeft = e := by
  cases h : e.dir <;> simp [Edge.rotRight, Edge.rotLeft, Edge.ext_iff, h]

@[simp] theorem dir_rotLeft : e.rotLeft.dir = e.dir.rotLeft := rfl

@[simp]
theorem ptsArr_rotRight {s} : e.rotRight.ptsArr s = e.ptsArr (rotRight.fs' s) := by
  ext:2; simp only [ptsArr, getBorderPoint_rotRight, List.pure_def, List.bind_eq_flatMap,
    List.flatMap_fn_singleton, List.map_map, Function.comp_def', taken_sym_of_basicSym',
    aPos_sym_of_basicSym', Set'.mem_map, ft'_eq_iff, exists_eq_right]

@[simp]
theorem defense_rotRight : e.rotRight.defense = e.defense.sym rotRight := by
  simp only [defense, dist_rotRight, points_rotRight, Defense.sym, pw_fs'_of_basicSym,
    aPos_sym_of_basicSym', Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f₁, dist_rotRight, Int.reduceNeg, ptsArr_rotRight, getBorderPoint_rotRight,
    Option.pure_def, Option.bind_eq_bind, ne_eq, Option.bind_eq_some_iff', Option.some.injEq,
    ft_eq_iff, Option.guard_eq_some', exists_const, ↓existsAndEq, and_true, aPos_sym_of_basicSym',
    taken_sym_of_basicSym', Set'.mem_map, ft'_eq_iff, exists_eq_right, Option.map_bind,
    Function.comp_apply, Option.map_some, exists_exists_and_eq_and]
  apply Iff.intro
  · intro a
    obtain ⟨left, right⟩ := a
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right⟩ := right
    obtain ⟨left_1, right_1⟩ := h
    simp_all only [Int.reduceNeg, Option.some.injEq, exists_eq_left',
      EmbeddingLike.apply_eq_iff_eq,
      not_false_eq_true, System.Symmetry.ft_ft', and_self]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    simp_all only [Int.reduceNeg, EmbeddingLike.apply_eq_iff_eq, System.Symmetry.ft_ft',
      Option.some.injEq, exists_eq_left', not_false_eq_true, and_self]

@[simp]
theorem rotRight_rotRight : e.rotRight.rotRight = e.rot180 := by
  simp [Edge.rotRight, Edge.rot180]
  rcases e with ⟨dir, offset⟩
  cases dir <;> simp

@[simp]
theorem rotLeft_rotLeft : e.rotLeft.rotLeft = e.rot180 := by
  simp [Edge.rotLeft, Edge.rot180]
  rcases e with ⟨dir, offset⟩
  cases dir <;> simp <;> rfl

@[simp]
theorem rot180_rotRight : e.rotRight.rot180 = e.rotLeft := by
  rcases e with ⟨dir, offset⟩; cases dir <;> simp [Edge.rotLeft, Edge.rotRight, Edge.rot180]

@[simp]
theorem defense_rotLeft : e.rotLeft.defense = e.defense.sym rotLeft := by
  trans Edge.rotRight^[3] e |>.defense; simp
  dsimp; simp only [defense_rotRight]; simp

@[simp]
theorem defense_rot180 : e.rot180.defense = e.defense.sym rot180 := by
  rw [←rotRight_rotRight, defense_rotRight]; simp