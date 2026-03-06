import Projects.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def translate (e : Edge) (offset : PointZ) : Edge where
  dir := e.dir
  offset := e.offset + if e.hor then offset.y else offset.x

@[simp]
theorem points_translate {offset} :
(e.translate offset).points = (translate offset).ft '' e.points := by
  ext p
  simp [translate, Edge.translate, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals revert h; simp [hd]

@[simp] theorem dir_translate {offset} : (e.translate offset).dir = e.dir := rfl

@[simp]
theorem offset_translate {offset} :
(e.translate offset).offset = e.offset + if e.hor then offset.y else offset.x := rfl

@[simp]
theorem dist_translate {offset p} :
(e.translate offset).dist p = e.dist (translate offset |>.ft' p) := by
  simp [translate, Edge.translate, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

@[simp]
theorem getBorderPoint_translate_of_down {dy p d} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).getBorderPoint p d = (translate ⟨0, dy⟩).ft
(e.getBorderPoint ((translate ⟨0, dy⟩).ft' p) d) := by
  simp [getBorderPoint]

@[simp]
theorem getBorderPoint₀_translate_of_down {dy p} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).getBorderPoint₀ p = (translate ⟨0, dy⟩).ft
(e.getBorderPoint₀ ((translate ⟨0, dy⟩).ft' p)) := by
  simp [getBorderPoint₀]

@[simp]
theorem getBorderPoints_translate_of_down {dy p d} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).getBorderPoints p d = (e.getBorderPoints ((translate
⟨0, dy⟩).ft' p) d).map ((translate ⟨0, dy⟩).ft) := by
  simp [getBorderPoints]

@[simp]
theorem ptsArr_translate_of_down {dy s} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).ptsArr s = e.ptsArr (translate ⟨0, dy⟩ |>.fs' s) := by
  ext:2; simp only [ptsArr, getBorderPoint_translate_of_down, List.pure_def, List.bind_eq_flatMap,
    List.flatMap_fn_singleton, List.map_map, Function.comp_def, taken_sym_of_basicSym',
    aPos_sym_of_basicSym', Set'.mem_map, ft'_eq_iff, exists_eq_right]

theorem defense_translate_of_down {dy} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).defense = e.defense.sym (translate ⟨0, dy⟩) := by
  simp only [defense, dist_translate, points_translate, Defense.sym, pw_fs'_of_basicSym,
    aPos_sym_of_basicSym', Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f₁, dist_translate, Int.reduceNeg, ptsArr_translate_of_down,
    getBorderPoint_translate_of_down, Option.pure_def, Option.bind_eq_bind, ne_eq,
    Option.bind_eq_some_iff', Option.some.injEq, ft_eq_iff, Option.guard_eq_some', exists_const,
    ↓existsAndEq, and_true, aPos_sym_of_basicSym', taken_sym_of_basicSym', Set'.mem_map, ft'_eq_iff,
    exists_eq_right, Option.map_bind, Function.comp_apply, Option.map_some,
    exists_exists_and_eq_and]
  simp_all only [dir_eq_of_down, fact_true, Int.reduceNeg]
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