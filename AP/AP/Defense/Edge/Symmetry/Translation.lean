import AP.AP.Defense.Edge.Symmetry.Basic

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

theorem defense_translate_of_down {dy} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).defense = e.defense.sym (translate ⟨0, dy⟩) := by
  simp only [defense, dist_translate, points_translate, Defense.sym, pw_fs'_of_basicSym,
    aPos_sym_of_basicSym', Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f', dist_translate, getBorderPoint₀_translate_of_down, decide_not,
    getBorderPoints_translate_of_down, List.any_map, Function.comp_def', List.any_eq_true,
    decide_eq_true_eq, List.find?_map, ne_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq, exists_const, ↓existsAndEq,
    and_true, aPos_sym_of_basicSym', taken_sym_of_basicSym', Set'.mem_map, not_exists, not_and,
    Option.map_bind, Function.comp_apply, Option.map_some, ft_eq_iff, EmbeddingLike.apply_eq_iff_eq,
    forall_ne_iff_not, and_congr_left_iff, and_imp]
  intro h₁ h₂
  split <;> try simp [ft'_eq_iff, ft_eq_iff]
  · nm x h₃; clear x
    split_ifs with h₄; simp
    simp only [getBorderPoint₀, getBorderPoint, dir_eq_of_down, translate_ft'_x, sub_zero, add_zero,
      Point.ext_iff, translate_ft'_y, eq_sub_iff_add_eq, getBorderPoints, Nat.cast_one,
      Int.reduceNeg, List.map_cons, List.map_nil, List.find?_cons_eq_some, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, translate_ft_x, translate_ft_y, Bool.not_not,
      decide_eq_true_eq, List.find?_singleton, ite_not, Option.ite_none_left_eq_some,
      Option.some.injEq]
  apply defense_sym_of_down_fCase2 <;> simp