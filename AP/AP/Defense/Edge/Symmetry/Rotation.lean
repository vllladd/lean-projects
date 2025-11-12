import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def rotRight (e : Edge) : Edge where
  dir := e.dir.rotRight
  offset := if e.hor then -e.offset else e.offset

protected def rotLeft (e : Edge) : Edge where
  dir := e.dir.rotLeft
  offset := if e.hor then e.offset else -e.offset

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
theorem defense_rotRight : e.rotRight.defense = e.defense.sym rotRight := by
  simp only [defense, dist_rotRight, points_rotRight, Defense.sym, pw_fs'_of_basicSym,
    aPos_sym_of_basicSym', Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f', dist_rotRight, getBorderPoint₀_rotRight, decide_not, getBorderPoints_rotRight,
    List.any_map, Function.comp_def', List.any_eq_true, decide_eq_true_eq, List.find?_map, ne_eq,
    Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff', Option.guard_eq_some',
    Option.some.injEq, exists_const, ↓existsAndEq, and_true, aPos_sym_of_basicSym',
    taken_sym_of_basicSym', Set'.mem_map, not_exists, not_and, Option.map_bind, Function.comp_apply,
    Option.map_some, ft_eq_iff, EmbeddingLike.apply_eq_iff_eq, forall_ne_iff_not,
    and_congr_left_iff, and_imp]
  intro h₁ h₂
  split <;> try simp [ft'_eq_iff, ft_eq_iff]
  · nm x h₃; clear x
    split_ifs with h₄; simp
    simp only [getBorderPoint₀, Point.ext_iff, rotRight_ft'_x, rotRight_ft'_y, getBorderPoints,
      Nat.cast_one, Int.reduceNeg, List.map_cons, List.map_nil, List.find?_cons_eq_some,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, rotRight_ft_x,
      neg_eq_iff_eq_neg, rotRight_ft_y, Bool.not_not, decide_eq_true_eq, List.find?_singleton,
      ite_not, Option.ite_none_left_eq_some, Option.some.injEq]
    rw [iff_iff_eq]
    congr 2
    generalize e.getBorderPoint (rotRight.ft' s.aPos) = g
    simp_all
    apply Iff.intro
    · intro a
      cases a with
      | inl h => simp_all only [Int.reduceNeg, not_false_eq_true, and_self, false_and, or_false]
      | inr h_1 => simp_all only [Int.reduceNeg, not_true_eq_false, false_and, not_false_eq_true,
        and_self, or_true]
    · intro a
      cases a with
      | inl h => simp_all only [Int.reduceNeg, not_false_eq_true, and_self, false_and, or_false]
      | inr h_1 => simp_all only [Int.reduceNeg, not_true_eq_false, false_and, not_false_eq_true,
        and_self, or_true]
  apply Iff.intro
  · intro a
    split
    next h =>
      simp_all only [Int.reduceNeg, not_false_eq_true, and_self, ↓reduceIte, Option.some.injEq,
        and_true]
      subst a
      simp_all only [Int.reduceNeg, System.Symmetry.ft'_ft]
    next
      h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.ite_none_right_eq_some, Option.some.injEq,
        not_and,
        Decidable.not_not, not_false_eq_true, and_self]
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      subst right
      simp_all only [Int.reduceNeg, not_false_eq_true, System.Symmetry.ft'_ft]
  · intro a
    split
    next h =>
      simp_all only [Int.reduceNeg, not_false_eq_true, and_self, ↓reduceIte, Option.some.injEq,
        System.Symmetry.ft_ft', and_true]
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.ite_none_right_eq_some, Option.some.injEq,
        not_and,
        Decidable.not_not, System.Symmetry.ft_ft', not_false_eq_true, and_self]