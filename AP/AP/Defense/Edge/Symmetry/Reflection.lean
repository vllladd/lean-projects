import AP.AP.Defense.Edge.Symmetry.Basic

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

theorem find?_eq_some_equiv_iff {e : α ≃ α} {p : α → Bool} {x} :
xs.find? p = some (e x) ↔ (xs.map e.symm).find? (p ∘ e) = some x := by
  simp [find?_eq_some_iff_append]; constructor
  · rintro ⟨h₁, xs, ⟨ys, rfl⟩, h₂⟩; use e x; simp [h₁]; use xs; simpa
  · rintro ⟨x, ⟨h₁, xs, ⟨h₂, rfl⟩, h₃⟩, rfl⟩; simp [h₁]; use xs; simpa

-- #check 0 #exit

end List

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

-- @[simp]
-- theorem map_flipV_ft_getBorderPoints_of_hor

-- #check 0 #exit

theorem defense_flipV_of_up [H : Fact # e.dir = .up] :
e.flipV.defense = e.defense.sym rot180 := by
  simp only [defense, dist, dir_flipV, hor, dir_eq_of_up, Dir.vert_up, ↓reduceIte, Dir.inv_up,
    instFactTrue_aP, dir_eq_of_down, offset_flipV, points_flipV, Defense.sym,
    System.Symmetry.SelfInverse.fs'_eq_fs, aPos_sym_of_basicSym, rot180_ft_y, neg_sub_comm,
    rot180_points_eq_flipV_points_of_hor, Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f', dist_flipV, System.Symmetry.SelfInverse.ft'_eq_ft, dist_flipV_ft_eq_of_hor,
    getBorderPoint₀_flipV_of_hor, decide_not, getBorderPoints_flipV_of_hor, List.find?_append,
    List.find?_map, Function.comp_def', List.find?_singleton, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, ite_not, ne_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq, exists_const, ↓existsAndEq,
    and_true, aPos_sym_of_basicSym, dist_rot180_ft_eq_dist_flipV_ft_of_hor,
    getBorderPoint₀_rot180_ft_of_hor, taken_sym_of_basicSym, Set'.mem_map, ft_eq_iff,
    exists_eq_right, rot180_ft_flipH_ft, Option.map_bind, Function.comp_apply, Option.map_some,
    EmbeddingLike.apply_eq_iff_eq, System.Symmetry.SelfInverse.ft_ft, and_congr_left_iff, and_imp]
  intro h₁ h₂
  sorry
  -- split <;> try simp [ft_eq_iff]
  -- all_goals
  --   nm x h₃; clear x
  -- 
  -- ·
  --   iterate 2 rw [List.find?_eq_some_equiv_iff]
  --   simp only [Function.comp_def', System.Symmetry.SelfInverse.ft_ft, System.Symmetry.ft_symm,
  --     System.Symmetry.SelfInverse.ft'_eq_ft]
  --     
  --   suffices h : ((e.getBorderPoints s.aPos 1).map flipV.ft).find?
  --     (λ x => !decide (x ∈ s.taken)) = ((e.getBorderPoints (rot180.ft s.aPos) 1).map
  --     rot180.ft).find? (λ x => !decide (x ∈ s.taken))
  --   · rw [h]
  --   simp [getBorderPoints, getBorderPoint]
  -- 
  -- exact defense_flipV_of_up_fCase2