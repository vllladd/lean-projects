import AP.AP.Defense.Corner

namespace AP.Box

def offset : ℕ := 106

def interior : Set' PointZ :=
  (0 : PointZ).nbhd Box.offset

def interior₁ : Set' PointZ :=
  (0 : PointZ).nbhd (offset - 1)

def corner₀ : Corner where
  dir := .up
  offset := ⟨offset, -offset⟩

def corners : List Corner :=
  List.range 4 |>.map (Corner.rotRight^[·] corner₀)

def defenses : List Defense :=
  corners.map (·.defense)

def defense : Defense :=
  .ofList defenses

def Cnd (s : State) : Prop :=
  corner₀.RotCnd s

def guardTiles : Set' PointZ :=
  .unionList # corners.map # λ c => c.offset * 103 / 106 |>.nbhd 2

-- #check 0 #exit

-----

@[simp] theorem length_corners : corners.length = 4 := rfl
@[simp] theorem length_defenses : defenses.length = 4 := rfl

@[simp]
theorem getElem_corners_eq_iter_rotRight {i h} :
corners[i]'h = Corner.rotRight^[i] corner₀ := by
  simp [corners]; decide +revert

@[simp] theorem edge₁_corner₀_dist_zero : corner₀.edge₁.dist 0 = offset := rfl
@[simp] theorem edge₂_corner₀_dist_zero : corner₀.edge₂.dist 0 = offset := rfl

@[simp]
instance : corner₀.Square := by
  constructor; simp

@[simp]
instance : corner₀.SquareGe 6 := by
  constructor; simp [offset]

theorem compatible_0_1 : defenses[0].Compatible defenses[1] := by
  simp [defenses]; apply Corner.compatible_rotRight

theorem compatible'_0_2 : defenses[0].Compatible' Cnd defenses[2] := by
  simp [defenses]; apply Corner.compatible'_rot180

theorem compatible_0_3 : defenses[0].Compatible defenses[3] := by
  simp [defenses]; apply Corner.compatible_rotLeft

theorem compatible_1_2 : defenses[1].Compatible defenses[2] := by
  simp [defenses]; apply Corner.compatible_rotRight

theorem compatible'_1_3 : defenses[1].Compatible' Cnd defenses[3] := by
  simp [defenses]; unfold Cnd
  rw [←Corner.rot180_rotRight, ←Corner.rotCnd_rotRight]
  apply Corner.compatible'_rot180

theorem compatible_2_3 : defenses[2].Compatible defenses[3] := by
  simp [defenses]; apply Corner.compatible_rotRight

theorem compatible_getElem_defenses {i j} (h₁ : i < j) (h₂ : j < defenses.length) :
defenses[i].Compatible' Cnd defenses[j] := by
  revert h₂; rw! [length_defenses]; intro h₂
  obtain (rfl | rfl | rfl) : i = 0 ∨ i = 1 ∨ i = 2; omega
  · obtain (rfl | rfl | rfl) : j = 1 ∨ j = 2 ∨ j = 3; omega
    · exact Defense.compatible'_of_compatible compatible_0_1
    · exact compatible'_0_2
    · exact Defense.compatible'_of_compatible compatible_0_3
  · obtain (rfl | rfl) : j = 2 ∨ j = 3; omega
    · exact Defense.compatible'_of_compatible compatible_1_2
    · exact compatible'_1_3
  · obtain rfl : j = 3; omega
    exact Defense.compatible'_of_compatible compatible_2_3

theorem cnd_eq_forall_cnd : Cnd = λ s => ∀ d ∈ defenses, d.cnd s := by
  ext s; simp [Cnd, defenses, corners, Corner.rotCnd_eq_and]

theorem compatibleList_defenses :  Defense.CompatibleList defenses := by
  rw [Defense.compatibleList_iff_getElem]
  intro i j h₁ h₂; simp [←cnd_eq_forall_cnd]
  exact compatible_getElem_defenses h₁ h₂

@[simp]
instance : defense.WF := by
  apply Defense.wf_ofList; simp [defenses]
  exact compatibleList_defenses

@[simp]
theorem ps_defense : defense.ps = Set.univ \ interior₁.toSet := by
  ext p; simp [interior₁, defense, Point.dist]
  constructor
  · unfold offset
    rintro ⟨d, hd, h⟩ h₁
    simp [defenses, corners] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals
      by_contra! h₂
      simp [abs_le] at h₁ h₂
      simp [corner₀, Corner.points, Corner.edge₁, Corner.edge₂, Edge.points,
        Edge.memPoints, offset] at h; omega
  · intro h
    simp [imp_iff_or_not, lt_abs, offset] at h
    simp [defenses, corners, corner₀, Corner.points, Corner.edge₁, Corner.edge₂, Edge.points,
      Edge.memPoints, offset]; omega

theorem mem_interior₁_of_simulate {s : State} {a : AStrat} {d : DStrat} {n r}
[hs : sys.WF s] [ha : a.WF] [hd : d.WF] (h₁ : defense.cnd s)
(h₂ : sys.simulate (Strat.f ⟨a, defense.st d⟩) s n = r) : r.1.aPos ∈ interior₁ := by
  have H : defense.WF := inferInstance
  replace H := @H.not_mem_ps
  specialize @H s _ h₁ a _ d _ n
  simp [h₂] at H; exact H

@[simp]
theorem size_guardTiles : guardTiles.size = 100 := by
  native_decide

@[simp]
theorem offset_corner₀ : corner₀.offset = ⟨106, -106⟩ := rfl

theorem cnd_defense_iff_guardTiles {s} : defense.cnd s ↔ s.pw = 1 ∧
s.aPos ∈ (0 : PointZ).nbhd 100 ∧ guardTiles ⊆ s.taken := by
  simp only [defense, defenses, Corner.defense, corners, corner₀, offset, Nat.cast_ofNat,
    Int.reduceNeg, List.range_map_iterate, List.iterate, Corner.rotRight, Dir.rotRight_up,
    rotRight_ft_mk, neg_neg, Dir.rotRight_right, Dir.rotRight_down, List.map_cons, List.map_nil,
    Defense.ofList_cons, Defense.ofList_nil, Defense.merge_empty_right, Defense.cnd_merge,
    Corner.cnd, Corner.dist, Edge.dist, Corner.edge₁, Corner.edge, Point.coord'_up, instFactTrue_aP,
    Edge.dir_eq_of_up, sub_neg_eq_add, Corner.edge₂, Point.coord'_right, le_inf_iff, Corner.cnd',
    tsub_le_iff_right, Point.coord'_down, Edge.dir_eq_of_down, Point.coord'_left, Dir.rotRight_left,
    Int.min_add_right, Point.mem_nbhd, Point.dist, Point.x_ofNat, CharP.cast_eq_zero, zero_sub,
    abs_neg, Point.y_ofNat, sup_le_iff, guardTiles, Set'.unionList_cons, Set'.unionList_nil,
    Set'.union_empty, Set'.subset_def, Set'.mem_union, Set'.mem_ofList, Point.x_div, Point.x_mul,
    Int.reduceMul, Int.reduceDiv, Point.y_div, Point.y_mul, neg_mul]
  rcases s.aPos with ⟨ax, ay⟩
  simp only [Point.forall_iff, Int.reduceNeg]
  by_cases hpw : s.pw = 1
  rotate_left; simp only [hpw, false_and, and_self, Int.reduceNeg]
  simp only [hpw, true_and, abs_le, Int.reduceNeg, neg_le_sub_iff_le_add, Int.reduceAdd,
    tsub_le_iff_right]
  apply Iff.intro
  · intro a
    obtain ⟨left, right⟩ := a
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_1, right_3⟩ := left_1
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_2, right_5⟩ := left_2
    obtain ⟨left_3, right⟩ := right
    simp_all only [Int.reduceNeg]
    use by omega
    rintro x y (h | h | h | h)
    · apply right_1 <;> omega
    · apply right_3 <;> omega
    · apply right_5 <;> omega
    · apply right <;> omega
  · rintro ⟨h₁, h₂⟩
    split_ands <;> try omega
    all_goals
      intro x y a a_1 a_2 a_3
      apply h₂; omega

@[simp]
theorem interior₁_subset_interior : interior₁ ⊆ interior := by
  intro p; simp [interior₁, interior, Point.dist]; omega

@[simp]
theorem guardTiles_subset_interior₁ : guardTiles ⊆ interior₁ := by
  native_decide

@[simp]
theorem guardTiles_subset_interior : guardTiles ⊆ interior :=
  Set'.subset_trans guardTiles_subset_interior₁ interior₁_subset_interior

theorem le_dist_center_of_mem_guardTiles {p} (h : p ∈ guardTiles) : 101 ≤ p.dist 0 := by
  simp only [guardTiles, corners, corner₀, offset, Nat.cast_ofNat, Int.reduceNeg,
    List.range_map_iterate, List.iterate, Corner.rotRight_mk, Dir.rotRight_up, rotRight_ft_mk,
    neg_neg, Dir.rotRight_right, Dir.rotRight_down, List.map_cons, List.map_nil,
    Set'.unionList_cons, Set'.unionList_nil, Set'.union_empty, Set'.mem_union, Set'.mem_ofList,
    Point.mem_nbhd, Point.dist, Point.x_div, Point.x_mul, Point.x_ofNat, Int.reduceMul,
    Int.reduceDiv, Point.y_div, Point.y_mul, Point.y_ofNat, neg_mul, sup_le_iff, abs_le,
    neg_le_sub_iff_le_add, Int.reduceAdd, tsub_le_iff_right, CharP.cast_eq_zero, sub_zero,
    le_sup_iff, le_abs] at h ⊢; omega