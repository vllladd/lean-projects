import AP.AP.Defense.Corner

namespace AP.Box

def offset : ℕ := 106

def interior : Set' PointZ :=
  Point.nbhd (0 : PointZ) (offset - 1)

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
theorem ps_defense : defense.ps = Set.univ \ interior.toSet := by
  ext p; simp [interior, defense, Point.zero_def, Point.dist]
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

theorem mem_interior_of_simulate {s : State} {a : AStrat} {d : DStrat} {n r}
[hs : sys.WF s] [ha : a.WF] [hd : d.WF] (h₁ : defense.cnd s)
(h₂ : sys.simulate (Strat.f ⟨a, defense.st d⟩) s n = r) : r.1.aPos ∈ interior := by
  have H : defense.WF := inferInstance
  replace H := @H.not_mem_ps
  specialize @H s _ h₁ a _ d _ n
  simp [h₂] at H; exact H