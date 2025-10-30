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

theorem defense_rotRight_fCase2 {e : Edge} {s : State} {p : PointZ} :
fCase2 s (rotRight.ft (e.getBorderPoint₀
(rotRight.ft' s.aPos))) (e.rotRight.getBorderPoints s.aPos) = some p ↔ fCase2 (rotRight.fs' s)
(e.getBorderPoint₀ (rotRight.ft' s.aPos)) (e.getBorderPoints (rotRight.ft' s.aPos)) =
some (rotRight.ft' p) := by
  unfold fCase2
  nth_rw 2 [rotRight.ft.option_eq_iff_map]
  rw [Option.map_some, System.Symmetry.ft_ft', apply_ite (f := Option.map rotRight.ft)]
  rw [taken_sym_of_basicSym', Option.map_some]
  
  convert_to _ ↔ (if rotRight.ft (e.getBorderPoint₀ (rotRight.ft' s.aPos)) ∉ s.taken then
      some (rotRight.ft (e.getBorderPoint₀ (rotRight.ft' s.aPos)))
    else
      Option.map (⇑rotRight.ft)
        (have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
        have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2;
        have f := λ ps₁ ps₂ ↦ do
          let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑rotRight.ft')) ps₁
          List.find? (λ p' ↦ decide (p' ∉ s.taken.map ⇑rotRight.ft' ∧ Point.dist p' p ≠ 1)) ps₂
        (f ps₁ ps₂).elim (f ps₂ ps₁) some)) =
    some p
  · simp [ft'_eq_iff]
  
  suffices h : (have ps₁ := e.rotRight.getBorderPoints s.aPos 1;
    have ps₂ := e.rotRight.getBorderPoints s.aPos 2;
    have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken ∧ Point.dist p' p ≠ 1)) ps₂;
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (Option.map (⇑rotRight.ft)
      (have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
      have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2;
      have f := λ ps₁ ps₂ ↦ do
        let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑rotRight.ft')) ps₁
        List.find? (λ p' ↦ decide (p' ∉ s.taken.map ⇑rotRight.ft' ∧ Point.dist p' p ≠ 1)) ps₂
      (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rw [h]
  
  iterate 2 rw [getBorderPoints_rotRight]
  
  trans (have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑rotRight.ft')) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken.map rotRight.ft' ∧ Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂ |>.map rotRight.ft).elim (f ps₂ ps₁ |>.map rotRight.ft) some)
  rotate_left; rw [Option.map_elim_fn_some]
  
  trans (have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ Option.map rotRight.ft # do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑rotRight.ft')) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken.map rotRight.ft' ∧ Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; rfl
  
  trans (have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map rotRight.ft')) ps₁
      Option.map rotRight.ft # List.find? (λ p' ↦ decide (p' ∉ s.taken.map rotRight.ft' ∧
        Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; simp
  
  trans ((have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) # List.map (rotRight.ft) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken ∧ Point.dist p' p ≠ 1)) #
        List.map (⇑rotRight.ft) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rfl
  
  trans ((have ps₁ := e.getBorderPoints (rotRight.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (rotRight.ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (rotRight.ft x ∈ s.taken)) ps₁ |>.map rotRight.ft
      List.find? (λ p' ↦ decide (rotRight.ft p' ∉ s.taken ∧
        Point.dist (rotRight.ft p') p ≠ 1)) ps₂ |>.map rotRight.ft
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · simp_rw [List.find?_map]; rfl
  
  generalize hps₁ : e.getBorderPoints (rotRight.ft' s.aPos) 1 = ps₁
  generalize hps₂ : e.getBorderPoints (rotRight.ft' s.aPos) 2 = ps₂
  
  convert_to
    (have f := fun ps₁ ps₂ ↦ do
      let p ← Option.map (⇑rotRight.ft) (List.find? (fun x ↦ decide
        (rotRight.ft x ∈ s.taken)) ps₁)
      Option.map (⇑rotRight.ft) (List.find? (fun p' ↦ decide
        (rotRight.ft p' ∉ s.taken ∧ Point.dist (rotRight.ft p') p ≠ 1)) ps₂);
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide (x ∈ s.taken.map ⇑rotRight.ft')) ps₁
      Option.map rotRight.ft # List.find? (fun p' ↦ decide (p' ∉ s.taken.map ⇑rotRight.ft' ∧
        Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  
  trans (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide (rotRight.ft x ∈ s.taken)) ps₁
      Option.map rotRight.ft # List.find? (fun p' ↦ decide (rotRight.ft p' ∉ s.taken ∧
         Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; simp [ft'_eq_iff]
  
  trans (have f := fun ps₁ ps₂ ↦ do
    let p ← (List.find? (fun x ↦ decide (rotRight.ft x ∈ s.taken)) ps₁)
    Option.map rotRight.ft (List.find? (fun p' ↦ decide (rotRight.ft p' ∉ s.taken ∧
      Point.dist (rotRight.ft p') (rotRight.ft p) ≠ 1)) ps₂)
  (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  · simp [Option.bind_map]
  
  simp only [rotRight_dist_rotRight, ne_eq, Bool.decide_and, decide_not, Option.bind_eq_bind]

@[simp]
theorem defense_rotRight : e.rotRight.defense = e.defense.sym rotRight := by
  simp only [defense, dist_rotRight, points_rotRight, Defense.sym, aPos_sym_of_basicSym',
    Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f', dist_rotRight, getBorderPoint₀_rotRight, decide_not,
    getBorderPoints_rotRight, List.find?_append, List.find?_map, Function.comp_def',
    List.find?_singleton, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not,
    ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff', Option.guard_eq_some',
    Option.some.injEq, exists_const, ↓existsAndEq, and_true, aPos_sym_of_basicSym',
    taken_sym_of_basicSym', Set'.mem_map, not_exists, not_and, decide_eq_true_eq, Option.map_bind,
    Function.comp_apply, Option.map_some, ft_eq_iff, EmbeddingLike.apply_eq_iff_eq,
    forall_ne_iff_not, and_congr_left_iff, and_imp]
  intro h₁ h₂
  split <;> try simp [ft'_eq_iff, ft_eq_iff]
  exact defense_rotRight_fCase2