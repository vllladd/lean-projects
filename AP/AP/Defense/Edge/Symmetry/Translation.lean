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

theorem defense_translate_of_down_fCase2 {e : Edge} {s p dy} [H : Fact # e.dir = .down] :
fCase2 s ((translate ⟨0, dy⟩).ft (e.getBorderPoint₀ ((translate ⟨0, dy⟩).ft' s.aPos)))
((e.translate ⟨0, dy⟩).getBorderPoints s.aPos) = some p ↔
fCase2 ((translate ⟨0, dy⟩).fs' s) (e.getBorderPoint₀ ((translate ⟨0, dy⟩).ft' s.aPos))
(e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos)) = some ((translate ⟨0, dy⟩).ft' p) := by
  unfold fCase2
  nth_rw 2 [(translate ⟨0, dy⟩).ft.option_eq_iff_map]
  rw [Option.map_some, System.Symmetry.ft_ft', apply_ite (f := Option.map (translate ⟨0, dy⟩).ft)]
  rw [taken_sym_of_basicSym', Option.map_some]
  
  convert_to _ ↔ (if (translate ⟨0, dy⟩).ft (e.getBorderPoint₀
    ((translate ⟨0, dy⟩).ft' s.aPos)) ∉ s.taken then
      some ((translate ⟨0, dy⟩).ft (e.getBorderPoint₀ ((translate ⟨0, dy⟩).ft' s.aPos)))
    else
      Option.map (⇑(translate ⟨0, dy⟩).ft)
        (have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
        have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2;
        have f := λ ps₁ ps₂ ↦ do
          let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑(translate ⟨0, dy⟩).ft')) ps₁
          List.find? (λ p' ↦ decide (p' ∉ s.taken.map ⇑(translate ⟨0, dy⟩).ft' ∧
          Point.dist p' p ≠ 1)) ps₂
        (f ps₁ ps₂).elim (f ps₂ ps₁) some)) =
    some p
  · simp [ft'_eq_iff]
  
  suffices h : (have ps₁ := (e.translate ⟨0, dy⟩).getBorderPoints s.aPos 1;
    have ps₂ := (e.translate ⟨0, dy⟩).getBorderPoints s.aPos 2;
    have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken ∧ Point.dist p' p ≠ 1)) ps₂;
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (Option.map (⇑(translate ⟨0, dy⟩).ft)
      (have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
      have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2;
      have f := λ ps₁ ps₂ ↦ do
        let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑(translate ⟨0, dy⟩).ft')) ps₁
        List.find? (λ p' ↦ decide (p' ∉ s.taken.map ⇑(translate ⟨0, dy⟩).ft' ∧
        Point.dist p' p ≠ 1)) ps₂
      (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rw [h]

  iterate 2 rw [getBorderPoints_translate_of_down]
  
  trans (have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑(translate ⟨0, dy⟩).ft')) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken.map (translate ⟨0, dy⟩).ft' ∧
      Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂ |>.map (translate ⟨0, dy⟩).ft).elim (f ps₂ ps₁ |>.map (translate ⟨0, dy⟩).ft) some)
  rotate_left; rw [Option.map_elim_fn_some]
  
  trans (have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ Option.map (translate ⟨0, dy⟩).ft # do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑(translate ⟨0, dy⟩).ft')) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken.map (translate ⟨0, dy⟩).ft' ∧
      Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; rfl
  
  trans (have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map (translate ⟨0, dy⟩).ft')) ps₁
      Option.map (translate ⟨0, dy⟩).ft # List.find? (λ p' ↦ decide
      (p' ∉ s.taken.map (translate ⟨0, dy⟩).ft' ∧
        Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; simp
  
  trans ((have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) # List.map ((translate ⟨0, dy⟩).ft) ps₁
      List.find? (λ p' ↦ decide (p' ∉ s.taken ∧ Point.dist p' p ≠ 1)) #
        List.map (⇑(translate ⟨0, dy⟩).ft) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rfl
  
  trans ((have ps₁ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide ((translate ⟨0, dy⟩).ft x ∈ s.taken)) ps₁
        |>.map (translate ⟨0, dy⟩).ft
      List.find? (λ p' ↦ decide ((translate ⟨0, dy⟩).ft p' ∉ s.taken ∧
        Point.dist ((translate ⟨0, dy⟩).ft p') p ≠ 1)) ps₂ |>.map (translate ⟨0, dy⟩).ft
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · simp_rw [List.find?_map]; rfl
  
  generalize hps₁ : e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 1 = ps₁
  generalize hps₂ : e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos) 2 = ps₂
  
  convert_to
    (have f := fun ps₁ ps₂ ↦ do
      let p ← Option.map (⇑(translate ⟨0, dy⟩).ft) (List.find? (fun x ↦ decide
        ((translate ⟨0, dy⟩).ft x ∈ s.taken)) ps₁)
      Option.map (⇑(translate ⟨0, dy⟩).ft) (List.find? (fun p' ↦ decide
        ((translate ⟨0, dy⟩).ft p' ∉ s.taken ∧ Point.dist ((translate ⟨0, dy⟩).ft p') p ≠ 1)) ps₂);
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide (x ∈ s.taken.map ⇑(translate ⟨0, dy⟩).ft')) ps₁
      Option.map (translate ⟨0, dy⟩).ft # List.find? (fun p' ↦ decide (p' ∉ s.taken.map
        ⇑(translate ⟨0, dy⟩).ft' ∧ Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  
  trans (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide ((translate ⟨0, dy⟩).ft x ∈ s.taken)) ps₁
      Option.map (translate ⟨0, dy⟩).ft # List.find? (fun p' ↦ decide
        ((translate ⟨0, dy⟩).ft p' ∉ s.taken ∧ Point.dist p' p ≠ 1)) ps₂
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; simp [ft'_eq_iff]
  
  trans (have f := fun ps₁ ps₂ ↦ do
    let p ← (List.find? (fun x ↦ decide ((translate ⟨0, dy⟩).ft x ∈ s.taken)) ps₁)
    Option.map (translate ⟨0, dy⟩).ft (List.find?
      (fun p' ↦ decide ((translate ⟨0, dy⟩).ft p' ∉ s.taken ∧
      Point.dist ((translate ⟨0, dy⟩).ft p') ((translate ⟨0, dy⟩).ft p) ≠ 1)) ps₂)
  (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  · simp [Option.bind_map]
  
  simp only [translate, ft_mkSym, Equiv.coe_fn_mk, Point.dist_add_right_cancel, ne_eq,
    Bool.decide_and, decide_not, Option.bind_eq_bind]

theorem defense_translate_of_down {dy} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).defense = e.defense.sym (translate ⟨0, dy⟩) := by
  simp only [defense, dist_translate, points_translate, Defense.sym, pw_fs'_of_basicSym,
    aPos_sym_of_basicSym', Defense.mk.injEq, true_and]
  ext s p :2
  simp only [f, f', dist_translate, getBorderPoint₀_translate_of_down, decide_not,
    getBorderPoints_translate_of_down, List.find?_append, List.find?_map, Function.comp_def',
    List.find?_singleton, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not,
    ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff', Option.guard_eq_some',
    Option.some.injEq, exists_const, ↓existsAndEq, and_true, aPos_sym_of_basicSym',
    taken_sym_of_basicSym', Set'.mem_map, not_exists, not_and, decide_eq_true_eq, Option.map_bind,
    Function.comp_apply, Option.map_some, ft_eq_iff, EmbeddingLike.apply_eq_iff_eq,
    forall_ne_iff_not, and_congr_left_iff, and_imp]
  intro h₁ h₂
  split <;> try simp [ft'_eq_iff, ft_eq_iff]
  exact defense_translate_of_down_fCase2