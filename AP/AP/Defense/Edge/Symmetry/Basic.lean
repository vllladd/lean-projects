import AP.AP.Defense.Edge.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

@[simp] theorem vert_dir_of_hor [H : Fact e.hor] : e.dir.vert := H.1
@[simp] theorem not_hor_dir_of_hor [H : Fact e.hor] : ¬e.dir.hor := by simp
@[simp] theorem hor_dir_of_vert [H : Fact e.vert] : e.dir.hor := H.1
@[simp] theorem not_vert_dir_of_vert [H : Fact e.vert] : ¬e.dir.vert := by simp
@[simp] theorem dir_eq_of_up [H : Fact # e.dir = .up] : e.dir = .up := H.1
@[simp] theorem dir_eq_of_down [H : Fact # e.dir = .down] : e.dir = .down := H.1
@[simp] theorem hor_of_up [H : Fact # e.dir = .up] : e.hor := by simp
@[simp] theorem not_vert_of_up [H : Fact # e.dir = .up] : ¬e.vert := by simp
@[simp] theorem hor_of_down [H : Fact # e.dir = .down] : e.hor := by simp

@[simp] instance [H : Fact # e.dir = .up] : Fact # e.hor := by simp

@[simp] theorem dir_eq_or_eq_of_hor [H : Fact e.hor] : e.dir = .up ∨ e.dir = .down := by
  cases hd : e.dir <;> simp [hd] at H ⊢

theorem defense_sym_of_down_fCase2 {e : Edge} {esym : Edge → Edge} {s p} {sym : sys.Symmetry}
[Hsym : BasicSym sym]
(h₁ : ∀ {p d}, (esym e).getBorderPoints p d =
(e.getBorderPoints (sym.ft' p) d).map sym.ft)
(h₂ : ∀ {p₁ p₂}, (sym.ft p₁).dist (sym.ft p₂) = p₁.dist p₂) :
fCase2 s (sym.ft (e.getBorderPoint₀ (sym.ft' s.aPos)))
((esym e).getBorderPoints s.aPos) = some p ↔
fCase2 (sym.fs' s) (e.getBorderPoint₀ (sym.ft' s.aPos))
(e.getBorderPoints (sym.ft' s.aPos)) = some (sym.ft' p) := by
  unfold fCase2
  nth_rw 2 [sym.ft.option_eq_iff_map]
  rw [Option.map_some, System.Symmetry.ft_ft', apply_ite (f := Option.map sym.ft)]
  rw [taken_sym_of_basicSym', Option.map_some]
  
  convert_to _ ↔ (if sym.ft (e.getBorderPoint₀
    (sym.ft' s.aPos)) ∉ s.taken then
      some (sym.ft (e.getBorderPoint₀ (sym.ft' s.aPos)))
    else
      Option.map (⇑sym.ft)
        (have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
        have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2;
        have f := λ ps₁ ps₂ ↦ do
          let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑sym.ft')) ps₁
          let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) ps₂
          guard # p' ∉ s.taken.map ⇑sym.ft'
          return p'
        (f ps₁ ps₂).elim (f ps₂ ps₁) some)) =
    some p
  · simp [ft'_eq_iff]
  
  suffices h : (have ps₁ := (esym e).getBorderPoints s.aPos 1;
    have ps₂ := (esym e).getBorderPoints s.aPos 2;
    have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) ps₁
      let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) ps₂;
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (Option.map (⇑sym.ft)
      (have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
      have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2;
      have f := λ ps₁ ps₂ ↦ do
        let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑sym.ft')) ps₁
        let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) ps₂
        guard # p' ∉ s.taken.map ⇑sym.ft'
        return p'
      (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rw [h]

  iterate 2 rw [h₁]
  
  trans (have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑sym.ft')) ps₁
      let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) ps₂
      guard # p' ∉ s.taken.map sym.ft'
      return p'
    (f ps₁ ps₂ |>.map sym.ft).elim (f ps₂ ps₁ |>.map sym.ft) some)
  rotate_left
  · rw [Option.map_elim_fn_some]

  trans (have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ Option.map sym.ft # do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map ⇑sym.ft')) ps₁
      let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) ps₂
      guard # p' ∉ s.taken.map sym.ft'
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left; rfl
  
  trans (have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2;
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken.map sym.ft')) ps₁
      let p' ← Option.map sym.ft # List.find? (λ p' ↦ decide
        (Point.dist p' p ≠ 1)) ps₂
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left
  · simp [Option.bind_map]
    congr
    · ext p₁ p₂
      simp_all only [Option.bind_eq_some_iff',
      Option.guard_eq_some',
        Option.some.injEq, exists_const]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        subst right
        simp_all only [Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq_left', and_true]
        intro x a
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [System.Symmetry.ft_ft', not_true_eq_false]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        subst right
        simp_all only [Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq_left', and_true]
        apply Aesop.BuiltinRules.not_intro
        intro a
        apply left_1
        · exact a
        · simp_all only [System.Symmetry.ft'_ft]
    · ext x a : 2
      simp_all only [Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq,
      exists_const]
      apply Iff.intro
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        subst right
        simp_all only [Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq_left', and_true]
        intro x_1 a
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [System.Symmetry.ft_ft', not_true_eq_false]
      · intro a_1
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        subst right
        simp_all only [Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq_left', and_true]
        apply Aesop.BuiltinRules.not_intro
        intro a
        apply left_1
        · exact a
        · simp_all only [System.Symmetry.ft'_ft]
  
  trans ((have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (x ∈ s.taken)) # List.map (sym.ft) ps₁
      let p' ← List.find? (λ p' ↦ decide (Point.dist p' p ≠ 1)) #
        List.map (⇑sym.ft) ps₂
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · rfl
  
  trans ((have ps₁ := e.getBorderPoints (sym.ft' s.aPos) 1;
    have ps₂ := e.getBorderPoints (sym.ft' s.aPos) 2
    have f := λ ps₁ ps₂ ↦ do
      let p ← List.find? (λ x ↦ decide (sym.ft x ∈ s.taken)) ps₁
        |>.map sym.ft
      let p' ← List.find? (λ p' ↦ decide (Point.dist (sym.ft p') p ≠ 1)) ps₂
        |>.map sym.ft
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some))
  · simp only [List.find?_map, Function.comp_def', ne_eq, decide_not, Option.pure_def,
      Option.bind_eq_bind]
  
  generalize hps₁ : e.getBorderPoints (sym.ft' s.aPos) 1 = ps₁
  generalize hps₂ : e.getBorderPoints (sym.ft' s.aPos) 2 = ps₂
  
  convert_to
    (have f := fun ps₁ ps₂ ↦ do
      let p ← Option.map (⇑sym.ft) (List.find? (fun x ↦ decide
        (sym.ft x ∈ s.taken)) ps₁)
      let p' ← Option.map (⇑sym.ft) (List.find? (fun p' ↦ decide
        (Point.dist
        (sym.ft p') p ≠ 1)) ps₂);
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some) =
    (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide (x ∈ s.taken.map ⇑sym.ft')) ps₁
      let p' ← Option.map sym.ft # List.find? (fun p' ↦ decide
        (Point.dist p' p ≠ 1)) ps₂
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  
  trans (have f := fun ps₁ ps₂ ↦ do
      let p ← List.find? (fun x ↦ decide (sym.ft x ∈ s.taken)) ps₁
      let p' ← Option.map sym.ft # List.find? (fun p' ↦ decide
        (Point.dist p' p ≠ 1)) ps₂
      guard # p' ∉ s.taken
      return p'
    (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  rotate_left
  · simp [ft'_eq_iff]
  
  trans (have f := fun ps₁ ps₂ ↦ do
    let p ← (List.find? (fun x ↦ decide (sym.ft x ∈ s.taken)) ps₁)
    let p' ← Option.map sym.ft (List.find?
      (fun p' ↦ decide (Point.dist (sym.ft p')
      (sym.ft p) ≠ 1)) ps₂)
    guard # p' ∉ s.taken
    return p'
  (f ps₁ ps₂).elim (f ps₂ ps₁) some)
  · simp [Option.bind_map]
  
  simp only [h₂, ne_eq, decide_not, Option.pure_def, Option.bind_eq_bind, Option.bind_map,
    Function.comp_apply]