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
theorem getBorderPoint₀_rotRight {p} :
e.rotRight.getBorderPoint₀ p = rotRight.ft (e.getBorderPoint₀ # rotRight.ft' p) := by
  simp [Edge.rotRight, rotRight, getBorderPoint₀, getBorderPoint]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd]

@[simp]
theorem getBorderPoint_rotRight_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoint p d = rotRight.ft (e.getBorderPoint (rotRight.ft' p) d) := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

@[simp]
theorem getBorderPoints_rotRight_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoints p d = (e.getBorderPoints (rotRight.ft' p) d).map rotRight.ft := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoints, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

@[simp] theorem dir_rotRight : e.rotRight.dir = e.dir.rotRight := rfl

@[simp] theorem offset_rotRight_eq_of_hor [H : Fact e.hor] :
e.rotRight.offset = -e.offset := by simp [Edge.rotRight]

@[simp] theorem offset_rotRight_eq_of_vert [H : Fact e.vert] :
e.rotRight.offset = e.offset := by simp [Edge.rotRight]

theorem rotRight_defense_of_hor_fCase2 {e : Edge} {s : State} {p : PointZ}
[H : Fact e.hor] : fCase2 s (rotRight.ft (e.getBorderPoint₀
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
  
  iterate 2 rw [getBorderPoints_rotRight_of_hor]
  
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
  
  simp

@[simp]
theorem defense_rotRight_of_hor [H : Fact e.hor] :
e.rotRight.defense = e.defense.sym rotRight := by
  simp [defense, Defense.sym]
  ext s p :2
  simp [ft_eq_iff, f, f']
  intro h₁ h₂
  split <;> try simp [ft'_eq_iff, ft_eq_iff]
  exact rotRight_defense_of_hor_fCase2

@[simp] theorem dir_eq_or_eq_of_hor [H : Fact e.hor] : e.dir = .up ∨ e.dir = .down := by
  cases hd : e.dir <;> simp [hd] at H ⊢

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

@[simp]
theorem rotRight_rotLeft : e.rotLeft.rotRight = e := by
  cases h : e.dir <;> simp [Edge.rotRight, Edge.rotLeft, Edge.ext_iff, h]

@[simp]
theorem rotLeft_rotRight : e.rotRight.rotLeft = e := by
  cases h : e.dir <;> simp [Edge.rotRight, Edge.rotLeft, Edge.ext_iff, h]

@[simp] theorem dir_rotLeft : e.rotLeft.dir = e.dir.rotLeft := rfl

@[simp] theorem hor_of_down [H : Fact # e.dir = .down] : e.hor := by simp

-- set_option maxHeartbeats 10000000

theorem defense_translate_of_down_fCase2 {dy s p} [H : Fact # e.dir = .down] :
fCase2 s (e.getBorderPoint₀ s.aPos + ⟨0, dy⟩) ((e.translate ⟨0, dy⟩).getBorderPoints s.aPos) =
some p ↔ fCase2 ((translate ⟨0, dy⟩).fs' s) (e.getBorderPoint₀ ((translate ⟨0, dy⟩).ft' s.aPos))
(e.getBorderPoints ((translate ⟨0, dy⟩).ft' s.aPos)) = some ((translate ⟨0, dy⟩).ft' p) := by
  unfold fCase2
  sorry

-- #check 0 #exit

theorem defense_translate_of_down {dy} [H : Fact # e.dir = .down] :
(e.translate ⟨0, dy⟩).defense = e.defense.sym (translate ⟨0, dy⟩) := by
  simp [defense, Defense.sym, dist]; ring_nf; simp
  ext s p :2
  simp [ft_eq_iff, f, f']
  intro h₁ h₂
  split
  
  all_goals
    nm x h₃; clear x
    conv_rhs => rw [Equiv.option_eq_iff_map (e := translate ⟨0, dy⟩ |>.ft)]
    simp [translate, getBorderPoint₀, getBorderPoint, getBorderPoints, Point.ext_iff]
    try simp [Point.forall_iff, Point.exi_iff, sub_eq_iff_eq_add, add_eq_iff_eq_sub]
  
  ·
    simp_all only [dir_eq_of_down, instFactTrue_aP, Int.reduceNeg]
    apply Iff.intro
    · intro a
      cases a with
      | inl
        h =>
        simp_all only [sub_add_cancel, and_self, and_true, Int.reduceNeg, left_eq_add,
          one_ne_zero, and_false, false_or, false_and, or_false]
        intro x y a a_1
        subst a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only [sub_add_cancel, not_false_eq_true]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [not_true_eq_false]
      | inr h_1 =>
        simp_all only [Int.reduceNeg, true_and]
        obtain ⟨left, right⟩ := h_1
        cases right with
        | inl
          h =>
          simp_all only [sub_add_cancel, Int.reduceNeg, add_eq_left, one_ne_zero, and_true,
            and_false, add_neg_cancel_right, and_self, false_and, or_false, false_or]
          intro x y a a_1
          subst a_1
          obtain ⟨left_1, right⟩ := h
          obtain ⟨left_2, right⟩ := right
          simp_all only [Int.reduceNeg, add_neg_cancel_right, sub_add_cancel, not_false_eq_true]
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
        | inr
          h_1 =>
          simp_all only [sub_add_cancel, Int.reduceNeg, sub_eq_self, one_ne_zero, and_true,
            and_false, and_self, false_or]
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_false_eq_true, true_and]
          apply Or.inr
          intro x y a a_1
          subst a_1
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
    · intro a
      cases a with
      | inl h =>
        simp_all only [sub_add_cancel, not_false_eq_true, and_self, Int.reduceNeg, left_eq_add,
          one_ne_zero, and_true, and_false, false_or, false_and, or_false]
      | inr h_1 =>
        simp_all only [Int.reduceNeg, not_true_eq_false, false_and, true_and, false_or]
        obtain ⟨left, right⟩ := h_1
        cases right with
        | inl h =>
          simp_all only [sub_add_cancel, Int.reduceNeg, add_neg_cancel_right, not_false_eq_true,
            and_self, and_true, false_and, or_false]
        | inr h_1 =>
          simp_all only [sub_add_cancel, Int.reduceNeg, and_true, not_false_eq_true, and_self]
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_true_eq_false, false_and, or_true]
  
  · simp_all only [dir_eq_of_down, instFactTrue_aP, Int.reduceNeg]
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        cases h with
        | inl
          h_1 =>
          simp_all only [Int.reduceNeg, add_neg_cancel_right, sub_add_cancel, and_self, and_true,
            false_and, or_false, add_eq_left, one_ne_zero, and_false]
          intro x y a a_1
          subst a_1
          obtain ⟨left, right⟩ := h_1
          obtain ⟨left_1, right⟩ := right
          simp_all only [Int.reduceNeg, add_neg_cancel_right, sub_add_cancel, not_false_eq_true]
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
        | inr
          h_2 =>
          simp_all only [Int.reduceNeg, sub_add_cancel, and_true, and_self, sub_eq_self,
            one_ne_zero, and_false, or_false]
          obtain ⟨left, right⟩ := h_2
          obtain ⟨left_1, right⟩ := right
          obtain ⟨left_2, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_false_eq_true, true_and]
          apply Or.inr
          intro x y a a_1
          subst a_1
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
      | inr
        h_1 =>
        simp_all only [Int.reduceNeg, sub_add_cancel, left_eq_add, one_ne_zero, and_true,
          and_false, false_or, implies_true, and_self, true_and]
        obtain ⟨left, right⟩ := h_1
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right⟩ := right
        simp_all only [Int.reduceNeg, sub_add_cancel, not_false_eq_true]
        apply Or.inr
        intro x y a a_1
        subst a_1
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [not_true_eq_false]
    · intro a
      cases a with
      | inl h =>
        cases h with
        | inl h_1 =>
          simp_all only [Int.reduceNeg, add_neg_cancel_right, sub_add_cancel, not_false_eq_true,
            and_self, and_true, false_and, or_false, add_eq_left, one_ne_zero, and_false]
        | inr
          h_2 =>
          simp_all only [Int.reduceNeg, sub_add_cancel, and_true, not_false_eq_true, and_self,
            sub_eq_self, one_ne_zero, and_false, or_false]
          obtain ⟨left, right⟩ := h_2
          obtain ⟨left_1, right⟩ := right
          obtain ⟨left_2, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_true_eq_false, false_and, or_true]
      | inr h_1 =>
        simp_all only [Int.reduceNeg, sub_add_cancel, left_eq_add, one_ne_zero, and_true,
          and_false, false_or, implies_true, not_false_eq_true, and_self, or_true]
  
  · sorry
  
  · simp_all only [dir_eq_of_down, instFactTrue_aP, Int.reduceNeg]
    apply Iff.intro
    · intro a
      cases a with
      | inl
        h =>
        simp_all only [sub_add_cancel, and_self, and_true, Int.reduceNeg, left_eq_add, one_ne_zero,
          and_false, false_or, false_and, or_false]
        intro x y a a_1
        subst a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only [sub_add_cancel, not_false_eq_true]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        subst a_1
        simp_all only [not_true_eq_false]
      | inr h_1 =>
        simp_all only [Int.reduceNeg, true_and]
        obtain ⟨left, right⟩ := h_1
        cases right with
        | inl
          h =>
          simp_all only [sub_add_cancel, Int.reduceNeg, add_eq_left, one_ne_zero, and_true,
            and_false, add_neg_cancel_right, and_self, false_and, or_false, false_or]
          intro x y a a_1
          subst a_1
          obtain ⟨left_1, right⟩ := h
          obtain ⟨left_2, right⟩ := right
          simp_all only [Int.reduceNeg, add_neg_cancel_right, sub_add_cancel, not_false_eq_true]
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
        | inr
          h_1 =>
          simp_all only [sub_add_cancel, Int.reduceNeg, sub_eq_self, one_ne_zero, and_true,
            and_false, and_self, false_or]
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_false_eq_true, true_and]
          apply Or.inr
          intro x y a a_1
          subst a_1
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
    · intro a
      cases a with
      | inl h =>
        simp_all only [sub_add_cancel, not_false_eq_true, and_self, Int.reduceNeg, left_eq_add,
          one_ne_zero, and_true, and_false, false_or, false_and, or_false]
      | inr h_1 =>
        simp_all only [Int.reduceNeg, not_true_eq_false, false_and, true_and, false_or]
        obtain ⟨left, right⟩ := h_1
        cases right with
        | inl h =>
          simp_all only [sub_add_cancel, Int.reduceNeg, add_neg_cancel_right, not_false_eq_true,
            and_self, and_true, false_and, or_false]
        | inr h_1 =>
          simp_all only [sub_add_cancel, Int.reduceNeg, and_true, not_false_eq_true, and_self]
          obtain ⟨left_1, right⟩ := h_1
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right⟩ := right
          simp_all only [Int.reduceNeg, sub_add_cancel, not_true_eq_false, false_and, or_true]

-- #check 0 #exit

theorem defense_flipV_of_up [H : Fact # e.dir = .up] :
e.flipV.defense = e.defense.sym rot180 := by
  simp [defense, Defense.sym, dist, neg_sub_comm]
  ext s p :2
  simp [ft_eq_iff, f, f']
  intro h₁ h₂
  split
  all_goals
    nm x h₃; clear x
    conv_rhs => rw [Equiv.option_eq_iff_map (e := rot180.ft)]
  · simp
  · sorry
  · sorry
  · sorry
  · sorry
  · simp