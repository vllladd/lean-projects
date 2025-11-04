import AP.AP.Defense.Edge.Defs

namespace AP.Edge

variable {e e₁ e₂ : Edge}

theorem mem_points_iff_memPoints {p} : p ∈ e.points ↔ e.memPoints p := by rfl

instance {p} : Decidable # p ∈ e.points :=
  match h : e.memPoints p with
  | true => .isTrue # by simp [mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [mem_points_iff_memPoints, h]

theorem memPoints_eq {p} : e.memPoints p = decide (p ∈ e.points) := by
  simp [mem_points_iff_memPoints]

theorem points_inj (h : e₁.points = e₂.points) : e₁ = e₂ := by
  rw [Set.ext_iff] at h; rcases e₁, e₂ with ⟨⟨d₁, n₁⟩, ⟨d₂, n₂⟩⟩; simp
  cases d₁ <;> cases d₂ <;> simp <;> simp [points, memPoints] at h <;> exact h

@[simp]
theorem points_eq_points_iff : e₁.points = e₂.points ↔ e₁ = e₂ :=
  ⟨points_inj, λ h => by rw [h]⟩

@[simp] theorem ps_defense : e.defense.ps = e.points := rfl

theorem of_eq_some_fCase2 {e : Edge} {s : State} {p : PointZ} (h₁ : e.dist s.aPos = 2)
(h₂ : fCase2 s (e.getBorderPoint s.aPos 0) (e.getBorderPoints s.aPos) = some p ∧
¬p = s.aPos ∧ p ∉ s.taken) : 0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧ p ∉ s.taken ∧
∃ z, |z| ≤ 2 ∧ e.getBorderPoint s.aPos z = p := by
  unfold fCase2 at h₂
  simp [getBorderPoints, List.find?_cons] at h₂ ⊢
  rename' h₂ => h
  revert h₁; intro _
  simp_all only [Nat.ofNat_pos, Int.reduceLE, not_false_eq_true, true_and]
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right⟩ := right
  split at left
  rename_i h
  split at left
  rename_i x_1 heq_1
  split at left
  rename_i x_2 heq_2
  simp_all only [Int.reduceNeg, decide_eq_true_eq, decide_true, Bool.not_true,
    Bool.false_and, Option.bind_some]
  split at left
  rename_i x_3 heq_3
  split at left
  rename_i x_4 heq_4
  simp_all only [Int.reduceNeg, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Option.elim_some, Option.some.injEq, not_false_eq_true, true_and]
  subst left
  obtain ⟨left, right_1⟩ := heq_4
  apply Exists.intro
  apply And.intro
  on_goal 8 => rename_i h
  on_goal 7 => rename_i x_1 heq_1
  on_goal 6 => rename_i x_2 heq_2
  on_goal 6 => split at left
  on_goal 6 => rename_i x_3 heq_3
  on_goal 7 => rename_i x_3 heq_3
  on_goal 8 => split at left
  on_goal 8 => rename_i x_2 heq_2
  on_goal 9 => rename_i x_2 heq_2
  on_goal 8 => split at left
  on_goal 8 => rename_i x_3 heq_3
  on_goal 9 => rename_i x_3 heq_3
  on_goal 9 => split at left
  on_goal 9 => rename_i x_4 heq_4
  on_goal 10 => rename_i x_4 heq_4
  on_goal 11 => split at left
  on_goal 11 => rename_i x_3 heq_3
  on_goal 12 => rename_i x_3 heq_3
  on_goal 12 => split at left
  on_goal 12 => rename_i x_4 heq_4
  on_goal 13 => rename_i x_4 heq_4
  on_goal 5 => rename_i x_3 heq_3
  on_goal 4 => rename_i x_4 heq_4
  on_goal 5 => split at left
  on_goal 5 => rename_i x_4 heq_4
  on_goal 6 => rename_i x_4 heq_4
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.and_eq_false_imp, Bool.not_false, decide_eq_true_eq,
    Option.elim_some, Option.some.injEq, not_false_eq_true, true_and]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.not_false, decide_eq_true_eq, Bool.and_eq_true,
      Option.elim_none, Option.some.injEq, not_false_eq_true, true_and]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.not_false, decide_eq_true_eq, Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_true_eq, decide_eq_false_iff_not, decide_false,
    Bool.not_false, Bool.true_and, decide_true, Bool.not_true, Bool.false_and, Option.bind_some]
  split at left
  rename_i x_4 heq_4
  split at left
  rename_i x_5 heq_5
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.and_eq_true, Option.elim_some, Option.some.injEq, not_false_eq_true]
  subst left
  obtain ⟨left, right_1⟩ := heq_5
  apply Exists.intro
  apply And.intro
  on_goal 5 => rename_i x_4 heq_4
  on_goal 4 => rename_i x_5 heq_5
  on_goal 5 => split at left
  on_goal 5 => rename_i x_5 heq_5
  on_goal 6 => rename_i x_5 heq_5
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.and_eq_false_imp, Bool.not_false, decide_eq_true_eq, Option.elim_some,
    Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.and_eq_true, Bool.not_true, decide_eq_false_iff_not, Option.elim_none,
    Option.some.injEq, not_false_eq_true, true_and]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.and_eq_false_imp, Bool.not_true, decide_eq_false_iff_not, Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_true_eq, decide_eq_false_iff_not, decide_false,
    Bool.not_false, Bool.true_and, Option.bind_some, decide_true, Bool.not_true,
    Bool.false_and, Option.bind_none]
  split at left
  rename_i x_4 heq_4
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Option.elim_some, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 4 => rename_i x_4 heq_4
  on_goal 4 => split at left
  on_goal 4 => rename_i x_5 heq_5
  on_goal 5 => rename_i x_5 heq_5
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.not_true, decide_eq_false_iff_not, Option.elim_some, Option.some.injEq,
    not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_eq_true_eq, decide_true,
    Bool.not_true, Bool.false_and, Option.bind_some, decide_false, Bool.not_false, Bool.true_and]
  split at left
  rename_i x_4 heq_4
  split at left
  rename_i x_5 heq_5
  simp_all only [Int.reduceNeg, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Option.elim_some, Option.some.injEq, not_false_eq_true, true_and]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 5 => rename_i x_4 heq_4
  on_goal 4 => rename_i x_5 heq_5
  on_goal 5 => split at left
  on_goal 5 => rename_i x_5 heq_5
  on_goal 6 => rename_i x_5 heq_5
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.not_false, decide_eq_true_eq, Option.elim_some,
    Option.some.injEq, not_false_eq_true, true_and]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.not_false, decide_eq_true_eq, Option.elim_none,
    Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.not_false, decide_eq_true_eq, Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_eq_true_eq, decide_false,
    Bool.not_false, Bool.true_and, decide_true, Bool.not_true, Bool.false_and, Option.bind_some]
  split at left
  rename_i x_5 heq_5
  split at left
  rename_i x_6 heq_6
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Option.elim_some, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 5 => rename_i x_5 heq_5
  on_goal 4 => rename_i x_6 heq_6
  on_goal 5 => split at left
  on_goal 5 => rename_i x_6 heq_6
  on_goal 6 => rename_i x_6 heq_6
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Bool.not_false, decide_eq_true_eq, Option.elim_some, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.not_true, decide_eq_false_iff_not, Option.elim_none, Option.some.injEq,
    not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_eq_true_eq, decide_false,
    Bool.not_false, Bool.true_and, Option.bind_some, decide_true, Bool.not_true,
    Bool.false_and, Option.bind_none]
  split at left
  rename_i x_5 heq_5
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Option.elim_some, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 4 => rename_i x_5 heq_5
  on_goal 4 => split at left
  on_goal 4 => rename_i x_6 heq_6
  on_goal 5 => rename_i x_6 heq_6
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.not_true, decide_eq_false_iff_not, Option.elim_some, Option.some.injEq,
    not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, Nat.abs_ofNat, le_refl]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Option.elim_none, reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_eq_true_eq, decide_true,
    Bool.not_true, Bool.false_and, Option.bind_none, decide_false, Bool.not_false,
    Bool.true_and, Option.bind_some, Option.elim_none]
  split at left
  rename_i x_4 heq_4
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 4 => rename_i x_4 heq_4
  on_goal 4 => split at left
  on_goal 4 => rename_i x_5 heq_5
  on_goal 5 => rename_i x_5 heq_5
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.not_true, decide_eq_false_iff_not, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_eq_true_eq, decide_false,
    Bool.not_false, Bool.true_and, decide_true, Bool.not_true, Bool.false_and,
    Option.bind_none, Option.bind_some, Option.elim_none]
  split at left
  rename_i x_5 heq_5
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  apply And.intro
  on_goal 4 => rename_i x_5 heq_5
  on_goal 4 => split at left
  on_goal 4 => rename_i x_6 heq_6
  on_goal 5 => rename_i x_6 heq_6
  on_goal 2 => {rfl}
  · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    Bool.not_true, decide_eq_false_iff_not, Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
  simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
    reduceCtorEq]
  simp_all only [Int.reduceNeg, decide_eq_false_iff_not, decide_false, Bool.not_false,
    Bool.true_and, Option.bind_none, Option.elim_none, reduceCtorEq]
  simp_all only [Option.some.injEq, not_false_eq_true]
  subst left
  apply Exists.intro
  · apply And.intro
    on_goal 2 => {rfl}
    · simp_all only [abs_zero, Nat.ofNat_nonneg]

theorem of_eq_some {s p} (h : e.defense.f s = some p) :
0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧ p ∉ s.taken ∧
∃ (z : ℤ), |z| ≤ 2 ∧ e.getBorderPoint s.aPos z = p := by
  simp [defense, f, f', getBorderPoints, getBorderPoint₀, List.find?_cons] at h
  split at h
  · simp_all only [Option.some.injEq, Nat.ofNat_pos, le_refl, not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      simp_all only [abs_zero, Nat.ofNat_nonneg]
  · simp_all only [Int.reduceNeg, Nat.ofNat_pos, Int.reduceLE, not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split at left
    rename_i x_1 heq_1
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Option.some.injEq, not_false_eq_true]
    subst left
    apply Exists.intro
    apply And.intro
    on_goal 4 => rename_i x_1 heq_1
    on_goal 4 => split at left
    on_goal 4 => rename_i x_2 heq_2
    on_goal 5 => rename_i x_2 heq_2
    on_goal 5 => split at left
    on_goal 5 => rename_i x_3 heq_3
    on_goal 6 => rename_i x_3 heq_3
    on_goal 2 => {rfl}
    · simp_all only [abs_zero, Nat.ofNat_nonneg]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
      Int.reduceNeg, Bool.not_true, decide_eq_false_iff_not, Option.some.injEq,
      not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
      Int.reduceNeg, Bool.not_true, decide_eq_false_iff_not, Option.some.injEq,
      not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
      Int.reduceNeg, reduceCtorEq]
  · simp_all only [Int.reduceNeg, Nat.ofNat_pos, Int.reduceLE, not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split at left
    rename_i x_1 heq_1
    simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Option.some.injEq, not_false_eq_true]
    subst left
    apply Exists.intro
    apply And.intro
    on_goal 4 => rename_i x_1 heq_1
    on_goal 4 => split at left
    on_goal 4 => rename_i x_2 heq_2
    on_goal 5 => rename_i x_2 heq_2
    on_goal 5 => split at left
    on_goal 5 => rename_i x_3 heq_3
    on_goal 6 => rename_i x_3 heq_3
    on_goal 2 => {rfl}
    · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
    simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq, Bool.not_true, decide_eq_false_iff_not, Option.some.injEq,
      not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
    simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq, Bool.not_true, decide_eq_false_iff_not, Option.some.injEq,
      not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_zero, Nat.ofNat_nonneg]
    simp_all only [Int.reduceNeg, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq, reduceCtorEq]
  · nm x h₁; exact of_eq_some_fCase2 h₁ h
  · simp_all only [Int.reduceNeg, zero_lt_one, Nat.one_le_ofNat, not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split at left
    rename_i x_1 heq_1
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Option.some.injEq, not_false_eq_true]
    subst left
    apply Exists.intro
    apply And.intro
    on_goal 4 => rename_i x_1 heq_1
    on_goal 4 => split at left
    on_goal 4 => rename_i x_2 heq_2
    on_goal 5 => rename_i x_2 heq_2
    on_goal 5 => split at left
    on_goal 5 => rename_i x_3 heq_3
    on_goal 6 => rename_i x_3 heq_3
    on_goal 2 => {rfl}
    · simp_all only [abs_zero, Nat.ofNat_nonneg]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, Int.reduceNeg,
      Bool.not_true, decide_eq_false_iff_not, Option.some.injEq, not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_neg, abs_one, Nat.one_le_ofNat]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, Int.reduceNeg,
      Bool.not_true, decide_eq_false_iff_not, Option.some.injEq, not_false_eq_true]
    subst left
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only [Int.reduceNeg, abs_one, Nat.one_le_ofNat]
    simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
      Int.reduceNeg, reduceCtorEq]
  · simp_all only [imp_false, reduceCtorEq, false_and]

theorem dist_eq_zero_of_eq_some {s p} (h : e.defense.f s = some p) : e.dist p = 0 := by
  obtain ⟨-, h₁, h₂, z, h₃, rfl⟩ := of_eq_some h; simp [getBorderPoint] at h₂ ⊢
  simp [dist]; cases hd : e.dir <;> simp [hd] at h₂ ⊢

theorem not_mem_taken_of_eq_some {s p} (h : e.defense.f s = some p) : p ∉ s.taken := by
  obtain ⟨-, h₁, h₂, z, h₃, h₄⟩ := of_eq_some h; exact h₂

@[simp]
theorem validTr_defense : e.defense.ValidTr := by
  intro s hs p h
  replace h := of_eq_some h
  simp [getBorderPoint, dist] at h
  cases hd : e.dir
  all_goals
    obtain ⟨h₁, h₂, h₃, z, h₄, rfl⟩ := h
    simp [hd] at h₁ h₂ h₃ ⊢
    simp [DState.validTr_iff]
    refine ⟨?_, h₃⟩
    simp [Point.ext_iff]
  · rintro rfl
    simp_all only [abs_zero, Nat.ofNat_nonneg]
    apply Aesop.BuiltinRules.not_intro
    intro a; simp_all only [lt_self_iff_false]
  · intro a; simp_all only [lt_self_iff_false]
  · intro a; simp_all only [lt_self_iff_false]
  · rintro rfl
    simp_all only [abs_zero, Nat.ofNat_nonneg, add_zero]
    apply Aesop.BuiltinRules.not_intro
    intro a; simp_all only [lt_self_iff_false]

@[simp] theorem dir_edge₀ : edge₀.dir = .down := rfl
@[simp] theorem offset_edge₀ : edge₀.offset = 0 := rfl
@[simp] theorem dist_edge₀ {p} : edge₀.dist p = -p.y := by simp [dist]