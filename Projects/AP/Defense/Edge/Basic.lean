import Projects.AP.Defense.Edge.Defs

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

@[simp]
theorem getBorderPoint_inj {p z₁ z₂} :
e.getBorderPoint p z₁ = e.getBorderPoint p z₂ ↔ z₁ = z₂ := by
  cases h : e.dir <;> simp [getBorderPoint, h]

theorem mem_cndMp_of_cnd_eq_false {d f} (h : cnd d f = false) : d ∈ cndMp := by
  rw [cnd] at h
  split at h; simp at h
  nm x xs h₁; clear x
  rw [Map.mem_iff_get?_eq_some]
  use xs

theorem cndMp_keys : cndMp.keys = [1, 2, 3, 4, 5] := by
  native_decide

@[simp]
theorem mem_cndMp_iff {d} : d ∈ cndMp ↔ 1 ≤ d ∧ d ≤ 5 := by
  simp [Map.mem_iff_mem_keys, cndMp_keys]; omega

theorem f₅_le_6_of {g m} (h : ∀ n, m = some n → n ≤ 6) : f₅ g m ≤ 6 := by
  simp [f₅]; split
  · nm x k; clear x
    simp at h
    exact h
  nm x; clear x
  simp [Option.getD]
  split; rotate_left; norm_num
  nm x k h₁; clear x
  simp at h₁
  omega

@[simp]
theorem f₄_le_6 {d g} : f₄ d g ≤ 6 := by
  rw [f₄]
  apply f₅_le_6_of
  intro k h₂
  simp at h₂
  omega

theorem of_f₁_eq_some {s p} (h : e.f₁ s = some p) :
0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧
∃ (z : ℤ), |z| ≤ 3 ∧ e.getBorderPoint s.aPos z = p := by
  simp [f₁] at h
  obtain ⟨n, h₁, h₄⟩ := h
  simp [f₂, f₃] at h₁
  obtain ⟨⟨-, h₁⟩, h₅⟩ := h₁
  generalize hf : (λ (i : ℕ) => (e.ptsArr s (-3) 7)[i]?.getD false) = f at h₁ h₅
  replace h₁ := mem_cndMp_of_cnd_eq_false h₁
  simp at h₁
  split_ands; iterate 2 omega
  use (n - 3 : ℤ)
  simp [h₄]
  rw [abs_le]
  simp [←h₅]

theorem of_f_eq_some {s p} (h : e.defense.f s = some p) :
0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧ p ∉ s.taken ∧
∃ (z : ℤ), |z| ≤ 3 ∧ e.getBorderPoint s.aPos z = p := by
  simp [defense, f] at h; obtain ⟨h₁, h₂, h₃⟩ := h; have := of_f₁_eq_some h₁; tauto

theorem dist_eq_zero_of_f_eq_some {s p} (h : e.defense.f s = some p) : e.dist p = 0 := by
  obtain ⟨-, h₁, h₂, z, h₃, rfl⟩ := of_f_eq_some h; simp [getBorderPoint] at h₂ ⊢
  simp [dist]; cases hd : e.dir <;> simp [hd] at h₂ ⊢

theorem not_mem_taken_of_f_eq_some {s p} (h : e.defense.f s = some p) : p ∉ s.taken := by
  obtain ⟨-, h₁, h₂, z, h₃, h₄⟩ := of_f_eq_some h; exact h₂

@[simp]
theorem validTr_defense : e.defense.ValidTr := by
  intro s hs p h
  replace h := of_f_eq_some h
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

theorem cnd_congr {d f₁ f₂} (h : ∀ i < 7, f₁ i = f₂ i) : cnd d f₁ = cnd d f₂ := by
  simp [cnd]
  split; rfl
  nm x xs h₁; clear x
  congr
  ext bs
  simp
  apply forall_congr'
  rintro ⟨i, hi⟩
  simp [h i hi]

@[simp] theorem get?_6_cndMp : cndMp.get? 6 = none := by simp

@[simp]
theorem get?_1_cndMp : cndMp.get? 1 = some
[#[false, false, true, true, true, false, false]] := by
  native_decide

theorem f₁_eq_of_f_eq_some {s p} (h : e.f s = some p) : e.f₁ s = some p := by
  simp [f] at h; exact h.1

theorem of_f₃_eq_some {d g k} (h : f₃ d g = some k) : 1 ≤ d ∧ d ≤ 6 ∧ k ≤ 6 := by
  simp [f₃] at h
  use by omega, by omega
  simp [←h.2]

theorem of_f₂_eq_some {d arr offset k} (h : f₂ d arr offset = some k) :
1 ≤ d ∧ d ≤ 6 ∧ k ≤ 6 := of_f₃_eq_some h

@[simp]
theorem cnd_const_true {d} : cnd d (λ _ => true) := by
  simp [cnd]; split; rfl
  nm x xs h; clear x
  have h₁ := Map.mem_of_get?_eq_some h
  simp at h₁
  generalize hn : (⟨(d - 1).toNat, by omega⟩ : Fin 5) = n
  replace hn : d = n.1 + 1
  · simp [←hn]; omega
  subst hn
  clear h₁
  replace h := congrArg (·.getD []) h
  simp at h
  subst h
  revert n
  native_decide

theorem f_eq_none_of_6_le_dist {s : State}
(h : 6 ≤ e.dist s.aPos) : e.f s = none := by
  by_contra! h₁
  rw [Option.ne_none_iff_exists'] at h₁
  choose p h₁ using h₁
  replace h₁ := of_f_eq_some h₁
  grind

theorem f_defense_eq_none_of_6_le_dist {s : State}
(h : 6 ≤ e.dist s.aPos) : e.defense.f s = none :=
  f_eq_none_of_6_le_dist h