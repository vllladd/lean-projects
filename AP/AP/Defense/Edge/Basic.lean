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

theorem of_eq_some {s p} (h : e.defense.f s = some p) :
0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧ p ∉ s.taken ∧
∃ (z : ℤ), |z| ≤ 3 ∧ e.getBorderPoint s.aPos z = p := by
  simp [defense, f] at h
  rcases h with ⟨h₁, h₂, h₃⟩
  simp [h₃]
  simp [f₁] at h₁
  obtain ⟨n, h₁, h₄⟩ := h₁
  simp [f₂, f₃] at h₁
  obtain ⟨h₁, h₅⟩ := h₁
  generalize hf : (λ (i : ℕ) => (e.ptsArr s (-3) 7)[i]?.getD false) = f at h₁ h₅
  replace h₁ := mem_cndMp_of_cnd_eq_false h₁
  simp at h₁
  split_ands
  · omega
  · omega
  · use (n - 3 : ℤ)
    simp [h₄]
    simp [f₄] at h₅
    rw [abs_le]
    simp
    rw [←h₅]
    delta Option.getD
    split; rotate_left; norm_num
    nm x k h; clear x
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨-, i, hi, rfl, -⟩ := h
    simp at hi ⊢
    omega

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