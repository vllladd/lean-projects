import Projects.AP.Defense.Edge.Symmetry

namespace AP.Edge

def cnd₀ (s : State) : Prop :=
  s.aPos.y < 0 ∧
    let arr := edge₀.ptsArr s (-3) 7
    cnd (-s.aPos.y) # λ i => arr[i]?.getD false

def cnd₁ (d : ℤ) (arr : Array Bool) (offset : ℕ) : Prop :=
  0 < d ∧ cnd d (λ i => arr[offset + i]?.getD false)

def aMove₀' (m : Fin 8) : PointZ :=
  match m with
  | 0 => ⟨-1, -1⟩
  | 1 => ⟨0, -1⟩
  | 2 => ⟨1, -1⟩
  | 3 => ⟨-1, 0⟩
  | 4 => ⟨1, 0⟩
  | 5 => ⟨-1, 1⟩
  | 6 => ⟨0, 1⟩
  | 7 => ⟨1, 1⟩

def aMove₀ (p : PointZ) (m : Fin 8) : PointZ :=
  p + aMove₀' m

-----

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

instance {s} : Decidable # cnd₀ s := by
  unfold cnd₀; infer_instance

instance {d arr offset} : Decidable # cnd₁ d arr offset := by
  unfold cnd₁; infer_instance

@[simp]
theorem size_ptsArr {s offset n} : (edge₀.ptsArr s offset n).size = n := by
  simp [ptsArr]

theorem cnd₀_iff_f₁_edge₀_eq_none_of_neg_aPos_y {s} (h : s.aPos.y < 0)
: cnd₀ s ↔ edge₀.f₁ s = none := by
  simp only [cnd₀, h, Int.reduceNeg, true_and, f₁, f₂, f₃, dist_edge₀, zero_add, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_none_iff, Option.ite_none_left_eq_some, Bool.not_eq_true,
    Option.some.injEq, reduceCtorEq, imp_false, not_and, forall_apply_eq_imp_iff, Bool.not_eq_false]
  simp_all only [Int.reduceNeg, Left.neg_nonpos_iff, Bool.or_eq_true, decide_eq_true_eq,
    iff_or_self]
  rintro (h₁ | h₁); omega
  simp [cnd]
  split; rfl
  nm x xs h₂; clear x
  replace h₂ := Map.mem_of_get?_eq_some h₂
  simp at h₂
  omega

theorem neg_aPos_y_of_cnd₀ (h : cnd₀ s) : s.aPos.y < 0 := h.1

theorem cnd₀_of_aPos_y_le_neg_6 (h : s.aPos.y ≤ -6) : cnd₀ s := by
  simp [cnd₀, cnd]
  split <;> simp; omega
  nm x xs h₁; clear x
  replace h₁ := Map.mem_of_get?_eq_some h₁
  simp at h₁; omega

theorem cnd₀_iff_cnd₁ {s} : cnd₀ s ↔ cnd₁ (-s.aPos.y) (edge₀.ptsArr s (-3) 7) 0 := by
  simp only [cnd₀, Int.reduceNeg, cnd₁, Int.neg_pos, zero_add]

theorem cnd₁_iff_cnd₁_extract {arr : Array Bool} {offset d} :
cnd₁ d arr offset ↔ cnd₁ d (arr.extract offset # offset + 7) 0 := by
  simp only [cnd₁, zero_add, and_congr_right_iff, Bool.coe_iff_coe]
  intro h
  apply cnd_congr
  intro k hk
  rw [Array.getElem?_extract_add hk]

theorem cnd₁_iff_cnd₁_append {arr : Array Bool} {offset d n} :
cnd₁ d arr offset ↔ cnd₁ d ⟨arr.1 ++ List.replicate n false⟩ offset := by
  rcases arr with ⟨xs⟩
  simp only [cnd₁, List.getElem?_toArray, List.getD_getElem?_append_replicate]

theorem cnd₁_iff_cnd₁_min_6 {arr : Array Bool} {offset d} :
cnd₁ d arr offset ↔ cnd₁ (min 6 d) arr offset := by
  simp [cnd₁]
  intro h
  rw [min_eq_ite]
  split_ifs with h₁
  rotate_left; rfl
  simp [cnd]
  split; rfl
  nm x xs h₃; clear x
  replace h₃ := Map.mem_of_get?_eq_some h₃
  simp at h₃
  omega

@[simp]
theorem ptsArr_eq_empty_iff {s z n} : e.ptsArr s z n = #[] ↔ n = 0 := by
  simp [ptsArr]

@[simp]
theorem ptsArr_zero {s z} : e.ptsArr s z 0 = #[] := rfl

theorem getBorderPoint_add {p n m} :
edge₀.getBorderPoint p (n + m) = edge₀.getBorderPoint p n + ⟨m, 0⟩ := by
  simp [getBorderPoint, add_assoc]

@[simp]
theorem extract_ptsArr {s z n i j} :
(edge₀.ptsArr s z n).extract i j = edge₀.ptsArr s (z + i) (min n j - i) := by
  rw [←Nat.sub_min_sub_right]
  by_cases h : j < i
  · rw [Array.extract_eq_empty_of_le # by omega]
    simp
    omega
  push_neg at h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  by_cases h : n < i
  · rw [show n - i = 0 by omega]
    simp; omega
  push_neg at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp
  by_cases h : n < j
  · rw [min_eq_left_of_lt h]
    simp [ptsArr, add_assoc]
    simp [List.range_add]
    omega
  push_neg at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp [ptsArr, add_assoc]
  simp [List.range_add]

theorem exi_aMove₀_of_dist_eq_one {p p' : PointZ} (h : p'.dist p = 1) :
∃ (m : Fin 8), aMove₀ p m = p' := by
  rcases p, p' with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  simp [Point.dist] at h
  simp_rw [max_eq_ite, abs_eq_ite] at h
  unfold aMove₀ aMove₀'
  split_ifs at h <;> nm h₁ h₂ h₃ <;> simp at *
  · by_cases h₄ : y' = y
    · use 4; simp; omega
    · use 7; simp; omega
  · use 6; simp; omega
  · by_cases h₄ : y' = y
    · use 3; simp; omega
    · use 5; simp; omega
  · use 5; simp; omega
  · use 2; simp; omega
  · use 1; simp; omega
  · use 0; simp; omega
  · omega

include hpw in
theorem exi_aMove₀_of_tr_eq_some {s' p} [hs : AState s]
(h : sys.tr s p = some s') : ∃ (m : Fin 8), aMove₀ s.aPos m = p := by
  rw [hs.tr_eq_some_iff] at h
  obtain ⟨⟨h₁, h₂, h₃⟩, rfl⟩ := h
  simp [hpw.1, ne_symm' h₁] at h₃
  exact exi_aMove₀_of_dist_eq_one h₃

theorem aMove₀_dist_eq_one (p m) : (aMove₀ p m).dist p = 1 := by
  unfold aMove₀ aMove₀'; split <;> simp [Point.dist]

@[simp]
theorem le_one_add_aMove₀_x {p m} : p.x ≤ 1 + (aMove₀ p m).x := by
  unfold aMove₀ aMove₀'; split <;> simp <;> omega

@[simp]
theorem one_add_aMove₀_le_two_add_x {p m} : 1 + (aMove₀ p m).x ≤ 2 + p.x := by
  unfold aMove₀ aMove₀'; split <;> simp <;> omega

@[simp]
theorem f₄_lt_7 {d f} : f₄ d f < 7 := by
  suffices : f₄ d f ≤ 6; omega; simp

theorem ptsArr_eq_of_taken_eq {s s' : State} {z n} (h : s'.taken = s.taken) :
edge₀.ptsArr s' z n = edge₀.ptsArr s (z + s'.aPos.x - s.aPos.x) n := by
  unfold ptsArr
  simp only [h, getBorderPoint, dir_edge₀, instFactTrue_aP, dir_eq_of_down, offset_edge₀,
    List.pure_def, List.bind_eq_flatMap, List.flatMap_fn_singleton, List.map_map,
    Function.comp_def, Array.mk.injEq, List.map_inj_left, List.mem_range, decide_eq_decide]
  ring_nf; simp

theorem ptsArr_eq_of_aPos_eq_and_taken_eq_insert.proof₁ {s s' : State} {p}
(h₁ : s'.taken = s.taken.insert p)
(h₃ : ∃ (z : ℤ), |z| ≤ 3 ∧ edge₀.getBorderPoint s.aPos z = p) :
(p.x - s.aPos.x + 3).toNat < (edge₀.ptsArr s (-3) 7).size := by
  obtain ⟨z, h₃, h₄⟩ := h₃
  simp [getBorderPoint] at h₄
  subst h₄
  simp
  rw [abs_le] at h₃
  omega

theorem ptsArr_eq_of_aPos_eq_and_taken_eq_insert {s s' : State} {p}
(h₂ : s'.aPos = s.aPos) (h₁ : s'.taken = s.taken.insert p)
(h₃ : ∃ (z : ℤ), |z| ≤ 3 ∧ edge₀.getBorderPoint s.aPos z = p) :
edge₀.ptsArr s' (-3) 7 = (edge₀.ptsArr s (-3) 7).set (p.x - s.aPos.x + 3).toNat true
(ptsArr_eq_of_aPos_eq_and_taken_eq_insert.proof₁ h₁ h₃) := by
  unfold ptsArr
  obtain ⟨z, h₃, h₄⟩ := h₃
  simp [getBorderPoint] at h₄ ⊢
  subst h₄
  simp only [h₁, h₂, Int.reduceNeg, Set'.mem_insert, Point.mk.injEq, add_right_inj, and_true,
    Bool.decide_or, add_sub_cancel_left]; clear h₁ h₂
  simp [List.range_succ]
  replace h₃ : z ∈ ({-3, -2, -1, 0, 1, 2, 3} : Set ℤ)
  · rw [abs_le] at h₃
    simp
    omega
  simp at h₃
  rcases h₃ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem exi_fin_y_of_f_eq_some {p} (h : edge₀.f s = some p) : ∃ (y : Fin 6), s.aPos.y = -y := by
  have h₁ := of_f_eq_some h; clear h
  obtain ⟨h₁, h₂, -⟩ := h₁
  simp at h₁ h₂
  simp_rw [←neg_eq_iff_eq_neg]
  generalize hy : -s.aPos.y = y
  rw [neg_eq_iff_eq_neg] at hy
  rw [hy] at h₁ h₂; clear hy
  simp at h₁ h₂
  refine ⟨⟨y.toNat, by omega⟩, ?_⟩
  simp
  omega 