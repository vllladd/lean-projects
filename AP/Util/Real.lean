import AP.Util.Finset

namespace Real

theorem add_inv {a b : ℝ} (h : b ≠ 0) : a + b⁻¹ = (a * b + 1) / b := by
  field_simp

theorem pow_lt_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ b < c ↔ a < c ^ (1 / b) := by
  iterate rw [Real.rpow_lt_iff_lt_log, Real.lt_rpow_iff_log_lt] <;>
    try linarith
  have h : Real.log c = b * ((1 / b) * Real.log c) := by
    rw [←mul_assoc, mul_div, mul_one, div_self # by linarith]
    simp
  nth_rw 1 [h]
  rw [mul_lt_mul_iff_of_pos_left hb]

theorem add_inv_pow_lt_exp_one_of {a : ℝ} (h : 0 ≤ a) :
    (1 + a⁻¹) ^ a < Real.exp 1 := by
  rw [le_iff_eq_or_lt] at h; rcases h with rfl | h; simp
  rw [Real.rpow_def_of_pos # by positivity, Real.exp_lt_exp, (by simp : a = a⁻¹⁻¹),
    mul_inv_lt_iff₀' # by positivity, add_comm]; simp
  nth_rw 2 [(by simp : a⁻¹ = a⁻¹ + 1 - 1)]; apply Real.log_lt_sub_one_of_pos
  positivity; apply ne_of_congr (· - 1); simp; linarith

theorem ofNat_eq {n} : (OfNat.ofNat n : ℝ) = n := by
  rw [ext_cauchy_iff]; (iterate 2 cases n; simp; nm n); rfl

theorem list_sum_map_mul_left {xs : List ℝ} {w : ℝ} :
(xs.map (w * ·)).sum = w * xs.sum := by
  induction xs; simp; nm x xs ih; simp [ih]; ring_nf

theorem list_sum_map_mul_right {xs : List ℝ} {w : ℝ} :
(xs.map (· * w)).sum = xs.sum * w := by
  induction xs; simp; nm x xs ih; simp [ih]; ring_nf

noncomputable
def am (xs : List ℝ) : ℝ :=
  xs.sum / xs.length

noncomputable
def gm (xs : List ℝ) : ℝ :=
  xs.prod ^ (xs.length : ℝ)⁻¹

theorem gm_le_am (xs : List ℝ) (h₁ : xs ≠ []) (h₂ : ∀ x ∈ xs, 0 ≤ x) : gm xs ≤ am xs := by
  have h_len : xs.length ≠ 0; simpa
  have h_len' : (xs.length : ℝ) ≠ 0; simpa
  have h₃ := @Real.geom_mean_le_arith_mean_weighted
  specialize @h₃ ℕ (Finset.range xs.length) (λ _ => xs.length⁻¹) (xs[·]!) _ _ _
  · simp only [Finset.mem_range, inv_nonneg, Nat.cast_nonneg, implies_true]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_inv_cancel₀ h_len'
  · simp; intro k hk; rw [List.getElem?_eq_getElem hk]
    simp; simp_all only [ne_eq, List.length_eq_zero_iff, not_false_eq_true,
      Nat.cast_eq_zero, List.getElem_mem]
  rw [Finset.sum_range_list_get! (f := ((xs.length : ℝ)⁻¹ * ·)),
    Finset.prod_range_list_get! (f := (· ^ (xs.length : ℝ)⁻¹)),
    Real.list_prod_map_rpow _ h₂, Real.list_sum_map_mul_left] at h₃
  convert h₃; unfold am; field_simp

theorem gm_le_am_2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  have h := gm_le_am (xs := [a, b])
  specialize h nofun (by simp [ha, hb])
  simp [am, gm] at h; simpa [Real.sqrt_eq_rpow]

theorem gm_le_am_3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
(a * b * c) ^ (3 : ℝ)⁻¹ ≤ (a + b + c) / 3 := by
  have h := gm_le_am (xs := [a, b, c])
  specialize h nofun (by simp [ha, hb, hc])
  simp [am, gm] at h; simpa [add_assoc, mul_assoc]

theorem log_eq_logb {a : ℝ} : a.log = Real.logb (Real.exp 1) a := by
  rw [logb]; simp

theorem eq_of_log_eq_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
(h : a.log = b.log) : a = b := by
  replace h := congrArg (·.exp) h; dsimp at h
  rw [exp_log ha, exp_log hb] at h; exact h

theorem log_eq_log_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
a.log = b.log ↔ a = b := by
  use eq_of_log_eq_log ha hb; rintro rfl; rfl

theorem rpow_eq_exp {a b : ℝ} (ha : 0 < a) : a ^ b = (b * a.log).exp := by
  rw [←log_eq_log_iff] <;> try positivity;; simp [log_rpow ha b]

section euclidean

noncomputable
def euclideanNorm {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  √(∑ i, a i ^ 2)

noncomputable
def euclideanDist {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  euclideanNorm (a - b)

theorem euclideanDist_triangle {n : ℕ} {a b c : Fin n → ℝ} :
euclideanDist a c ≤ euclideanDist a b + euclideanDist b c := by
  unfold euclideanDist euclideanNorm
  dsimp
  induction n; simp
  nm n ih
  specialize @ih (λ ⟨i, h⟩ => a ⟨i, by linarith⟩) (λ ⟨i, h⟩ => b ⟨i, by linarith⟩)
    (λ ⟨i, h⟩ => c ⟨i, by linarith⟩)
  simp at ih
  simp_rw [Finset.sum_fin_eq_sum_range] at ih ⊢
  simp [Finset.range_succ]
  generalize hx : (∑ i ∈ Finset.range n, if h : i < n
    then (a ⟨i, by linarith⟩ - c ⟨i, by linarith⟩) else 0) = x
  generalize hy : (∑ i ∈ Finset.range n, if h : i < n
    then (b ⟨i, by linarith⟩ - c ⟨i, by linarith⟩) else 0) = y
  generalize hz : (∑ i ∈ Finset.range n, if h : i < n
    then (c ⟨i, by linarith⟩ - c ⟨i, by linarith⟩) else 0) = z
  convert_to √((a ⟨n, by linarith⟩ - c ⟨n, by linarith⟩) ^ 2 + x) ≤
    √((a ⟨n, by linarith⟩ - b ⟨n, by linarith⟩) ^ 2 + y) +
    √((b ⟨n, by linarith⟩ - c ⟨n, by linarith⟩) ^ 2 + z)
  · simp [←hx]
    congr

#check 0 #exit

end euclidean