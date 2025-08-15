import AP.Util.Int

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