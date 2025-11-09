import AP.RealAnalysis.Completeness

namespace RealAnalysis

def series (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

theorem series_eq {a} : series a = λ n => ∑ i ∈ Finset.range n, a i := rfl

@[simp]
theorem series_zero {a} : series a 0 = 0 := by
  simp [series]

theorem series_succ {a n} : series a (n + 1) = series a n + a n := by
  simp [series, Finset.sum_range_succ]

@[simp]
theorem series_const {x n} : series (λ _ => x) n = n * x := by
  simp [series]

theorem tendsTo_zero_of_converges_series {a} (h : converges (series a)) : tendsTo a 0 := by
  choose S h using h
  intro e he
  simp
  unfold eventually
  specialize h (e / 2) (by positivity)
  choose N h using h
  dsimp at h
  use N
  intro n hn
  have h₁ := h n hn
  have h₂:= h (n + 1) (by omega)
  clear h
  rw [series_succ] at h₂
  replace h₂ : |series a n - S + a n| < e / 2; ring_nf at h₂ ⊢; exact h₂
  generalize series a n - S = x at h₁ h₂
  by_contra! h₃
  suffices : e < e; linarith
  calc
  _ ≤ |a n| := h₃
  _ = |a n + x - x| := by simp
  _ ≤ |a n + x| + |x| := by rw [sub_eq_add_neg]; apply abs_add_le _ _ |>.trans; simp
  _ < _ := by rw [add_comm _ x]; linarith

@[simp]
theorem inv_add_tendsTo_zero {x : ℝ} : tendsTo (λ n => (n + x)⁻¹) 0 := by
  rw [tendsTo_iff_eps_lt_one]
  intro e he he₁
  simp
  choose N h₁ using exists_nat_gt # e⁻¹ + |x|
  use N
  intro n hn
  replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
  have h₃ : e⁻¹ < n - |x|
  · calc
    _ < n - |x| := by linarith
    _ ≤ _ := by simp
  have h₄ : e⁻¹ < n + x
  · apply lt_of_lt_of_le h₃
    rw [sub_eq_add_neg, add_le_add_iff_left]
    exact neg_abs_le x
  have h₂ : 0 < n + x
  · calc
    _ < e⁻¹ := by positivity
    _ ≤ _ := by linarith
  rw [inv_lt_iff_one_lt_mul₀, abs_of_pos] <;> try positivity
  calc
  _ = e * e⁻¹ := by rw [mul_inv_cancel₀]; positivity
  _ < _ := by nlinarith

theorem add_div_add_tendsTo_one_aux₁ {x y : ℝ} (hy : 0 < y) :
tendsTo (λ n => (n + x) / (n + y)) 1 := by
  rw [show x = y + (x - y) by ring_nf]
  simp_rw [←add_assoc]
  have h : ∀ (n : ℕ) x, (n + y + x) / (n + y) = 1 + x / (n + y)
  · intro n x
    rw [same_add_div]
    positivity
  simp_rw [h]; clear h
  nth_rw 2 [show (1 : ℝ) = 1 + 0 by norm_num]
  apply tendsTo_add tendsTo_const
  rw [show 0 = (x - y) * 0 by simp]
  apply tendsTo_mul tendsTo_const
  simp

@[simp]
theorem add_div_add_tendsTo_one {x y : ℝ} : tendsTo (λ n => (n + x) / (n + y)) 1 := by
  choose k hk using exists_nat_gt |y|
  rw [←tendsTo_drop_iff (k := k)]
  simp [add_comm k, add_assoc]
  apply add_div_add_tendsTo_one_aux₁
  rw [abs_lt] at hk
  linarith

@[simp]
theorem add_div_tendsTo_one {x : ℝ} : tendsTo (λ n => (n + x) / n) 1 := by
  convert add_div_add_tendsTo_one (y := 0); simp

@[simp]
theorem div_add_tendsTo_one {x : ℝ} : tendsTo (λ n => n / (n + x)) 1 := by
  convert add_div_add_tendsTo_one (x := 0); simp

theorem leibniz_sum {n} : ∑ i ∈ Finset.range n, (1 : ℝ) / ((i + 1) * (i + 2)) = n / (n + 1) := by
  induction n
  · simp
  nm n ih
  rw [Finset.sum_range_succ, ih]; clear ih
  simp
  field_simp
  ring_nf

theorem leibniz_sum' {n} : ∑ i ∈ Finset.range n,
(1 : ℝ) / ((i + 1) * (i + 2)) = 1 - 1 / (n + 1) := by
  rw [leibniz_sum]; field_simp; simp

theorem leibniz_series_tendsTo : tendsTo (series λ n => 1 / ((n + 1) * (n + 2))) 1 := by
  simp_rw [series_eq, leibniz_sum]; simp