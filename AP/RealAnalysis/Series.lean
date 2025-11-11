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

theorem series_le_of_le {a b n} (h₁ : ∀ n, a n ≤ b n) : series a n ≤ series b n := by
  dsimp [series]
  apply Finset.sum_le_sum
  intro n hn
  apply h₁

theorem converges_of_monoLe_and_forall_le_add {a b x} (h₁ : converges b)
(h₂ : monoLe a) (h₃ : ∀ n, a n ≤ b n + x) : converges a := by
  apply converges_of_monoLe_and_bounded_top h₂; use ub b + x; intro n
  apply h₃ n |>.trans # le_of_lt _; simp; apply lt_ub_of_converges h₁

theorem converges_of_monoLe_and_forall_le {a b} (h₁ : converges b)
(h₂ : monoLe a) (h₃ : ∀ n, a n ≤ b n) : converges a := by
  convert converges_of_monoLe_and_forall_le_add (x := 0) h₁ h₂ _; simpa

theorem series_add {a n k} : series a (n + k) =
∑ i ∈ Finset.range n, a i + series (a # n + ·) k := by
  simp [series, Finset.sum_range_add]

theorem converges_basel {x} : converges # series # λ n => (1 / (n + x) ^ 2) := by
  choose k hk using exists_nat_gt # |x| + 2
  generalize hy : ∑ i ∈ Finset.range k, (1 : ℝ) / (i + x) ^ 2 = y
  rw [←converges_drop_iff (k := k)]
  apply converges_of_monoLe_and_forall_le_add (x := y) ⟨_, leibniz_series_tendsTo⟩
  · rw [monoLe_iff_le_succ]; intro n
    simp [Nat.add_one_add, series_succ]; positivity
  intro n
  rw [add_comm, series_add, add_comm _ y, hy]
  simp
  apply series_le_of_le
  clear n
  intro n
  field_simp
  have h₁ := add_abs_nonneg x
  rw [div_le_iff₀ # by rw [sq_pos_iff]; linarith]
  ring_nf
  nlinarith

@[simp]
theorem subseq_add_right {k : ℕ} : subseq (· + k) := by
  rw [subseq_iff_lt_add_one]; omega

@[simp]
theorem subseq_add_left {k : ℕ} : subseq (k + ·) := by
  rw [subseq_iff_lt_add_one]; omega

@[simp]
theorem subseq_mul_right {k : ℕ} (h : k ≠ 0) : subseq (· * k) := by
  rw [subseq_iff_lt_add_one]; cases k; simp at h; ring_nf; omega

@[simp]
theorem subseq_mul_left {k : ℕ} (h : k ≠ 0) : subseq (k * ·) := by
  rw [subseq_iff_lt_add_one]; cases k; simp at h; ring_nf; omega

theorem pow_tendsTo_zero_of_pos_and_lt_one {x : ℝ}
(h₁ : 0 < x) (h₂ : x < 1) : tendsTo (x ^ ·) 0 := by
  generalize ha : (x ^ ·) = a
  replace ha : ∀ n, a n = x ^ n
  · simp [←ha]
  have h₃ : monoGt a
  · rw [monoGt_iff_succ_lt]
    intro n
    simp [ha]
    rw [pow_lt_pow_iff_right_of_lt_one₀] <;> linarith
  have h₄ : ∀ n, 0 < a n
  · intro n
    rw [ha]
    positivity
  have h₅ := converges_of_monoGt_and_bounded_bottom h₃
  specialize h₅ _
  · use 0
    intro n
    exact le_of_lt # h₄ n
  choose L h₅ using h₅
  have h₆ : tendsTo (λ n => a # n * 2) L
  · apply tendsTo_subseq h₅
    simp
  have h₇ : tendsTo (λ n => a # n * 2) (L ^ 2)
  · simp_rw [ha, pow_mul, ←ha]
    exact tendsTo_pow h₅
  have h := tendsTo_unique h₆ h₇
  convert h₅
  symm
  replace h : L * (L - 1) = 0
  · nlinarith
  simp at h
  rcases h with h | h; exact h
  exfalso
  simp [sub_eq_iff_eq_add] at h
  subst h
  contrapose h₅; clear h₅
  simp [tendsTo, eventually]
  use 1 - x, by linarith
  intro N
  use N + 1, by simp
  rw [ha]
  rw [abs_of_neg]
  rotate_left
  · simp
    rwa [pow_lt_one_iff_of_nonneg]
    linarith; simp
  simp
  suffices h : x ^ (N + 1) ≤ x ^ 1
  · linarith
  rw [pow_le_pow_iff_right_of_lt_one₀ h₁ h₂]
  simp

theorem geom_series_eq {x : ℝ} {n : ℕ} (h : x ≠ 1) :
series (x ^ ·) n = (1 - x ^ n) / (1 - x) := by
  rw [series, Finset.sum_geom_eq h]

theorem geom_series_eq_ext {x : ℝ} (h : x ≠ 1) :
series (x ^ ·) = λ n => (1 - x ^ n) / (1 - x) := by
  ext n; exact geom_series_eq h

theorem geom_series_tendsTo {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1) :
tendsTo (series (x ^ ·)) # 1 / (1 - x) := by
  rw [geom_series_eq_ext # by linarith]
  apply tendsTo_div
  · linarith
  · nth_rw 2 [show (1 : ℝ) = 1 - 0 by norm_num]
    apply tendsTo_sub tendsTo_const
    exact pow_tendsTo_zero_of_pos_and_lt_one h₁ h₂
  · exact tendsTo_const