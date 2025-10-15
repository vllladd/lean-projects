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

theorem euclideanDist_triangle_aux₁ {a b x y : ℝ} :
a * b + x * y ≤ b ^ 2 + √((x ^ 2 + b ^ 2) * (y ^ 2 + (a - b) ^ 2)) := by
  suffices : a * b + x * y - b ^ 2 ≤ √((x ^ 2 + b ^ 2) * (y ^ 2 + (a - b) ^ 2))
  · linarith
  apply le_of_sq_le_sq _ # by positivity
  rw [sq_sqrt # by positivity]
  ring_nf
  suffices h : 0 ≤ x ^ 2 * (a - b) ^ 2 - 2 * (x * (a - b)) * (y * b) + y ^ 2 * b ^ 2
  · linarith
  simp only [←mul_pow, ←sub_sq]
  positivity

theorem euclideanDist_triangle {n : ℕ} {a b c : Fin n → ℝ} :
euclideanDist a c ≤ euclideanDist a b + euclideanDist b c := by
  dsimp [euclideanDist, euclideanNorm]
  induction n; simp
  nm n ih
  specialize @ih (λ ⟨i, h⟩ => a ⟨i, by linarith⟩) (λ ⟨i, h⟩ => b ⟨i, by linarith⟩)
    (λ ⟨i, h⟩ => c ⟨i, by linarith⟩)
  simp at ih
  simp_rw [Finset.sum_fin_eq_sum_range] at ih ⊢
  simp [Finset.range_succ]
  let f (a b : Fin (n + 1) → ℝ) : ℝ := ∑ i ∈ Finset.range n, if h : i < n
    then (a ⟨i, by linarith⟩ - b ⟨i, by linarith⟩) ^ 2 else 0
  have hf : ∀ a b, 0 ≤ f a b
  · intro x y; simp [f]; apply Finset.sum_nonneg; intros; split_ifs <;> positivity
  generalize hx : f a c = x
  generalize hy : f a b = y
  generalize hz : f b c = z
  generalize_proofs hn
  generalize hn' : (⟨n, hn⟩ : Fin # n + 1) = n'
  convert_to √((a n' - c n') ^ 2 + x) ≤ √((a n' - b n') ^ 2 + y) + √((b n' - c n') ^ 2 + z)
  · simp [←hx, ←hn']
    congr 2
    apply Finset.sum_congr rfl
    simp
    intro k hk
    split_ifs with h₁; rfl
    linarith
  · simp [←hy, ←hz, ←hn']
    congr 3
    · apply Finset.sum_congr rfl
      simp
      intro k hk
      split_ifs with h₁; rfl
      linarith
    · apply Finset.sum_congr rfl
      simp
      intro k hk
      split_ifs with h₁; rfl
      linarith
  subst hn' f
  dsimp at hx hy hz
  simp_rw [hx, hy, hz] at ih
  simp only [add_comm _ x, add_comm _ y, add_comm _ z]
  replace hx : 0 ≤ x; subst hx; apply hf
  replace hy : 0 ≤ y; subst hy; apply hf
  replace hz : 0 ≤ z; subst hz; apply hf
  replace ih : x ≤ y + z + 2 * √y * √z
  · rw [←sq_le_sq₀, add_sq, sq_sqrt, sq_sqrt, sq_sqrt] at ih
    all_goals first | positivity | linarith
  generalize_proofs hn
  generalize (⟨n, hn⟩ : Fin (n + 1)) = n
  generalize a n = a
  generalize b n = b
  generalize c n = c
  nm n' a' b' c'; clear! n' a' b' c'
  generalize hd : a - c = d
  rw [show a = c + d by linarith]
  generalize he : c + d - b = e
  rw [show b = c + d - e by linarith]
  rw [show c + d - e - c = d - e by ring_nf]
  clear! a b c
  rename' d => a, e => b
  rw [←sq_le_sq₀, add_sq, sq_sqrt, sq_sqrt, sq_sqrt, mul_assoc]
    <;> try positivity
  suffices h : 2 * √y * √z + a ^ 2 ≤ b ^ 2 +
    2 * √(y + b ^ 2) * √(z + (a - b) ^ 2) + (a - b) ^ 2
  · linarith
  clear! x
  rw [sub_sq]
  suffices h : 2 * √y * √z + a ^ 2 ≤ b ^ 2 +
    2 * √(y + b ^ 2) * √(z + (a - b) ^ 2) + a ^ 2 - 2 * a * b + b ^ 2
  · ring_nf at h ⊢; exact h
  suffices h : a * b + √y * √z ≤ b ^ 2 + √(y + b ^ 2) * √(z + (a - b) ^ 2)
  · linarith
  nth_rw 2 [←sq_sqrt hz, ←sq_sqrt hy]
  have hx : 0 ≤ √y; positivity
  have hy : 0 ≤ √z; positivity
  generalize √y = x at hx ⊢
  generalize √z = y at hy ⊢
  nm r h; clear! r z
  rw [←sqrt_mul] <;> try positivity
  exact euclideanDist_triangle_aux₁

end euclidean