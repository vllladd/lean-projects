import AP.Util

namespace Euclidean

open Real

variable {n : ℕ} {a b c : Fin n → ℝ}

protected noncomputable
def norm {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  √(∑ i, a i ^ 2)

protected noncomputable
def dist {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  Euclidean.norm (a - b)

theorem dist_triangle_aux₁ {a b x y : ℝ} :
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

theorem dist_triangle :
Euclidean.dist a c ≤ Euclidean.dist a b + Euclidean.dist b c := by
  dsimp [Euclidean.dist, Euclidean.norm]
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
  exact dist_triangle_aux₁

noncomputable
scoped instance (priority := high) {n} : Norm # Fin n → ℝ where
  norm := Euclidean.norm

noncomputable
scoped instance (priority := high) {n} : Dist # Fin n → ℝ where
  dist := Euclidean.dist

theorem norm_def' : ‖a‖ = Euclidean.norm a := rfl
theorem dist_def' : dist a b = Euclidean.dist a b := rfl

noncomputable
scoped instance (priority := high) : PseudoMetricSpace # Fin n → ℝ where
  dist_self a := by simp [dist_def', Euclidean.dist, Euclidean.norm]
  dist_comm a b := by simp [dist_def', Euclidean.dist, Euclidean.norm, sub_sq_comm]
  dist_triangle a b c := dist_triangle

noncomputable
scoped instance (priority := high) : MetricSpace # Fin n → ℝ where
  eq_of_dist_eq_zero := by
    intro a b h
    simp [dist_def', Euclidean.dist, Euclidean.norm] at h
    rw [sqrt_eq_zero # by positivity] at h
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h
    rotate_left; intros; positivity
    ext k; specialize h k (by simp)
    nlinarith

example : ‖(![3, 4] : Fin 2 → ℝ)‖ = 5 := by
  simp [norm_def', Euclidean.norm]; norm_num

end Euclidean

example : ‖(![3, 4] : Fin 2 → ℝ)‖ = 4 := by
  change NNReal.toReal _ = _; simp [Finset.univ_fin2]; norm_num