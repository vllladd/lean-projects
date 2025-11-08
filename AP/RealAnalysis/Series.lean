import AP.RealAnalysis.Completeness

namespace RealAnalysis

def series (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

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