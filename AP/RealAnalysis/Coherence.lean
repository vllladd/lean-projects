import AP.RealAnalysis.Series

namespace RealAnalysis

theorem subseq_nat_le_subseq_iff {σ n m} (h : Subseq σ) : σ n ≤ σ m ↔ n ≤ m := by
  unfold Subseq at h
  obtain (h₁ | rfl | h₁) := lt_trichotomy n m
  on_goal 2 => simp
  all_goals specialize h _ _ h₁
  · simp [le_of_lt h, le_of_lt h₁]
  · rw [iff_iff_not']; simp [h, h₁]

theorem tendsTo_of_eventually_subseq_cover {a : ℕ → ℝ} {s : Finset (ℕ → ℕ)} {L : ℝ}
(h₁ : ∀ σ ∈ s, Subseq σ) (h₂ : eventually # λ n => ∃ σ ∈ s, ∃ i, σ i = n)
(h₃ : ∀ σ ∈ s, tendsTo (a # σ ·) L) : tendsTo a L := by
  choose N h₂ using h₂; dsimp at h₂
  have h₀ : s.Nonempty
  · specialize h₂ N (by rfl)
    choose σ hσ h₂ using h₂
    use σ
  intro ε hε
  generalize hp : (λ (N : ℕ) (σ : ℕ → ℕ) => ∀ n, N ≤ n → |a (σ n) - L| < ε) = p
  replace h₃ : ∀ σ ∈ s, ∃ N, p N σ
  · subst hp; intro σ hσ; exact h₃ σ hσ ε hε
  replace h₃ : ∃ N, ∀ σ ∈ s, p N σ
  · clear! N
    generalize h₄ : (s.image # λ σ => Nat.find! (p · σ)).max' (by simpa) = N
    use N
    intro σ hσ
    simp_rw [←hp]
    intro n hn
    specialize h₃ σ hσ
    replace h₃ := Nat.find!_spec h₃
    generalize hM : Nat.find! (p · σ) = M at h₃
    have h₇ : M ≤ N
    · subst h₄ hM
      apply Finset.le_max'
      simp
      use σ
    simp_rw [←hp] at h₃
    apply h₃
    linarith
  choose M h₃ using h₃
  obtain ⟨K, h₄⟩ : ∃ K, ∀ σ ∈ s, σ (N + M) ≤ K
  · use (s.image # λ σ => σ # N + M).max' (by simpa)
    intro σ hσ
    apply Finset.le_max'
    simp
    use σ
  have h₅ : N + M ≤ K
  · choose σ hσ using h₀
    exact h₄ σ hσ |>.trans' # nat_le_of_subseq # h₁ σ hσ
  use K
  intro n hn
  obtain ⟨σ, hσ, i, rfl⟩ := h₂ n # by linarith
  simp_rw [←hp] at h₃
  specialize h₃ σ hσ
  apply h₃; clear h₃
  specialize h₄ σ hσ
  replace h₄ := h₄.trans hn
  specialize h₁ σ hσ
  rw [subseq_nat_le_subseq_iff h₁] at h₄
  linarith