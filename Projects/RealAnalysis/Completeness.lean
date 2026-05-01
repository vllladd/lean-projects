import Projects.RealAnalysis.Filter

namespace RealAnalysis

theorem abs_real_mk_sub_le_aux₁ {a : ℕ → ℚ} {x e : ℝ} {N} {ha : IsCauSeq abs a}
(h : ∀ n, N ≤ n → |a n - x| < e) : x - e ≤ Real.mk ⟨a, ha⟩ := by
  replace h : ∀ (n : ℕ), N ≤ n → x - e < a n
  · intro n hn
    specialize h n hn
    rw [abs_lt] at h
    linarith
  change ∀ n, _ → _ < Real.mk ⟨_, _⟩ at h
  obtain ⟨b, hb, h₁⟩ := @Real.exi_mk_cauchy (x - e)
  rw [h₁] at h ⊢; clear h₁; clear! x e
  simp_rw [Real.mk_lt] at h
  change ∀ n, _ → ∃ _, _ at h
  simp at h
  rw [le_iff_eq_or_lt, Real.mk_eq, Real.mk_lt, or_iff_not_imp_left]
  intro h₂
  change ¬∀ _, _ at h₂
  push Not at h₂
  simp at h₂
  obtain ⟨y, hy, h₁⟩ := h₂
  change ∃ _, _
  simp
  rw [isCauSeq_rat_iff] at ha hb
  obtain ⟨N₀, H⟩ : ∃ N, ∀ n, N ≤ n → b n < a n
  · specialize ha (y / 4) # by positivity
    specialize hb (y / 4) # by positivity
    obtain ⟨N₁, ha⟩ := ha
    obtain ⟨N₂, hb⟩ := hb
    specialize h₁ # N + N₁ + N₂
    obtain ⟨N₃, hN₃, h₁⟩ := h₁
    use N₃
    intro n hn
    specialize h N₃ # by linarith
    obtain ⟨x, hx, N₄, h⟩ := h
    specialize h (N₃ + N₄) # by linarith
    simp [le_abs] at h₁
    rcases h₁ with h₁ | h₁
    · suffices H : y < y / 2; linarith
      replace h : b (N₃ + N₄) - a N₃ ≤ -x; linarith
      calc
      _ ≤ b N₃ - a N₃ := h₁
      _ < b (N₃ + N₄) - a N₃ + y / 4 := by
        specialize hb N₃ (N₃ + N₄) (by linarith) (by linarith)
        rw [abs_lt] at hb; linarith
      _ < _ := by linarith
    calc
    _ < b N₃ + y / 4 := by
      specialize hb n N₃ (by linarith) (by linarith)
      rw [abs_lt] at hb; linarith
    _ ≤ a N₃ + y / 4 - y := by linarith
    _ < a n + y / 2 - y := by
      specialize ha n N₃ (by linarith) (by linarith)
      rw [abs_lt] at ha; linarith
    _ < _ := by linarith
  use y / 2 / 2, by positivity
  specialize ha (y / 2 / 2) # by positivity
  specialize hb (y / 2 / 2) # by positivity
  obtain ⟨N₁, ha⟩ := ha
  obtain ⟨N₂, hb⟩ := hb
  use N₀ + N + N₁ + N₂
  intro n hn
  specialize h₁ n
  obtain ⟨N₃, hN₃, h₁⟩ := h₁
  contrapose! h₁
  have h₂ : b n < a n
  · apply H; linarith
  replace h₂ : a n - b n = |a n - b n|
  · rw [abs_of_pos]; simpa
  rw [h₂] at h₁; clear h₂
  · rw [abs_sub_comm]
    apply abs_sub_lt_trans_half # b n
    · apply abs_sub_lt_trans_half (a n) _ h₁
      apply ha <;> linarith
    · rw [abs_sub_comm]
      apply abs_sub_lt_trans_half (b n)
      · apply hb <;> linarith
      simpa

theorem abs_real_mk_sub_le_aux₂ {a : ℕ → ℚ} {x e : ℝ} {N} {ha : IsCauSeq abs a}
(h : ∀ n, N ≤ n → |a n - x| < e) : Real.mk ⟨a, ha⟩ ≤ x + e := by
  have H₁ := @abs_real_mk_sub_le_aux₁ (-a) (-x) e N ha.neg
  specialize H₁ _
  · simp_rw [abs_sub_comm]
    simp
    simp_rw [add_comm (-x)]
    simpa
  rw [←Real.neg_mk] at H₁; rotate_left; exact ha
  linarith

theorem abs_real_mk_sub_le {a : ℕ → ℚ} {x e : ℝ} {ha : IsCauSeq abs a}
(h : ∃ N, ∀ n, N ≤ n → |a n - x| < e) : |Real.mk ⟨a, ha⟩ - x| ≤ e := by
  obtain ⟨N, h⟩ := h
  by_cases he : e ≤ 0
  · specialize h N (by rfl)
    contrapose! h
    apply he.trans
    simp
  push Not at he
  rw [abs_le]
  constructor
  · linarith [abs_real_mk_sub_le_aux₁ (ha := ha) h]
  · linarith [abs_real_mk_sub_le_aux₂ (ha := ha) h]

theorem tendsTo_real_mk {a : ℕ → ℚ} {ha : IsCauSeq abs a} :
tendsTo (a ·) (Real.mk ⟨a, ha⟩) := by
  intro e he
  obtain ⟨e', he₁, he₂⟩ := exists_rat_btwn (x := (0 : ℝ)) (y := e / 4) # by positivity
  simp at he₁
  obtain ⟨N, h⟩ := ha e' he₁
  use N
  intro n hn
  rw [abs_sub_comm]
  apply lt_of_le_of_lt (b := e / 2) _ # by linarith
  apply abs_real_mk_sub_le
  use N
  intro n₁ h₁
  have h₂ := h n # by linarith
  have h₃ := h n₁ # by linarith
  replace h₂ : |(a n : ℝ) - a N| < e / 2 / 2
  · trans (e' : ℝ); exact_mod_cast h₂; linarith
  replace h₃ : |(a n₁ : ℝ) - a N| < e / 2 / 2
  · trans (e' : ℝ); exact_mod_cast h₃; linarith
  exact Real.abs_sub_lt_of_lt_lt_half h₃ h₂