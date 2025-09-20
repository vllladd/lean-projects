import AP.Util

def tendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - L| < ε

def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, tendsTo a L

-----

theorem tendsTo_const {L} : tendsTo (λ _ => L) L := by
  intro e he; use 0; simpa

theorem tendsTo_unique {a L₁ L₂}
(h₁ : tendsTo a L₁) (h₂ : tendsTo a L₂) : L₁ = L₂ := by
  by_contra! h₃
  wlog h₄ : L₁ < L₂ with ih
  · push_neg at h₄; apply ne_symm' at h₃
    apply ih h₂ h₁ h₃; exact lt_of_le_of_ne h₄ h₃
  clear h₃
  generalize he : (L₂ - L₁) / 2 = e
  have h₅ : 0 < e; linarith
  specialize h₁ e (by linarith)
  specialize h₂ e (by linarith)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  specialize h₁ (max N₁ N₂) (by simp)
  specialize h₂ (max N₁ N₂) (by simp)
  generalize a (max N₁ N₂) = x at h₁ h₂
  replace h₁ := abs_lt.mp h₁ |>.2
  replace h₂ := abs_lt.mp h₂ |>.1
  simp at h₂
  linarith

theorem tendsTo_drop_iff {a L k} : tendsTo (a # · + k) L ↔ tendsTo a L := by
  constructor
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp at h
    use N + k
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    specialize h (n + N) (by linarith)
    ring_nf at h ⊢
    exact h
  · intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    dsimp
    use N
    intro n hn
    specialize h (n + k) (by linarith)
    exact h

theorem converges_drop_iff {a k} : converges (a # · + k) ↔ converges a :=
  exists_congr # λ _ => tendsTo_drop_iff

theorem tendsTo_one_div : tendsTo (1 / ·) 0 := by
  intro e he
  obtain ⟨N, hN⟩ := exists_nat_gt # 1 / e
  use N
  intro n hn
  simp
  rw [abs_of_nonneg # by simp]
  have h₁ : 0 < (n : ℝ)
  · cases n
    · simp at hn; simp [hn] at hN; linarith
    · simp; linarith
  replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
  rw [inv_lt_iff_one_lt_mul₀ h₁]
  replace hN : 1 < N * e
  · rwa [←mul_inv_lt_iff₀ he]
  nlinarith

theorem tendsTo_one_div_succ : tendsTo (λ n => 1 / (n + 1)) 0 := by
  have h := tendsTo_drop_iff (a := (1 / ·)) (k := 1) (L := 0)
  push_cast at h; rw [h]; exact tendsTo_one_div

theorem not_converges_alternating {x y : ℝ} (h : x ≠ y) :
¬converges (if Even · then x else y) := by
  simp only [converges, tendsTo, not_exists, not_forall, not_lt]
  intro L
  wlog h₁ : L ≠ x with ih
  · apply ne_symm' at h
    specialize ih h L _
    · simp at h₁
      subst h₁
      exact ne_symm' h
    obtain ⟨e, he, ih⟩ := ih
    use e, he
    intro N
    specialize ih N
    obtain ⟨n, hn, ih⟩ := ih
    use n + 1, by linarith
    simp_rw [Nat.even_succ_iff, ←Nat.not_even_iff_odd, ite_not]
    exact ih
  use |L - x|, by simp [sub_ne_zero_of_ne h₁]
  intro N
  use N * 2, by simp
  simp
  rw [abs_sub_comm]

theorem not_converges_minus_one_pow : ¬converges ((-1 : ℝ) ^ ·) := by
  convert not_converges_alternating (x := 1) (y := -1) (by norm_num)
  nm n; induction n using Nat.mod_2_ind <;> simp