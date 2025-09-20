import AP.Util

def tendsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - L| < ε

def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, tendsTo a L

-----

@[simp]
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

theorem tendsTo_sub {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ - a₂) (L₁ - L₂) := by
  intro e he
  dsimp
  specialize h₁ (e / 2) (by simpa)
  specialize h₂ (e / 2) (by simpa)
  obtain ⟨N₁, h₁⟩ := h₁
  obtain ⟨N₂, h₂⟩ := h₂
  use max N₁ N₂
  intro n hn
  specialize h₁ n # le_of_max_le_left hn
  specialize h₂ n # le_of_max_le_right hn
  calc
    _ = |(a₁ n - L₁) - (a₂ n - L₂)| := by ring_nf
    _ ≤ |a₁ n - L₁| + |a₂ n - L₂| := by apply abs_sub
  linarith

theorem ofNat_seq_eq {n : ℕ} : (OfNat.ofNat n : ℕ → ℝ) = λ _ => ↑n := by
  ext i; iterate 2 cases n; simp; nm n
  change ((n + 2 : ℕ) : ℝ) = _; ring_nf

theorem cast_seq_eq {n : ℕ} : (n : ℕ → ℝ) = λ _ => ↑n := by
  ext i; iterate 2 cases n; simp; nm n
  change ((n + 2 : ℕ) : ℝ) = _; ring_nf

@[simp]
theorem tendsTo_const_ofNat {n : ℕ} : tendsTo (OfNat.ofNat n) n := by
  simp [ofNat_seq_eq]

@[simp]
theorem tendsTo_const_cast {n : ℕ} : tendsTo n n := by
  simp [cast_seq_eq]

@[simp]
theorem tendsTo_const_ofNat_lit {n : ℕ} :
tendsTo (OfNat.ofNat n) (OfNat.ofNat n) := by
  simp [Real.ofNat_eq]

theorem tendsTo_neg {a L} (h : tendsTo a L) :
tendsTo (-a) (-L) := by
  have h₁ := @tendsTo_sub 0 a 0 L tendsTo_const_ofNat_lit h
  simp at h₁; exact h₁

theorem tendsTo_add {a₁ a₂ L₁ L₂} (h₁ : tendsTo a₁ L₁)
(h₂ : tendsTo a₂ L₂) : tendsTo (a₁ + a₂) (L₁ + L₂) := by
  have h₃ := tendsTo_neg h₂
  convert_to tendsTo (a₁ - (0 - a₂)) (L₁ - (0 - L₂))
  iterate 2 ring_nf
  apply tendsTo_sub h₁; simpa

theorem tendsTo_mul_two {a L} (h : tendsTo a L) :
tendsTo (a * 2) (L * 2) := by
  simp only [mul_two]; exact tendsTo_add h h

example {a b : ℕ → ℝ} {L : ℝ} (h₁ : tendsTo a L)
(h₂ : ∀ (n : ℕ), b n = 2 * a n) : tendsTo b (2 * L) := by
  have h₃ : b = 2 * a
  · ext n; simp [h₂]
  subst h₃; clear h₂
  repeat rw [mul_comm 2]
  exact tendsTo_mul_two h₁