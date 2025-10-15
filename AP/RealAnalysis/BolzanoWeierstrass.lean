import AP.RealAnalysis.Continuity

namespace RealAnalysis

open scoped Classical in
@[simp] noncomputable
def bwSeq (a : ℕ → ℝ) (y₁ y₂ : ℚ) (n : ℕ) : ℚ × ℚ := match n with
| 0 => (y₁, y₂)
| n + 1 => let y := (y₁ + y₂) / 2
  if {i | y₁ ≤ a i ∧ a i ≤ y₂}.Infinite
  then bwSeq a y₁ y n else bwSeq a y y₂ n

theorem le_bwSeq_fst {a : ℕ → ℝ} {M : ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(h : boundedBy a M) (hy₁ : y₁ < -M) (hy₂ : M < y₂) : y₁ ≤ (bwSeq a y₁ y₂ n).1 := by
  have hM : 0 ≤ (M : ℝ)
  · specialize h 0; trans |a 0| <;> simp [h]
  have h₂ : y₁ < y₂
  · have H : (y₁ : ℝ) < y₂; linarith
    simp at H; exact H
  clear hy₁ hy₂
  induction n generalizing y₁ y₂; rfl
  nm n ih
  simp
  split_ifs with h₁
  · apply ih; linarith
  trans (y₁ + y₂) / 2; linarith
  apply ih; linarith

theorem bwSeq_snd_le {a : ℕ → ℝ} {M : ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(h : boundedBy a M) (hy₁ : y₁ < -M) (hy₂ : M < y₂) : (bwSeq a y₁ y₂ n).2 ≤ y₂ := by
  have hM : 0 ≤ (M : ℝ)
  · specialize h 0; trans |a 0| <;> simp [h]
  have h₂ : y₁ < y₂
  · have H : (y₁ : ℝ) < y₂; linarith
    simp at H; exact H
  clear hy₁ hy₂
  induction n generalizing y₁ y₂; simp
  nm n ih
  simp
  split_ifs with h₁
  · trans (y₁ + y₂) / 2
    · apply ih; linarith
    linarith
  apply ih; linarith

theorem bwSeq_add {a : ℕ → ℝ} {M : ℝ} {y₁ y₂ : ℚ} {n k : ℕ}
(h : boundedBy a M) (hy₁ : y₁ < -M) (hy₂ : M < y₂) :
bwSeq a y₁ y₂ (n + k) = match bwSeq a y₁ y₂ n with
| (y₁', y₂') => bwSeq a y₁' y₂' k := by
  have hM : 0 ≤ (M : ℝ)
  · specialize h 0; trans |a 0| <;> simp [h]
  have h₂ : y₁ < y₂
  · have H : (y₁ : ℝ) < y₂; linarith
    simp at H; exact H
  clear hy₁ hy₂
  
  -- generalize hr : bwSeq a y₁ y₂ n = r
  -- rcases r with ⟨y₁', y₂'⟩
  -- dsimp
  -- 
  -- induction k generalizing y₁ y₂ y₁' y₂' n; exact hr
  -- nm k ih
  -- nth_rw 1 [Nat.add_succ, ←Nat.succ_add]
  -- 
  -- generalize hr' : bwSeq a y₁ y₂ (n + 1) = r'
  -- rcases r' with ⟨z₁, z₂⟩
  -- simp at hr'
  -- split_ifs at hr' with h₃
  -- 
  -- ·
  --   specialize @ih y₁ ((y₁ + y₂) / 2) n (by linarith) z₁ z₂ hr'
  --   rw [Nat.succ_add]
  --   simp [h₃, ih]
  --   split_ifs with h₄
  --   · 
  -- -- rw [ih # by linarith]
  -- split_ifs with h₃
  -- · 
  -- --   simp
  -- --   split_ifs with h₄
  -- --   · 
  
  sorry

-- #check 0 #exit

theorem bwSeq_fst_le_of_le {a : ℕ → ℝ} {M : ℝ} {y₁ y₂ : ℚ} {n m : ℕ}
(h : boundedBy a M) (hy₁ : y₁ < -M) (hy₂ : M < y₂) (hn : m ≤ n) :
(bwSeq a y₁ y₂ m).fst ≤ (bwSeq a y₁ y₂ n).fst := by
  have hM : 0 ≤ (M : ℝ)
  · specialize h 0; trans |a 0| <;> simp [h]
  have h₂ : y₁ < y₂
  · have H : (y₁ : ℝ) < y₂; linarith
    simp at H; exact H
  clear hy₁ hy₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  
  -- induction n generalizing y₁ y₂ <;> simp
  -- nm n ih
  -- split_ifs with h₁
  -- 
  -- · apply ih h₂ |>.trans
  
  sorry

-- #check 0 #exit

theorem isCauSeq_bwSeq {a : ℕ → ℝ} {M : ℝ} {y₁ y₂ : ℚ} (h : boundedBy a M)
(hy₁ : y₁ < -M) (hy₂ : M < y₂) : IsCauSeq abs (bwSeq a y₁ y₂ · |>.1) := by
  unfold boundedBy at h
  have hM : 0 ≤ (M : ℝ)
  · specialize h 0; trans |a 0| <;> simp [h]
  generalize hd : (y₂ - y₁ : ℝ) = d
  have H₁ : 0 < d; linarith
  intro ε hε
  replace hε : 0 < (ε : ℝ); simpa
  obtain ⟨N, hN⟩ : ∃ (n : ℕ), d / 2 ^ n < ε
  · by_cases h₂ : d ≤ ε; use 1
    · simp; calc
      d / 2 ≤ ε / 2 := by linarith
      _ < _ := by linarith
    push_neg at h₂
    suffices h₁ : ∃ (r : ℝ), 0 < r ∧ d / 2 ^ r < ε
    · obtain ⟨r, hr, h₁⟩ := h₁
      obtain ⟨n, hn⟩ := exists_nat_gt r
      use n
      apply h₁.trans'; clear h₁
      simp_rw [div_eq_mul_inv, mul_lt_mul_left H₁]
      rw [inv_lt_inv₀] <;> try positivity
      rw [←Real.rpow_natCast]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hn
    use Real.logb 2 (d / ε) + 1
    constructor
    · apply lt_add_of_le_of_pos _ # by norm_num
      apply Real.logb_nonneg # by norm_num
      rw [one_le_div₀ hε]; exact le_of_lt h₂
    rw [Real.rpow_add # by norm_num]
    rw [Real.rpow_logb] <;> try first | positivity | norm_num
    rw [div_mul, div_div_cancel₀] <;> try positivity
    linarith
  use N
  intro n (hn : N ≤ n)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  sorry

-- #check 0 #exit

-- example {a b c : ℝ}
-- (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c)
-- (ha₂ : 0 ≤ a) (hb₂ : 0 ≤ b) (hc₂ : 0 ≤ c)
-- (ha₃ : 0 ≠ a) (hb₃ : 0 ≠ b) (hc₃ : 0 ≠ c)
-- :
-- a / (a / b) = b := by
--   exact?

-- #check 0 #exit

open scoped Classical in noncomputable
def bwLimit (a : ℕ → ℝ) (M : ℚ) (h : boundedBy a M) : ℝ :=
  Real.mk # .mk (bwSeq a (-(M + 1)) (M + 1) · |>.1) # by
  apply isCauSeq_bwSeq h <;> norm_cast <;> linarith

-- #check 0 #exit

theorem exi_subseq_tendsTo_of_bounded {a} (h : bounded a) :
∃ σ L, subseq σ ∧ tendsTo (a ∘ σ) L := by
  obtain ⟨M', h⟩ := h
  unfold boundedBy at h
  obtain ⟨M, h₁⟩ := exists_rat_gt M'
  replace h : ∀ n, |a n| ≤ M
  · intro n; specialize h n; linarith
  clear! M'
  sorry