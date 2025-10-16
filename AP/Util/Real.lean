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

-----

theorem exi_mk_cauchy {x : ℝ} : ∃ (a : ℕ → ℚ) (ha : IsCauSeq abs a), x = .mk ⟨a, ha⟩ := by
  rcases x with ⟨⟨a, ha⟩⟩; use a, ha; rfl

theorem _root_.IsCauSeq.sub {a b : ℕ → ℚ}
(ha : IsCauSeq abs a) (hb : IsCauSeq abs b) : IsCauSeq abs (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem mk_sub_mk {a b : ℕ → ℚ} {ha : IsCauSeq abs a} {hb : IsCauSeq abs b} :
mk ⟨a, ha⟩ - mk ⟨b, hb⟩ = mk ⟨a - b, ha.sub hb⟩ := by
  rw [←ofCauchy_sub]; rfl

theorem _root_.IsCauSeq.abs' {a : ℕ → ℚ} (ha : IsCauSeq abs a) : IsCauSeq abs |a| := by
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, ha⟩ := ha
  use N
  intro n hn
  specialize ha n hn
  simp
  exact lt_of_le_of_lt (abs_abs_sub_abs_le _ _) ha

theorem neg_mk {a : ℕ → ℚ} {ha : IsCauSeq abs a} : -mk ⟨a, ha⟩ = mk ⟨-a, ha.neg⟩ := by
  rw [←ofCauchy_neg]; rfl

theorem abs_mk {a : ℕ → ℚ} {ha : IsCauSeq abs a} : |mk ⟨a, ha⟩| = mk ⟨|a|, ha.abs'⟩ := by
  change max _ _ = _; rw [neg_mk]; exact ofCauchy_sup _ _ |>.symm

example : ¬∀ {a : ℕ → ℚ} (ha : IsCauSeq abs a) (N : ℕ) (b : ℕ → ℚ)
(hb : IsCauSeq abs b) (h : ∀ (n : ℕ), N ≤ n → ∃ x, 0 < x ∧
∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a n + b j),
∃ (x : ℚ), 0 < x ∧ ∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a j + b j := by
  push_neg
  use λ n => (n + 1)⁻¹
  constructor
  · intro e he
    obtain ⟨n, hn⟩ := exists_nat_gt e⁻¹
    use n
    intro j hj
    simp
    rw [abs_of_nonpos]
    rotate_left
    · simp
      replace hj : (n : ℚ) + 1 ≤ j + 1; simpa
      rwa [inv_le_inv₀] <;> positivity
    simp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
    clear hj
    field_simp
    replace hn : (n + 1 : ℚ)⁻¹ < e⁻¹
    · trans (e + 1)⁻¹
      rotate_left
      · rw [inv_lt_inv₀] <;> try positivity
        linarith
      rw [inv_lt_inv₀] <;> try positivity
      simp
      sorry
    sorry
  use 0
  use λ _ => 0
  constructor
  · intro e he
    simp
    use 0
    simpa
  simp
  constructor
  · intro N
    use (N + 1 : ℚ)⁻¹
    simp
    positivity
  intro x hx i
  obtain ⟨n, hn⟩ := exists_nat_gt x⁻¹
  use n + i, by linarith
  simp
  have h : (n : ℚ) < n + i + 1; linarith
  rw [inv_lt_comm₀] <;> try positivity
  apply h.trans'
  exact hn

-- example : ¬∀ {a : ℕ → ℚ} {x ε : ℝ} (ha : IsCauSeq abs a)
-- (h : ∃ N, ∀ n, N ≤ n → |a n - x| < ε), |x - (.mk ⟨a, ha⟩)| < ε := by
--   push_neg
-- 
-- #check 0 #exit

theorem abs_sub_cauchy_lt_of_exi {a : ℕ → ℚ} {x ε : ℝ} (ha : IsCauSeq abs a)
(h : ∃ N, ∀ n, N ≤ n → |a n - x| < ε) : |x - (.mk ⟨a, ha⟩)| < ε := by
  rw [abs_sub_comm]
  obtain ⟨N, h⟩ := h
  obtain ⟨b, hb, rfl⟩ := x.exi_mk_cauchy
  rw [mk_sub_mk]
  simp_rw [abs_lt] at h ⊢
  constructor
  · obtain ⟨e, he, H⟩ := (-ε).exi_mk_cauchy
    rw [neg_eq_iff_eq_neg] at H
    subst H
    simp at h ⊢
    change ∃ _, _
    simp
    
    -- specialize h N (by rfl)
    -- replace h := h.1
    -- change mk _ < mk ⟨_, _⟩ - _ at h
    -- rw [mk_sub_mk] at h
    -- simp at h
    -- 
    -- obtain ⟨x, hx, n, h⟩ := h
    -- simp at h
    -- 
    -- rename' b => b', hb => hb'
    -- generalize h₁ : -b' - e = b
    -- have hb : IsCauSeq abs b
    -- · rw [←h₁]; exact hb'.neg.sub he
    -- replace h₁ : b' = -b - e; simp [←h₁]
    -- subst h₁; clear hb'
    -- 
    -- have h₁ : ∀ (x : ℚ) i, x - (-b i - e i) - e i = x + b i
    -- · intros; ring_nf
    -- simp [h₁] at h ⊢; clear h₁; clear! e
    -- 
    -- have h₁ : 0 < x / 3; positivity
    -- use x / 3, h₁
    -- 
    -- specialize ha _ h₁
    -- specialize hb _ h₁
    -- 
    -- obtain ⟨N₁, ha⟩ := ha
    -- obtain ⟨N₂, hb⟩ := hb
    
    replace h : ∀ n, N ≤ n → mk ⟨e, he⟩ < ↑(a n) - mk ⟨b, hb⟩
    · intro n hn; specialize h n hn; exact h.1
    change ∀ n, N ≤ n → mk ⟨e, he⟩ < mk ⟨_, _⟩ - mk ⟨b, hb⟩ at h
    simp [mk_sub_mk] at h
    change ∀ n, N ≤ n → ∃ _, _ at h
    simp at h
    
    rename' b => b', hb => hb'
    generalize h₁ : -b' - e = b
    have hb : IsCauSeq abs b
    · rw [←h₁]; exact hb'.neg.sub he
    replace h₁ : b' = -b - e; simp [←h₁]
    subst h₁; clear hb'
    
    have h₁ : ∀ (x : ℚ) i, x - (-b i - e i) - e i = x + b i
    · intros; ring_nf
    simp [h₁] at h ⊢; clear h₁; clear! e
    
    sorry
  · sorry