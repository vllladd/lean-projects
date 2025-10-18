import AP.RealAnalysis.Monotonicity

theorem abs_sub_lt_trans {a c e : ℝ} (b : ℝ)
(h : |a - b| + |b - c| < e) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans {a c e : ℝ} (b : ℝ)
(h : |a - b| + |b - c| ≤ e) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_lt_trans_half {a c e : ℝ} (b : ℝ)
(h₁ : |a - b| < e / 2) (h₂ : |b - c| < e / 2) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans_half {a c e : ℝ} (b : ℝ)
(h₁ : |a - b| ≤ e / 2) (h₂ : |b - c| ≤ e / 2) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

-- #check 0 #exit

namespace Real

theorem sqrt_add_one_sub_lt_one {x} (hx : 0 < x) : √(x + 1) - √x < 1 := by
  have h₁ : √x < √(x + 1); rw [sqrt_lt_sqrt_iff] <;> linarith
  rw [←sq_lt_sq₀, sub_sq, sq_sqrt, sq_sqrt] <;> try first | positivity | linarith
  suffices H : x < √(x + x ^ 2)
  · rw [mul_assoc, ←sqrt_mul'] <;> try positivity
    ring_nf at H ⊢; linarith
  rw [lt_sqrt] <;> try positivity;; simpa

@[simp]
theorem abs_sqrt {x : ℝ} : |√x| = √x := by
  rw [abs_of_nonneg]; positivity

theorem abs_sub_lt_of_lt_lt_half {a b c d : ℝ}
(h₁ : |a - c| < d / 2) (h₂ : |b - c| < d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_lt_of_le_lt_half {a b c d : ℝ}
(h₁ : |a - c| ≤ d / 2) (h₂ : |b - c| < d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_lt_of_lt_le_half {a b c d : ℝ}
(h₁ : |a - c| < d / 2) (h₂ : |b - c| ≤ d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_le_of_le_le_half {a b c d : ℝ}
(h₁ : |a - c| ≤ d / 2) (h₂ : |b - c| ≤ d / 2) : |a - b| ≤ d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ ≤ _ := by linarith

-- #check 0 #exit

theorem abs_mk_sub_le {a : ℕ → ℚ} {x e : ℝ} (ha : IsCauSeq abs a)
(h : ∃ N, ∀ n, N ≤ n → |a n - x| < e) : |mk ⟨a, ha⟩ - x| ≤ e := by
  obtain ⟨N, h⟩ := h
  by_cases he : e ≤ 0
  · specialize h N (by rfl)
    contrapose! h
    apply he.trans
    simp
  push_neg at he
  
  rw [abs_le]
  constructor
  
  · suffices H : x - e ≤ mk ⟨a, ha⟩; linarith
    sorry
  
  · sorry

-- #check 0 #exit

end Real

namespace RealAnalysis

def isCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - a N| < ε

theorem isCauchy_iff_isCauSeq {a : ℕ → ℚ} : isCauchy (a ·) ↔ IsCauSeq abs a := by
  constructor <;> intro h e (he : 0 < e)
  · specialize h e # by exact_mod_cast he
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h
    specialize h n hn
    dsimp at h
    exact_mod_cast h
  · obtain ⟨e', he', h₁⟩ := exists_pos_rat_lt he
    specialize h e' he'
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h n hn
    dsimp
    apply h₁.trans'
    exact_mod_cast h

theorem forall_epsilon_iff {p : ℝ → Prop}
(h : ∀ {ε₁ ε₂}, 0 < ε₁ → ε₁ < ε₂ → p ε₁ → p ε₂) :
(∀ ε, 0 < ε → p ε) ↔ ∀ ε, 0 < ε → ε < 1 → p ε := by
  use λ h e he he' => h e he
  intro h₁ e he
  specialize h₁ (min e e⁻¹ / 2) (by positivity) _
  · rw [min_eq_ite]
    split_ifs with h₁ <;> contrapose! h₁
    · replace h₁ : 1 < e; linarith
      exact Real.inv_lt_self_of_one_lt h₁
    replace h₁ : 1 ≤ e⁻¹; linarith
    replace h₁ : e ≤ 1; rwa [←one_le_inv₀ he]
    exact Real.le_inv_self_of he h₁
  apply h (by positivity) _ h₁
  rw [div_lt_iff₀ # by norm_num]
  simp; left; linarith

theorem isCauchy_iff {a} : isCauchy a ↔ ∀ ε, 0 < ε → ε < 1 →
∃ N, ∀ n, N ≤ n → |a n - a N| < ε := by
  apply forall_epsilon_iff; rintro e₁ e₂ h₁ h₂ ⟨N, h⟩
  use N; intro n hn; linarith [h n hn]

def isFakeCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i, N ≤ i → |a i - a (i + 1)| < ε

theorem isFakeCauchy_iff {a} : isFakeCauchy a ↔ ∀ ε, 0 < ε → ε < 1 →
∃ N, ∀ i, N ≤ i → |a i - a (i + 1)| < ε := by
  apply forall_epsilon_iff; rintro e₁ e₂ h₁ h₂ ⟨N, h⟩
  use N; intro n hn; linarith [h n hn]

theorem isFakeCauchy_sqrt : isFakeCauchy (√·) := by
  rw [isFakeCauchy_iff]
  intro e he he'
  obtain ⟨N, hN⟩ := exists_nat_gt # ((1 - e ^ 2) / (2 * e)) ^ 2
  use N
  rintro n hn
  rw [abs_of_neg # by simp]
  simp
  replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
  replace hN : ((1 - e ^ 2) / (2 * e)) ^ 2 < n; linarith
  clear! N
  have h₁ : √(n : ℝ) ≤ √(n + 1)
  · rw [Real.sqrt_le_sqrt_iff] <;> linarith
  rw [←sq_lt_sq₀, sub_sq, mul_assoc, ←Real.sqrt_mul', Real.sq_sqrt, Real.sq_sqrt]
    <;> try first | positivity | linarith
  suffices H : 2 * n + 1 - e ^ 2 < 2 * √(n + n ^ 2)
  · ring_nf at H ⊢; linarith
  rw [←sq_lt_sq₀] <;> try positivity
  rotate_left; simp; trans e <;> nlinarith
  rw [mul_pow, Real.sq_sqrt] <;> try positivity
  rw [div_pow, div_lt_iff₀] at hN <;> try positivity
  ring_nf at hN ⊢
  linarith

theorem isCauchy_of_converges {a} (h : converges a) : isCauchy a := by
  obtain ⟨L, h⟩ := h
  intro e he
  specialize h (e / 2) (by positivity)
  obtain ⟨N, h⟩ := h
  use N
  dsimp at h
  intro n hn
  exact Real.abs_sub_lt_of_lt_lt_half (h n hn) # h N # by rfl

theorem bounded_of_isCauchy {a} (h : isCauchy a) : bounded a := by
  specialize h 1 # by norm_num
  obtain ⟨N, h⟩ := h
  use 1 + |a N| + ∑ i ∈ Finset.range N, |a i|
  intro n
  have h₁ : 0 ≤ ∑ i ∈ Finset.range N, |a i|; positivity
  by_cases hn : n < N
  · have h₂ : |a n| ≤ ∑ i ∈ Finset.range N, |a i|
    · exact Finset.le_sum_range hn
    suffices h₃ : 0 ≤ 1 + |a N|; linarith
    positivity
  push_neg at hn
  specialize h n hn
  suffices : |a n| - |a N| < 1; linarith
  apply lt_of_le_of_lt _ h
  apply abs_sub_abs_le_abs_sub

def isCauchyAlt₁ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i j, N ≤ i → N ≤ j → |a i - a j| < ε

def isCauchyAlt₂ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i, N ≤ i → ∀ j, N ≤ j → |a i - a j| < ε

def isCauchyAlt₃ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i, N ≤ i → ∀ j, i ≤ j → |a i - a j| < ε

theorem isCauchyAlt₁_iff_isCauchy {a} : isCauchyAlt₁ a ↔ isCauchy a := by
  constructor <;> intro h e he
  · specialize h e he
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h N n (by rfl) hn
    rwa [abs_sub_comm]
  · specialize h (e / 2) # by positivity
    obtain ⟨N, h⟩ := h
    use N
    intro i j hi hj
    exact Real.abs_sub_lt_of_lt_lt_half (h i hi) (h j hj)

theorem isCauchyAlt₂_iff_isCauchy {a} : isCauchyAlt₂ a ↔ isCauchy a := by
  rw [←isCauchyAlt₁_iff_isCauchy]
  constructor; all_goals
    intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    use N
    tauto

theorem isCauchyAlt₃_iff_isCauchy {a} : isCauchyAlt₃ a ↔ isCauchy a := by
  rw [←isCauchyAlt₂_iff_isCauchy]
  symm; constructor
  all_goals
    intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    use N
    intro i hi j hj
  exact h i hi j (by linarith)
  specialize h (min i j) (Nat.le_min_of_le_of_le hi hj)
    (max i j) (inf_le_sup)
  by_cases h₁ : i ≤ j
  · rw [min_eq_left h₁, max_eq_right h₁] at h; exact h
  · replace h₁ : j ≤ i; linarith
    rw [min_eq_right h₁, max_eq_left h₁, abs_sub_comm] at h; exact h

theorem tendsTo_of_isCauchy_and_subseq_tendsTo {a σ L}
(hσ : subseq σ) (ha : isCauchy a) (h : tendsTo (a ∘ σ) L) : tendsTo a L := by
  intro e he
  rw [←isCauchyAlt₁_iff_isCauchy] at ha
  specialize ha (e / 2) # by positivity
  obtain ⟨N₁, ha⟩ := ha
  specialize h (e / 2) # by positivity
  obtain ⟨N₂, h⟩ := h
  use N₁ + N₂
  intro n hn
  have h₁ : N₁ + N₂ ≤ σ (N₁ + N₂) := nat_le_of_subseq hσ
  apply abs_sub_lt_trans_half # a # σ # N₁ + N₂
  · apply ha <;> linarith
  · apply h; linarith

theorem tendsTo_of_converges_and_subseq_tendsTo {a σ L}
(hσ : subseq σ) (ha : converges a) (h : tendsTo (a ∘ σ) L) : tendsTo a L :=
  tendsTo_of_isCauchy_and_subseq_tendsTo hσ (isCauchy_of_converges ha) h

theorem converges_of_isCauchy {a} (h : isCauchy a) : converges a := by
  have h₁ := bounded_of_isCauchy h
  obtain ⟨σ, L, hσ, h₂⟩ := exi_subseq_tendsTo_of_bounded h₁
  use L, tendsTo_of_isCauchy_and_subseq_tendsTo hσ h h₂

theorem isCauchy_iff_converges {a} : isCauchy a ↔ converges a :=
  ⟨converges_of_isCauchy, isCauchy_of_converges⟩

theorem converges_iff_isCauchy {a} : converges a ↔ isCauchy a :=
  isCauchy_iff_converges.symm

theorem not_converges_sqrt : ¬converges (√·) := by
  unfold converges tendsTo eventually
  push_neg; simp
  intro L
  use 1, by norm_num
  intro N
  by_cases hL : L = 0
  · subst hL
    use N + 1
    simp
  obtain ⟨n, hn⟩ := exists_nat_gt # N + L ^ 2 + |L| * 2 + 2
  have hn' : N + L ^ 2 + 2 < n
  · apply hn.trans'; simpa
  use n
  constructor
  · suffices H : (N : ℝ) ≤ n; exact_mod_cast H; nlinarith
  rw [le_abs]; left
  rw [le_sub_iff_add_le]
  have h₁ : 1 < √n
  · rw [Real.lt_sqrt, one_pow] <;> try positivity;; nlinarith
  clear hL
  by_cases hL : L < 0; linarith
  push_neg at hL
  rw [←sq_le_sq₀, Real.sq_sqrt, add_sq] <;> try positivity
  simp
  apply le_of_lt
  apply hn.trans'
  rw [abs_of_nonneg hL]
  linarith

theorem not_isCauchy_sqrt : ¬isCauchy (√·) := by
  rw [isCauchy_iff_converges]; exact not_converges_sqrt

theorem isFakeCauchy_ne_isCauchy : isFakeCauchy ≠ isCauchy := by
  apply ne_of_congr (· (√·)); simp; push_neg; left
  use isFakeCauchy_sqrt, not_isCauchy_sqrt

theorem isCauchy_add {a b} (ha : isCauchy a) (hb : isCauchy b) : isCauchy (a + b) := by
  rw [isCauchy_iff_converges] at ha hb ⊢; exact converges_add ha hb

@[simp]
theorem isCauchy_neg {a} : isCauchy (-a) ↔ isCauchy a := by
  simp [isCauchy_iff_converges]

theorem isCauchy_of_monoLe_and_bounded_top {a}
(h₁ : monoLe a) (h₂ : ∃ M, ∀ n, a n ≤ M) : isCauchy a := by
  intro e he
  have h₃ := λ n => le_lub_of_bounded_top (n := n) h₂
  obtain ⟨N, h₄⟩ := exi_lub_sub_lt_of_bounded_top h₂ he
  use N
  intro n hN
  have h₅ : a N ≤ a n := h₁ _ _ hN
  rw [abs_of_nonneg # by linarith]
  linarith [h₃ n]

theorem isCauchy_of_monoGe_and_bounded_bottom {a}
(h₁ : monoGe a) (h₂ : ∃ M, ∀ n, M ≤ a n) : isCauchy a := by
  rw [←monoLe_neg] at h₁
  replace h₂ : ∃ M, ∀ n, (-a) n ≤ M
  · dsimp; obtain ⟨M, h₂⟩ := h₂; use -M
    intro n; linarith [h₂ n]
  rw [←isCauchy_neg]
  exact isCauchy_of_monoLe_and_bounded_top h₁ h₂

theorem isCauchy_of_monoLt_and_bounded_top {a}
(h₁ : monoLt a) (h₂ : ∃ M, ∀ n, a n ≤ M) : isCauchy a :=
  isCauchy_of_monoLe_and_bounded_top (monoLe_of_monoLt h₁) h₂

theorem isCauchy_of_monoGt_and_bounded_bottom {a}
(h₁ : monoGt a) (h₂ : ∃ M, ∀ n, M ≤ a n) : isCauchy a :=
  isCauchy_of_monoGe_and_bounded_bottom (monoGe_of_monoGt h₁) h₂

theorem converges_of_monoLe_and_bounded_top {a}
(h₁ : monoLe a) (h₂ : ∃ M, ∀ n, a n ≤ M) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoLe_and_bounded_top h₁ h₂

theorem converges_of_monoGe_and_bounded_bottom {a}
(h₁ : monoGe a) (h₂ : ∃ M, ∀ n, M ≤ a n) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoGe_and_bounded_bottom h₁ h₂

theorem converges_of_monoLt_and_bounded_top {a}
(h₁ : monoLt a) (h₂ : ∃ M, ∀ n, a n ≤ M) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoLt_and_bounded_top h₁ h₂

theorem converges_of_monoGt_and_bounded_bottom {a}
(h₁ : monoGt a) (h₂ : ∃ M, ∀ n, M ≤ a n) : converges a := by
  rw [converges_iff_isCauchy]; exact isCauchy_of_monoGt_and_bounded_bottom h₁ h₂

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
  apply Real.abs_mk_sub_le
  use N
  intro n₁ h₁
  have h₂ := h n # by linarith
  have h₃ := h n₁ # by linarith
  replace h₂ : |(a n : ℝ) - a N| < e / 2 / 2
  · trans (e' : ℝ); exact_mod_cast h₂; linarith
  replace h₃ : |(a n₁ : ℝ) - a N| < e / 2 / 2
  · trans (e' : ℝ); exact_mod_cast h₃; linarith
  exact Real.abs_sub_lt_of_lt_lt_half h₃ h₂

/- todo:
* 1, 1.4, 1.41, 1.412 ... -> sqrt 2
-/