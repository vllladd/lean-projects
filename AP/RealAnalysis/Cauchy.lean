import AP.RealAnalysis.Monotonicity

namespace RealAnalysis

def isCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i j, N ≤ i → N ≤ j → |a i - a j| < ε

def isCauchyAlt₁ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |a n - a N| < ε

def isCauchyAlt₂ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i, N ≤ i → ∀ j, N ≤ j → |a i - a j| < ε

def isCauchyAlt₃ (a : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ i, N ≤ i → ∀ j, i ≤ j → |a i - a j| < ε

theorem isCauchy_iff_isCauchyAlt₁ {a} : isCauchy a ↔ isCauchyAlt₁ a := by
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

theorem isCauchy_iff_isCauchyAlt₂ {a} : isCauchy a ↔ isCauchyAlt₂ a := by
  constructor; all_goals
    intro h e he
    specialize h e he
    obtain ⟨N, h⟩ := h
    use N
    tauto

theorem isCauchy_iff_isCauchyAlt₃ {a} : isCauchy a ↔ isCauchyAlt₃ a := by
  rw [isCauchy_iff_isCauchyAlt₂]; constructor
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

theorem isCauSeq_iff_isCauchy {a : ℕ → ℚ} : IsCauSeq abs a ↔ isCauchy (a ·) := by
  rw [isCauchy_iff_isCauchyAlt₁]
  constructor <;> intro h e (he : 0 < e)
  · obtain ⟨e', he', h₁⟩ := exists_pos_rat_lt he
    specialize h e' he'
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h n hn
    dsimp
    apply h₁.trans'
    exact_mod_cast h
  · specialize h e # by exact_mod_cast he
    obtain ⟨N, h⟩ := h
    use N
    intro n hn
    specialize h n hn
    dsimp at h
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
  rw [isCauchy_iff_isCauchyAlt₁]
  obtain ⟨L, h⟩ := h
  intro e he
  specialize h (e / 2) (by positivity)
  obtain ⟨N, h⟩ := h
  use N
  dsimp at h
  intro n hn
  exact Real.abs_sub_lt_of_lt_lt_half (h n hn) # h N # by rfl

theorem bounded_of_isCauchy {a} (h : isCauchy a) : bounded a := by
  rw [isCauchy_iff_isCauchyAlt₁] at h
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

theorem tendsTo_of_isCauchy_and_subseq_tendsTo {a σ L}
(hσ : subseq σ) (ha : isCauchy a) (h : tendsTo (a ∘ σ) L) : tendsTo a L := by
  intro e he
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
  push_neg
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
  rw [isCauchy_iff_isCauchyAlt₁]
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

theorem isCauSeq_rat_iff {a : ℕ → ℚ} : IsCauSeq abs a ↔
∀ ε, 0 < ε → ∃ N, ∀ i j, N ≤ i → N ≤ j → |a i - a j| < ε := by
  rw [isCauSeq_iff_isCauchy]
  constructor
  · intro h e he
    specialize h e # by exact_mod_cast he
    obtain ⟨N, h⟩ := h
    use N
    intro i j hi hj
    specialize h i j hi hj
    replace h : ((|a i - a j| : ℚ) : ℝ) < e; simpa
    exact_mod_cast h
  · intro h e he
    obtain ⟨e', he₁, he₂⟩ := exists_rat_btwn he
    simp at he₁
    specialize h e' he₁
    obtain ⟨N, h⟩ := h
    use N
    intro i j hi hj
    specialize h i j hi hj
    dsimp
    apply he₂.trans'
    exact_mod_cast h

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
  push_neg at h₂
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
  push_neg at he
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

/- todo:
* τ σ iterate_gap non-subseqs
* for each real number x there is a monoLt rat seq that converges to x
* 1, 1.4, 1.41, 1.412 ... -> sqrt 2
-/