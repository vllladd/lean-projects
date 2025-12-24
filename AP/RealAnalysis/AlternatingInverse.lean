import AP.RealAnalysis.ConditionalConvergence

namespace RealAnalysis

noncomputable
def altInv (n : ℕ) : ℝ :=
  (-1) ^ n * (n + 1 : ℝ)⁻¹

-----

@[simp]
theorem altInv_zero : altInv 0 = 1 := by
  simp [altInv]

@[simp]
theorem altInv_one : altInv 1 = -2⁻¹ := by
  simp [altInv]; norm_num

theorem tendsTo_zero_iff_abs_tendsTo {a} : tendsTo a 0 ↔ tendsTo |a| 0 := by
  constructor
  · nth_rw 2 [←abs_zero]; exact tendsTo_abs
  · exact tendsTo_zero_of_abs_tendsTo

@[simp]
theorem abs_altInv {n} : |altInv n| = (n + 1 : ℝ)⁻¹ := by
  simp [altInv]; norm_cast; simp

@[simp]
theorem altInv_tendsTo_zero : tendsTo altInv 0 := by
  apply tendsTo_zero_of_abs_tendsTo; simp

@[simp]
theorem converges_altInv : converges altInv :=
  ⟨_, altInv_tendsTo_zero⟩

@[simp]
theorem converges_series_altInv : converges (series altInv) := by
  apply converges_series_alternating_of_monoGe _ # by simp
  intro i j h; simp; field_simp; norm_cast; omega

theorem converges_series_fn_mul_two_of_nonneg {a L}
(h₁ : ∀ n, 0 ≤ a n) (h₂ : tendsTo (series a) L) :
converges # series (a # · * 2) := by
  apply converges_of_monoLe_and_bounded_top
  · apply monoLe_series_of_nonneg; grind
  use L
  intro n
  simp [series]
  have h₃ : series a (n * 2) ≤ L
  · apply le_limit_of_monoLe _ h₂
    apply monoLe_series_of_nonneg; grind
  simp [series] at h₃
  apply h₃.trans'
  clear h₃
  induction n; simp
  nm n ih
  simp [Finset.sum_range_succ, Nat.add_mul]
  grind

theorem converges_series_fn_mul_two_add_one_of_nonneg {a L}
(h₁ : ∀ n, 0 ≤ a n) (h₂ : tendsTo (series a) L) :
converges # series (a # · * 2 + 1) := by
  apply converges_of_monoLe_and_bounded_top
  · apply monoLe_series_of_nonneg; grind
  use L
  intro n
  simp [series]
  have h₃ : series a (n * 2) ≤ L
  · apply le_limit_of_monoLe _ h₂
    apply monoLe_series_of_nonneg; grind
  simp [series] at h₃
  apply h₃.trans'
  clear h₃
  induction n; simp
  nm n ih
  simp [Finset.sum_range_succ, Nat.add_mul]
  grind

theorem tendsTo_of_bounded_top {a L} (h₂ : ∀ n, a n ≤ L)
(h₃ : ∀ (ε : ℝ), 0 < ε → eventually λ n => L - ε < a n) : tendsTo a L := by
  intro e he
  specialize h₃ e he
  choose N h₃ using h₃
  use N
  intro n hn
  specialize h₃ n hn
  rw [abs_lt]
  grind

theorem tendsTo_of_bounded_bottom {a L} (h₂ : ∀ n, L ≤ a n)
(h₃ : ∀ (ε : ℝ), 0 < ε → eventually λ n => a n < L + ε) : tendsTo a L := by
  intro e he
  specialize h₃ e he
  choose N h₃ using h₃
  use N
  intro n hn
  specialize h₃ n hn
  rw [abs_lt]
  grind

theorem tendsTo_iff_bounded_top {a L} (h : ∀ n, a n ≤ L) :
tendsTo a L ↔ ∀ (ε : ℝ), 0 < ε → eventually λ n => L - ε < a n := by
  symm; use tendsTo_of_bounded_top h
  intro h₁ e he
  specialize h₁ e he
  choose N h₁ using h₁
  use N
  intro n hn
  specialize h₁ n hn
  rw [abs_lt] at h₁
  grind

theorem tendsTo_iff_bounded_bottom {a L} (h : ∀ n, L ≤ a n) :
tendsTo a L ↔ ∀ (ε : ℝ), 0 < ε → eventually λ n => a n < L + ε := by
  symm; use tendsTo_of_bounded_bottom h
  intro h₁ e he
  specialize h₁ e he
  choose N h₁ using h₁
  use N
  intro n hn
  specialize h₁ n hn
  rw [abs_lt] at h₁
  grind

theorem tendsTo_series_fn_add {a L} (h₂ : tendsTo (series a) L) :
tendsTo (series # λ n => a (n * 2) + a (n * 2 + 1)) L := by
  unfold series
  simp [Finset.sum_add_distrib]
  convert_to tendsTo (series a # · * 2) L
  · ext n
    simp [series]
    induction n; simp
    nm n ih
    simp [Finset.sum_range_succ, Nat.add_mul]
    grind
  apply tendsTo_subseq (a := series a) (σ := (· * 2)) h₂
  simp [Subseq]

theorem exi_tendsTo_series_fn_add_of_nonneg {a L} (h₂ : tendsTo (series a) L) (h₁ : ∀ n, 0 ≤ a n) :
∃ L₁ L₂, L₁ + L₂ = L ∧ tendsTo (series (a # · * 2)) L₁ ∧ tendsTo (series (a # · * 2 + 1)) L₂ := by
  have h₃ := tendsTo_series_fn_add h₂
  choose L₁ h₄ using converges_series_fn_mul_two_of_nonneg h₁ h₂
  choose L₂ h₅ using converges_series_fn_mul_two_add_one_of_nonneg h₁ h₂
  have h₆ := tendsTo_add h₄ h₅
  refine ⟨L₁, L₂, ?_, h₄, h₅⟩
  apply tendsTo_unique h₆
  convert h₃ using 1
  ext n
  simp [series]
  induction n; simp
  nm n ih
  simp [Finset.sum_range_succ]
  grind

theorem series_smul {a : ℕ → ℝ} {x} : series (a · * x) = λ n => series a n * x := by
  ext; simp [series]; symm; apply Finset.sum_mul

theorem series_sdiv {a : ℕ → ℝ} {x} : series (a · / x) = λ n => series a n / x :=
  series_smul

theorem tendsTo_smul {a L x} (h : tendsTo a L) : tendsTo (a · * x) (L * x) := by
  apply tendsTo_mul h; simp

theorem tendsTo_sdiv {a L x} (h : tendsTo a L) : tendsTo (a · / x) (L / x) :=
  tendsTo_smul h

theorem exi_tendsTo_le_of_monoLe_and_forall_le {a b L} (h₁ : tendsTo b L)
(h₂ : monoLe a) (h₃ : ∀ n, a n ≤ b n) : ∃ M, M ≤ L ∧ tendsTo a M := by
  choose M h₄ using converges_of_monoLe_and_forall_le ⟨_, h₁⟩ h₂ h₃
  exact ⟨M, limit_le_limit_of_forall_le h₄ h₁ h₃, h₄⟩

theorem series_fn_add {a b} : series (a + b) = series a + series b := by
  ext; simp [series, Finset.sum_add_distrib]

@[simp]
theorem series_one {a} : series a 1 = a 0 := by
  simp [series]

theorem exi_series_tendsTo_lt_of_forall_lt {a b L} (h₁ : tendsTo (series b) L)
(h₂ : ∀ n, 0 ≤ b n) (h₃ : ∀ n, 0 ≤ a n) (h₄ : ∀ n, a n < b n) :
∃ M, M < L ∧ tendsTo (series a) M := by
  replace h₄ : ∀ n, ∃ c, 0 < c ∧ a n + c = b n
  · intro n
    specialize h₄ n
    use b n - a n
    split_ands <;> linarith
  choose c h₄ h₅ using h₄
  replace h₅ : b = a + c
  · ext n; rw [←h₅]; rfl
  subst h₅
  simp at h₂
  rw [series_fn_add] at h₁
  obtain ⟨M, h₅⟩ : converges # series a
  · apply converges_of_monoLe_and_forall_le ⟨_, h₁⟩ # monoLe_series_of_nonneg h₃
    intro n
    simp [series]
    apply Finset.sum_nonneg
    intro k hk
    exact le_of_lt # h₄ _
  refine ⟨M, ?_, h₅⟩
  have h₆ : tendsTo (series c) (L - M)
  · rw [show series c = series a + series c - series a by simp]
    exact tendsTo_sub h₁ h₅
  suffices : 0 < L - M; linarith
  apply lt_of_lt_of_le (b := series c 1)
  · simp; apply h₄
  apply le_limit_of_monoLe _ h₆
  apply monoLe_series_of_nonneg
  intro n; exact le_of_lt # h₄ _

@[simp]
theorem not_converges_series_inv : ¬converges (series (λ n => (n + 1 : ℝ)⁻¹)) := by
  rintro ⟨L, h⟩
  choose L₁ L₂ h₁ h₂ h₃ using exi_tendsTo_series_fn_add_of_nonneg h # λ _ => by positivity
  replace h₃ : tendsTo (series λ n => (n + 1 : ℝ)⁻¹ / 2) L₂
  · convert h₃ using 2
    ext n
    field_simp
    norm_cast
    ring_nf
  rw [series_sdiv] at h₃
  obtain rfl := tendsTo_unique h₃ # tendsTo_sdiv h (x := 2)
  replace h₁ : L₁ = L / 2; linarith
  subst h₁
  have h₁ : tendsTo (series λ n => 2 / (n * 2 + 1)) L
  · replace h₂ := tendsTo_smul h₂ (x := 2)
    simp [div_eq_inv_mul, series_smul]
    simp at h₂ ⊢
    exact h₂
  clear h₂ h₃
  replace h₁ : ∃ M, M < L ∧ tendsTo (series λ n => 2 / (n * 2 + 2)) M
  · apply exi_series_tendsTo_lt_of_forall_lt h₁
    · intro n
      field_simp
      simp
    · intro n
      positivity
    · intro n
      field_simp
      norm_cast
      omega
  choose M h₁ h₂ using h₁
  replace h₂ : tendsTo (series λ n => (n + 1 : ℝ)⁻¹) M
  · convert h₂ using 2; ext n; field_simp
  contrapose! h₁; clear h₁
  apply le_of_eq
  exact tendsTo_unique h h₂

@[simp]
theorem not_absConv_altInv : ¬AbsConv altInv := by
  simp [AbsConv]

@[simp]
theorem condConv_altInv : CondConv altInv :=
  ⟨converges_series_altInv, not_absConv_altInv⟩