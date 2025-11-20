import AP.RealAnalysis.Coherence

namespace RealAnalysis

def Rment (σ : ℕ → ℕ) : Prop :=
  σ.Bijective

noncomputable
def rinv (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon # λ k => σ k = n

theorem rment_eq_iff {σ n m} (h : Rment σ) : σ n = σ m ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁; exact h.1 h₁

theorem rinv_cancel_left {σ n} (h : Rment σ) : rinv σ (σ n) = n := by
  simp [rinv, rment_eq_iff h]

theorem rinv_cancel_right {σ n} (h : Rment σ) : σ (rinv σ n) = n := by
  unfold rinv
  apply Classical.epsilon_spec (p := λ k => σ k = n)
  apply h.2

theorem rment_rinv {σ} (h : Rment σ) : Rment (rinv σ) := by
  constructor
  · intro n m h₁
    replace h₁ := congrArg σ h₁
    simp_rw [rinv_cancel_right h] at h₁
    exact h₁
  · intro n
    use σ n
    rw [rinv_cancel_left h]

theorem tendsTo_rment_of {a σ L} (h₁ : Rment σ)
(h₂ : tendsTo a L) : tendsTo (a # σ ·) L := by
  intro e he
  dsimp
  specialize h₂ e he
  choose N h₂ using h₂
  dsimp at h₂
  use ∑ i ∈ Finset.range N, rinv σ i + 1
  intro n hn
  apply h₂; clear h₂
  by_contra! h₃
  have h₄ : rinv σ (σ n) ≤ ∑ i ∈ Finset.range N, rinv σ i
  · apply Finset.le_sum_of_mem <;> simp [h₃]
  rw [rinv_cancel_left h₁] at h₄
  omega

theorem tendsTo_rment_iff {a σ L} (h₁ : Rment σ) :
tendsTo (a # σ ·) L ↔ tendsTo a L := by
  symm; use tendsTo_rment_of h₁
  intro h₂
  replace h₂ := tendsTo_rment_of (rment_rinv h₁) h₂
  simp_rw [rinv_cancel_right h₁] at h₂
  exact h₂

theorem converges_rment_of {a σ} (h₁ : Rment σ)
(h₂ : converges a) : converges (a # σ ·) := by
  choose L h₂ using h₂; use L, tendsTo_rment_of h₁ h₂

theorem converges_rment_iff {a σ} (h₁ : Rment σ) :
converges (a # σ ·) ↔ converges a := by
  apply exists_congr; simp [tendsTo_rment_iff h₁]

theorem exi_gt_of_monoLe_and_not_converges {a}
(h₁ : monoLe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, L < a N := by
  contrapose! h₂; apply converges_of_monoLe_and_bounded_top h₁ ⟨L, h₂⟩

theorem exi_lt_of_monoGe_and_not_converges {a}
(h₁ : monoGe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, a N < L := by
  contrapose! h₂; apply converges_of_monoGe_and_bounded_bottom h₁ ⟨L, h₂⟩

def CondConv (a : ℕ → ℝ) : Prop :=
  converges (series a) ∧ ¬AbsConv a

theorem absConv_drop_of {a N} (h : AbsConv a) : AbsConv (a # N + ·) := by
  unfold AbsConv at h ⊢; rwa [converges_series_drop_iff (a := (|a ·|))]

theorem absConv_drop_iff {a N} : AbsConv (a # N + ·) ↔ AbsConv a := by
  exact converges_series_drop_iff (a := (|a ·|))

theorem condConv_drop_of {a N} (h : CondConv a) : CondConv (a # N + ·) := by
  unfold CondConv at h ⊢; rwa [converges_series_drop_iff, absConv_drop_iff]

theorem condConv_drop_iff {a N} : CondConv (a # N + ·) ↔ CondConv a := by
  unfold CondConv; rw [converges_series_drop_iff, absConv_drop_iff]

theorem absConv_neg {a} : AbsConv (-a) ↔ AbsConv a := by
  simp [AbsConv]

theorem condConv_neg {a} : CondConv (-a) ↔ CondConv a := by
  unfold CondConv; rw [←neg_series', converges_neg, absConv_neg]

def Infp (a : ℕ → ℝ) (p : ℝ → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ p (a n)

theorem infp_iff_infinite {a p} : Infp a p ↔ {n | p # a n}.Infinite := by
  simp_rw [Set.infinite_iff_exists_gt, Set.mem_setOf_eq]
  constructor; all_goals
    intro h N
    specialize h # N + 1
    choose n h₁ h₂ using h
    use n, by omega, by omega

open Classical in noncomputable
def mkSubseq (a : ℕ → ℝ) (p : ℝ → Prop) (n : ℕ) : ℕ :=
  match n with
  | 0 => Nat.findRaw (p # a ·)
  | n + 1 =>
    let k := mkSubseq a p n
    k + 1 + Nat.findRaw (p # a # k + 1 + ·)

theorem subseq_mkSubseq {a p} : Subseq (mkSubseq a p) := by
  rw [subseq_iff_lt_add_one]
  intro n
  rw [mkSubseq]
  omega

theorem exi_add_of_infp {a p N} (h : Infp a p) : ∃ n, p (a # N + n) := by
  specialize h N
  choose n h₁ h₂ using h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁
  use n

theorem exi_of_infp {a p} (h : Infp a p) : ∃ n, p (a n) := by
  convert exi_add_of_infp h (N := 0); simp

theorem mkSubseq_spec {a p n} (h : Infp a p) : p # a # mkSubseq a p n := by
  cases n <;> rw [mkSubseq]
  · exact Nat.findRaw_spec (P := (p # a ·)) # exi_of_infp h
  nm n; apply Nat.findRaw_spec (P := λ k => p (a (mkSubseq a p n + 1 + k)))
  exact exi_add_of_infp h

theorem apply_of_mkSubseq_eq {a p n k} (h : Infp a p)
(h₁ : mkSubseq a p k = n) : p (a n) := by
  subst h₁; exact mkSubseq_spec h

theorem infp_drop_of {a p N} (h : Infp a p) : Infp (a # N + ·) p := by
  intro M
  specialize h (N + M)
  choose n h₁ h₂ using h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  use n + M, by omega
  ring_nf at h₂ ⊢
  exact h₂

theorem infp_of_drop {a p N} (h : Infp (a # N + ·) p) : Infp a p := by
  intro M
  specialize h M
  choose n h₁ h₂ using h
  use N + n, by omega

theorem infp_drop_iff {a p N} : Infp (a # N + ·) p ↔ Infp a p :=
   ⟨infp_of_drop, infp_drop_of⟩

theorem exi_mkSubseq_eq_of_apply {a p n} (h : Infp a p)
(h₁ : p (a n)) : ∃ k, mkSubseq a p k = n := by
  induction n using Nat.strong_induction_on generalizing a
  nm n ih
  by_cases h₂ : ∀ k < n, ¬p (a k)
  · use 0
    rw [mkSubseq]
    rw [Nat.findRaw_eq_iff, if_pos ⟨_, h₁⟩]
    exact ⟨h₁, h₂⟩
  push_neg at h₂
  replace h₂ : ∃ k, k < n ∧ p (a k) ∧ ∀ r, k < r → r < n → ¬p (a r)
  · choose k hk h₂ using h₂
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
    have h₃ : ∃ d, p # a # k + n - d
    · use n
      simpa
    replace h₃ := Nat.findRaw_spec' h₃
    generalize Nat.findRaw (λ d => p # a # k + n - d) = d at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    use k + n - d, by omega, h₃
    intro r h₅ h₆ h₇
    rw [Nat.lt_succ_iff] at h₆
    obtain ⟨w, h₈⟩ := Nat.exists_eq_add_of_le h₆
    clear h₆
    have h₆ : r = k + n - w; omega
    rw [h₆] at h₇
    specialize h₄ _ h₇
    omega
  choose k h₂ h₃ h₄ using h₂
  specialize @ih k (by omega) a h h₃
  choose i ih using ih
  use i + 1
  rw [mkSubseq, ih]; clear ih
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₂; clear h₂
  ring_nf at h₁ ⊢
  simp
  rw [Nat.findRaw_eq_iff]
  rw [if_pos ⟨_, h₁⟩]
  use h₁
  intro w hw
  apply h₄ <;> omega

theorem apply_iff_exi_mkSubseq_eq {a p n} (h : Infp a p) : p (a n) ↔ ∃ k, mkSubseq a p k = n :=
  ⟨exi_mkSubseq_eq_of_apply h, λ ⟨_, h₁⟩ => apply_of_mkSubseq_eq h h₁⟩

theorem exi_subseq_of_infp {a p} (h : Infp a p) :
∃ σ, Subseq σ ∧ ∀ n, p (a n) ↔ ∃ k, σ k = n :=
  ⟨_, subseq_mkSubseq, λ _ => apply_iff_exi_mkSubseq_eq h⟩

theorem infp_of_imp {a} {p₁ p₂ : ℝ → Prop} (h₁ : Infp a p₁)
(h₂ : ∀ n, p₁ (a n) → p₂ (a n)) : Infp a p₂ := by
  intro N; specialize h₁ N; choose n h₁ h₃ using h₁; use n, h₁, h₂ _ h₃

theorem infp_pos_of_condConv {a} (h : CondConv a) : Infp a (0 < ·) := by
  intro N
  by_contra! h₃
  generalize hb : (a # N + ·) = b
  have h₄ : CondConv b; rwa [←hb, condConv_drop_iff]
  have h₅ : |b| = -b
  · subst hb
    rw [abs_of_nonpos]
    intro n
    apply h₃
    simp
  have h₆ := h₄.1
  have h₇ : ¬converges (series b)
  · rw [←converges_neg, neg_series', ←h₅]; exact h₄.2
  contradiction

theorem infp_neg_of_condConv {a} (h : CondConv a) : Infp a (· < 0) := by
  intro N; rw [←condConv_neg] at h
  have h₁ := infp_pos_of_condConv h N
  simp at h₁; exact h₁

theorem infp_nonneg_of_condConv {a} (h : CondConv a) : Infp a (0 ≤ ·) := by
  apply infp_of_imp (infp_pos_of_condConv h); intro n; apply le_of_lt

theorem infp_nonpos_of_condConv {a} (h : CondConv a) : Infp a (· ≤ 0) := by
  apply infp_of_imp (infp_neg_of_condConv h); intro n; apply le_of_lt

theorem monoLe_series_of_nonneg {a} (h : ∀ n, 0 ≤ a n) : monoLe (series a) := by
  rw [monoLe_iff_le_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGe_series_of_nonpos {a} (h : ∀ n, a n ≤ 0) : monoGe (series a) := by
  rw [monoGe_iff_succ_le]; intro n; rw [series_succ]; linarith [h n]

theorem monoLt_series_of_pos {a} (h : ∀ n, 0 < a n) : monoLt (series a) := by
  rw [monoLt_iff_lt_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGt_series_of_neg {a} (h : ∀ n, a n < 0) : monoGt (series a) := by
  rw [monoGt_iff_succ_lt]; intro n; rw [series_succ]; linarith [h n]

theorem subseq_nat_eq_subseq_iff {σ n m} (h : Subseq σ) : σ n = σ m ↔ n = m := by
  by_cases h₁ : n < m
  · simp [ne_of_lt h₁]
    apply ne_of_lt
    apply h
    exact h₁
  push_neg at h₁
  rw [le_iff_eq_or_lt] at h₁
  rcases h₁ with rfl | h₁
  · simp
  simp [ne_symm' # ne_of_lt h₁]
  apply ne_of_gt
  apply h
  exact h₁

theorem subseq_nat_lt_subseq_iff {σ n m} (h : Subseq σ) : σ n < σ m ↔ n < m := by
  by_cases h₁ : n = m; simp [h₁]
  simp [lt_iff_le_and_ne, subseq_nat_le_subseq_iff h, subseq_nat_eq_subseq_iff h, h₁]

theorem subseq_nat_succ_le {σ n} (h : Subseq σ) : σ n + 1 ≤ σ (n + 1) := by
  simp [Nat.add_one_le_iff, subseq_nat_lt_subseq_iff h]

theorem subseq_nat_eq_succ_of_subseq_eq_succ {σ n m}
(h₁ : Subseq σ) (h₂ : σ n = σ m + 1) : n = m + 1 := by
  have h₃ : m < n
  · apply lt_of_le_of_ne
    · contrapose! h₂
      apply ne_of_lt
      rw [Nat.lt_succ]
      apply le_of_lt
      apply h₁
      exact h₂
    rintro rfl
    simp at h₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₃; clear h₃
  suffices : n = 0; linarith
  contrapose! h₂
  apply ne_of_gt
  cases n; simp at h₂; clear h₂
  nm n
  suffices h : σ m + 1 < σ (m + n + 2); ring_nf at h ⊢; exact h
  apply lt_of_le_of_lt # subseq_nat_succ_le h₁
  apply h₁
  omega

theorem subseq_card_filter_range_eq {a : ℕ → ℝ} {p : ℝ → Prop} {σ : ℕ → ℕ} {n k : ℕ}
[hp : DecidablePred p] (h₁ : Subseq σ) (h₂ : ∀ n, p (a n) ↔ ∃ k, σ k = n)
(h₃ : σ k = n) : {k ∈ Finset.range n | p (a k)}.card = k := by
  induction k generalizing n
  · simp
    simp [h₂]
    rintro k hk r rfl
    subst h₃
    simp [subseq_nat_lt_subseq_iff h₁] at hk
  nm k ih
  have h₄ : σ k ≤ n
  · simp [←h₃, subseq_nat_le_subseq_iff h₁]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₄; clear h₄
  specialize ih rfl
  rw [Finset.card_filter_range_add, ih]; clear ih
  simp
  rw [Finset.card_eq_one_iff_exiu]
  use σ k
  simp
  split_ands
  · rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp [subseq_nat_eq_subseq_iff h₁] at h₃
  · rw [h₂]
    use k
  intro r h₄ h₅ h₆
  rw [←h₃] at h₅
  rw [h₂] at h₆
  obtain ⟨r, rfl⟩ := h₆
  rw [subseq_nat_le_subseq_iff h₁] at h₄
  rw [subseq_nat_lt_subseq_iff h₁] at h₅
  rw [subseq_nat_eq_subseq_iff h₁]
  omega

theorem exi_fn_series_of_subseq_cover {a : ℕ → ℝ} {p : ℝ → Prop} {σ₁ σ₂ : ℕ → ℕ}
(h₁ : Subseq σ₁) (h₂ : Subseq σ₂)
(h₃ : ∀ n, p (a n) ↔ ∃ k, σ₁ k = n)
(h₄ : ∀ n, ¬p (a n) ↔ ∃ k, σ₂ k = n) :
∃ (f g : ℕ → ℕ),
(∀ i j, i ≤ j → f i ≤ f j) ∧
(∀ i j, i ≤ j → g i ≤ g j) ∧
(∀ n, f n + g n = n) ∧
(∀ n, series a n = series (a # σ₁ ·) (f n) + series (a # σ₂ ·) (g n)) := by
  classical
  use λ n => Finset.range n |>.filter (λ n => p (a n)) |>.card
  use λ n => Finset.range n |>.filter (λ n => ¬p (a n)) |>.card
  use λ _ _ => Finset.card_filter_range_le_of_le
  use λ _ _ => Finset.card_filter_range_le_of_le
  split_ands
  · intro n; convert Finset.card_filter_add_card_filter_not; simp
  intro n
  induction n
  · simp
  nm n ih
  simp_rw [series_succ, Finset.range_add_one, Finset.filter_insert]
  by_cases h : p (a n) <;> simp [h]
  · rw [series_succ]
    rw [h₃] at h
    choose k h using h
    suffices : a (σ₁ {n ∈ Finset.range n | p (a n)}.card) = a n
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq h₁ h₃ h
  · rw [series_succ]
    rw [h₄] at h
    choose k h using h
    suffices : a (σ₂ {n ∈ Finset.range n | ¬p (a n)}.card) = a n
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq (p := (¬p ·)) h₂ h₄ h

theorem exi_fn_series_abs_of_subseq_cover {a : ℕ → ℝ} {p : ℝ → Prop} {σ₁ σ₂ : ℕ → ℕ}
(h₁ : Subseq σ₁) (h₂ : Subseq σ₂)
(h₃ : ∀ n, p (a n) ↔ ∃ k, σ₁ k = n)
(h₄ : ∀ n, ¬p (a n) ↔ ∃ k, σ₂ k = n) :
∃ (f g : ℕ → ℕ),
(∀ i j, i ≤ j → f i ≤ f j) ∧
(∀ i j, i ≤ j → g i ≤ g j) ∧
(∀ n, f n + g n = n) ∧
(∀ n, series |a| n = series |(a # σ₁ ·)| (f n) + series |(a # σ₂ ·)| (g n)) := by
  classical
  use λ n => Finset.range n |>.filter (λ n => p (a n)) |>.card
  use λ n => Finset.range n |>.filter (λ n => ¬p (a n)) |>.card
  use λ _ _ => Finset.card_filter_range_le_of_le
  use λ _ _ => Finset.card_filter_range_le_of_le
  split_ands
  · intro n; convert Finset.card_filter_add_card_filter_not; simp
  intro n
  induction n
  · simp
  nm n ih
  simp_rw [series_succ, Finset.range_add_one, Finset.filter_insert]
  by_cases h : p (a n) <;> simp [h]
  · rw [series_succ]
    rw [h₃] at h
    choose k h using h
    simp only [Pi.abs_apply]
    suffices : |a (σ₁ {n ∈ Finset.range n | p (a n)}.card)| = |a n|
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq h₁ h₃ h
  · rw [series_succ]
    rw [h₄] at h
    choose k h using h
    simp only [Pi.abs_apply]
    suffices : |a (σ₂ {n ∈ Finset.range n | ¬p (a n)}.card)| = |a n|
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq (p := (¬p ·)) h₂ h₄ h

-- #check 0 #exit

theorem exi_rment_tendsTo_of_condConv {a L} (h : CondConv a) :
∃ σ, Rment σ ∧ tendsTo (series (a # σ ·)) L := by
  -- suppose that series of `a` converges to `M`
  obtain ⟨⟨M, h₁⟩, h₂⟩ := id h
  -- infinitely many elements of `a` are nonnegative
  have h₃ := infp_nonneg_of_condConv h
  -- infinitely many elements of `a` are negative
  have h₄ := infp_neg_of_condConv h
  -- there exists a subsequence of `a` called `a+`
  -- that contains exactly positive elements of `a`
  obtain ⟨σp, hp₁, hp₂⟩ := exi_subseq_of_infp h₃
  generalize hp : (a # σp ·) = ap
  -- similarly applies for `a-`
  obtain ⟨σn, hn₁, hn₂⟩ := exi_subseq_of_infp h₄
  generalize hn : (a # σn ·) = an
  
  -- series of `a+` is monotone
  have h₅ : monoLe # series ap
  · subst hp; apply monoLe_series_of_nonneg; intro n; rw [hp₂]; use n
  -- series of `a-` is antitone
  have h₆ : monoGe # series an
  · subst hn; apply monoGe_series_of_nonpos; intro n; apply le_of_lt; rw [hn₂]; use n
  
  have G₁ : 0 ≤ ap
  · intro n
    subst hp
    simp
    rw [hp₂]
    use n
  
  have G₂ : an ≤ 0
  · intro n
    subst hn
    simp
    apply le_of_lt
    rw [hn₂]
    use n
  
  have G₃ : |ap| = ap := abs_of_nonneg G₁
  have G₄ : |an| = -an := abs_of_nonpos G₂
  
  have G₅ : 0 ≤ series ap
  · intro n
    apply Finset.sum_nonneg
    intro k hk
    apply G₁
  
  have G₆ : series an ≤ 0
  · intro n
    apply Finset.sum_nonpos
    intro k hk
    apply G₂
  
  obtain ⟨f, g, hf, hg, hfg, Hfg⟩ :=
    exi_fn_series_of_subseq_cover hp₁ hn₁ hp₂ # by simpa
  obtain ⟨f', g', hf', hg', hfg', Hfg'⟩ :=
    exi_fn_series_abs_of_subseq_cover hp₁ hn₁ hp₂ # by simpa
  rw [hp, hn] at Hfg'
  
  -- series of `a+` and series of `a-` cannot both converge
  have h₇ : ¬(converges (series ap) ∧ converges (series an))
  ·
    -- suppose that series of `a+` converges to `X`
    rintro ⟨⟨X, h₇⟩, ⟨Y', h₈⟩⟩
    -- suppose that series of `a-` converges to `-Y`
    generalize hY : -Y' = Y
    rw [neg_eq_iff_eq_neg] at hY
    subst hY
    
    have hX : 0 ≤ X := le_limit_of_forall_le h₇ G₅
    
    have hY : 0 ≤ Y
    · suffices : -Y ≤ 0; linarith
      exact limit_le_of_forall_le h₈ G₆
    
    -- absolute series of `a` is bounded above by `X + Y`
    have h₉ : ∀ n, series |a| n ≤ X + Y
    ·
      intro n
      have H₁ : monoLe # series |an|
      · apply monoLe_series_abs
      have H₂ : tendsTo |series an| Y
      · rw [show Y = |-Y| by rw [abs_neg, abs_of_nonneg hY]]
        exact tendsTo_abs h₈
      have H₃ : ∀ n, series |ap| n ≤ X
      ·
        rw [abs_of_nonneg]; exact le_limit_of_monoLe h₅ h₇
        intro k
        subst hp
        simp
        rw [hp₂]
        use k
      have H₄ : ∀ n, series |an| n ≤ Y
      ·
        rw [abs_of_nonpos]
        rotate_left
        · subst hn
          intro k
          simp
          apply le_of_lt
          rw [hn₂]
          use k
        intro k
        rw [←neg_series']
        apply neg_le_of_neg_le
        apply limit_le_of_monoGe h₆ h₈
      rw [Hfg']
      linarith [H₃ (f' n), H₄ (g' n)]
    
    -- since it is monotone and bounded above, it converges
    have H : converges # series |a|
    · apply converges_of_monoLe_and_bounded_top # by simp
      use X + Y, h₉
    -- contradiction
    exact h₂ H
  
  rw [not_and_iff_or] at h₇
  
  -- series of `a+` diverges
  replace h₇ : ¬converges (series ap)
  ·
    -- suppose that it converges to some `X`
    by_contra h₈
    -- series of `a-` must diverge
    simp [h₈] at h₇
    -- since series of `a-` diverges and it is antitone,
    --   there exists a prefix of `a-` whose sum is smaller than `2 * (M - X - 1)`
    -- choose X h₈ using h₈
    -- have H₁ : 0 ≤ X := le_limit_of_forall_le h₈ G₅
    -- 
    -- obtain ⟨N, H₂⟩ := exi_lt_of_monoGe_and_not_converges h₆ h₇ # 2 * (M - X - 1)
    -- 
    -- specialize G₇ N
    -- choose kp kn hkp hkn G₇ using G₇
    -- clear hkp
    -- 
    -- -- there exists a prefix of `a` whose sum is smaller than `M - X - 1`
    -- have H₃ : series a kn < M - X - 1
    -- ·
    --   obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hkn
    --   clear hkn
    --   
    --   rw [series_add] at G₇
    --   replace G₇ : series a kn = series ap kp + series an kn - series (a # kn + ·) N; linarith
    --   rw [G₇]; clear G₇
    --   
    --   -- suffices : series ap kp - series (an # kn + ·) N < X + 2⁻¹ - 2⁻¹; linarith
    --   -- clear H₂
    --   -- apply sub_lt_sub
    --   -- · suffices : series ap kp ≤ X; linarith
    --   --   apply le_limit_of_monoLe h₅ h₈
    --   -- suffices : 0 ≤ series (an # kn + ·); linarith
    --   
    --   sorry
    --     
    -- -- all subsequent elements of the series of `a` are smaller than `M - 1`
    -- -- therefore series of `a` cannot converge to `M`
    -- -- contradiction
    sorry
  
  -- similarly `a-` diverges
  have h₈ : ¬converges (series an)
  ·
    sorry
  
  -- we construct the rearrangement recursively
  --   we start from the empty list and the sum `0`
  --   in the `n`-th iteration (starting from `n = 0`) we do the following
  --     consume the first unconsumed element `x` of `a+`
  --     consume the first unconsumed element `y` of `a-`
  --     add `x + y` to the current sum
  --     let the current sum be `s`
  --     let `d = |s - L|`
  --     if `s <= L - 1 / (n + 2)`
  --       let `N` be the index in `a+` after which all elements are smaller than `1 / (n + 2)`
  --         and all elements are unconsumed
  --       consume the shortest prefix of `a+` starting from `N`
  --         whose sum is larger than `L - 1 / (n + 2)`
  --       the new total sum will be between `L - 1 / (n + 2)` and `L` inclusively
  --     if `s >= L + 1 / (n + 2)`
  --       ditto
  --     let `s` be the new sum
  --     we now have `|s - L| < 1 / (n + 1)`
  --   the `n`-th element of the rearrangement is obtained by constructing the list
  --     in `n + 1` iterations and taking the `n`-th element
  --   let `f : N -> N` be a function that maps `n` to the index representing the
  --     end of the `n`-th generation
  --   for all `n`, sum of rearrangement of `a` up to `f n` (inclusively) is
  --     at distance from `L` at most `1 / (n + 1)`
  --   elements of series of rearrangement of `a` between `f n` and `f (n + 1)`
  --     are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
  --   moreover, all elements or series of rearrangement of `a` after `f n`
  --     are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
  --   since `a` tends to `0` and `1 / (n + 1)` also tends to `0`,
  --     the series of rearrangement of `a` tends to `L`
  sorry