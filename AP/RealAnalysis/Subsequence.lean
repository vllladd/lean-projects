import AP.RealAnalysis.Coherence

namespace RealAnalysis

def Infp (a : ℕ → ℝ) (p : ℝ → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ p (a n)

open Classical in noncomputable
def mkSubseq (a : ℕ → ℝ) (p : ℝ → Prop) (n : ℕ) : ℕ :=
  match n with
  | 0 => Nat.find! (p # a ·)
  | n + 1 =>
    let k := mkSubseq a p n
    k + 1 + Nat.find! (p # a # k + 1 + ·)

-- #check 0 #exit

-----

theorem absConv_drop_of {a N} (h : AbsConv a) : AbsConv (a # N + ·) := by
  unfold AbsConv at h ⊢; rwa [converges_series_drop_iff (a := (|a ·|))]

theorem absConv_drop_iff {a N} : AbsConv (a # N + ·) ↔ AbsConv a := by
  exact converges_series_drop_iff (a := (|a ·|))

theorem absConv_neg {a} : AbsConv (-a) ↔ AbsConv a := by
  simp [AbsConv]

theorem infp_iff_infinite {a p} : Infp a p ↔ {n | p # a n}.Infinite := by
  simp_rw [Set.infinite_iff_exists_gt, Set.mem_setOf_eq]
  constructor; all_goals
    intro h N
    specialize h # N + 1
    choose n h₁ h₂ using h
    use n, by omega, by omega

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
  · exact Nat.find!_spec (P := (p # a ·)) # exi_of_infp h
  nm n; apply Nat.find!_spec (P := λ k => p (a (mkSubseq a p n + 1 + k)))
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
    rw [Nat.find!_eq_iff, if_pos ⟨_, h₁⟩]
    exact ⟨h₁, h₂⟩
  push_neg at h₂
  replace h₂ : ∃ k, k < n ∧ p (a k) ∧ ∀ r, k < r → r < n → ¬p (a r)
  · choose k hk h₂ using h₂
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk; clear hk
    have h₃ : ∃ d, p # a # k + n - d
    · use n
      simpa
    replace h₃ := Nat.find!_spec' h₃
    generalize Nat.find! (λ d => p # a # k + n - d) = d at h₃
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
  rw [Nat.find!_eq_iff]
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

theorem exi_gt_of_monoLe_and_not_converges {a}
(h₁ : monoLe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, L < a N := by
  contrapose! h₂; apply converges_of_monoLe_and_bounded_top h₁ ⟨L, h₂⟩

theorem exi_lt_of_monoGe_and_not_converges {a}
(h₁ : monoGe a) (h₂ : ¬converges a) (L : ℝ) : ∃ N, a N < L := by
  contrapose! h₂; apply converges_of_monoGe_and_bounded_bottom h₁ ⟨L, h₂⟩

theorem monoLe_series_of_nonneg {a} (h : ∀ n, 0 ≤ a n) : monoLe (series a) := by
  rw [monoLe_iff_le_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGe_series_of_nonpos {a} (h : ∀ n, a n ≤ 0) : monoGe (series a) := by
  rw [monoGe_iff_succ_le]; intro n; rw [series_succ]; linarith [h n]

theorem monoLt_series_of_pos {a} (h : ∀ n, 0 < a n) : monoLt (series a) := by
  rw [monoLt_iff_lt_succ]; intro n; rw [series_succ]; linarith [h n]

theorem monoGt_series_of_neg {a} (h : ∀ n, a n < 0) : monoGt (series a) := by
  rw [monoGt_iff_succ_lt]; intro n; rw [series_succ]; linarith [h n]

theorem subseq_nat_succ_le {σ n} (h : Subseq σ) : σ n + 1 ≤ σ (n + 1) := by
  simp [Nat.add_one_le_iff, subseq_lt_iff h]

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
    simp [subseq_lt_iff h₁] at hk
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
    simp [subseq_eq_iff h₁] at h₃
  · rw [h₂]
    use k
  intro r h₄ h₅ h₆
  rw [←h₃] at h₅
  rw [h₂] at h₆
  obtain ⟨r, rfl⟩ := h₆
  rw [subseq_nat_le_subseq_iff h₁] at h₄
  rw [subseq_lt_iff h₁] at h₅
  rw [subseq_eq_iff h₁]
  omega

theorem exi_fn_series_of_subseq_cover {a : ℕ → ℝ} {p : ℝ → Prop} {σ₁ σ₂ : ℕ → ℕ}
{F : ℝ → ℝ}
(h₁ : Subseq σ₁) (h₂ : Subseq σ₂)
(h₃ : ∀ n, p (a n) ↔ ∃ k, σ₁ k = n)
(h₄ : ∀ n, ¬p (a n) ↔ ∃ k, σ₂ k = n) :
∃ (f g : ℕ → ℕ), (∀ n, f n + g n = n) ∧
(∀ i j, i ≤ j → f i ≤ f j) ∧ (∀ i j, i ≤ j → g i ≤ g j) ∧
(Infp a p → ∀ n, ∃ k, n ≤ f k) ∧ (Infp a (¬p ·) → ∀ n, ∃ k, n ≤ g k) ∧
(∀ n, series (F # a ·) n = series (F # a # σ₁ ·) (f n) + series (F # a # σ₂ ·) (g n)) := by
  classical
  use λ n => Finset.range n |>.filter (λ n => p (a n)) |>.card
  use λ n => Finset.range n |>.filter (λ n => ¬p (a n)) |>.card
  split_ands
  · intro n; convert Finset.card_filter_add_card_filter_not; simp
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | p (a i)}.card; linarith
    simp
    use k + r
    simpa
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    dsimp
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | ¬p (a i)}.card; linarith
    simp
    use k + r
    simpa
  intro n
  induction n
  · simp
  nm n ih
  simp_rw [series_succ, Finset.range_add_one, Finset.filter_insert]
  by_cases h : p (a n) <;> simp [h]
  · rw [series_succ]
    rw [h₃] at h
    choose k h using h
    suffices : F (a # σ₁ {n ∈ Finset.range n | p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq h₁ h₃ h
  · rw [series_succ]
    rw [h₄] at h
    choose k h using h
    suffices : F (a # σ₂ {n ∈ Finset.range n | ¬p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq (p := (¬p ·)) h₂ h₄ h

theorem not_of_lt_mkSubseq_zero {a p n}
(h : n < mkSubseq a p 0) : ¬p (a n) := by
  simp [mkSubseq] at h; exact Nat.find!_min h

@[simp]
theorem mkSubseq_lt_mkSubseq_succ {a p n} : mkSubseq a p n < mkSubseq a p (n + 1) := by
  simp [mkSubseq]; omega

@[simp]
theorem mkSubseq_le_mkSubseq_succ {a p n} : mkSubseq a p n ≤ mkSubseq a p (n + 1) :=
  le_of_lt mkSubseq_lt_mkSubseq_succ

theorem not_of_between_mkSubseq {a p k} n (H : Infp a p)
(h₁ : mkSubseq a p n < k) (h₂ : k < mkSubseq a p (n + 1)) : ¬p (a k) := by
  intro h₃
  replace h₃ := exi_mkSubseq_eq_of_apply H h₃
  obtain ⟨k, rfl⟩ := h₃
  rw [subseq_lt_iff subseq_mkSubseq] at h₁ h₂
  omega

theorem filter_range_mkSubseq_succ {a p n} [hp : DecidablePred p] (H : Infp a p) :
(List.range (mkSubseq a p # n + 1) |>.filter (p # a ·)) =
(List.range (mkSubseq a p n) |>.filter (p # a ·)) ++ [mkSubseq a p n] := by
  have h₁ : mkSubseq a p n < mkSubseq a p (n + 1)
  · apply subseq_lt_of_lt subseq_mkSubseq; simp
  obtain ⟨k, h₂⟩ := Nat.exists_eq_add_of_lt h₁
  rw [h₂]; replace h₂ : k + mkSubseq a p n < mkSubseq a p (n + 1); omega
  induction k
  · simp [List.range_succ]; exact mkSubseq_spec H
  nm k ih
  rw [←ih # by omega]; clear ih
  nth_rw 1 [List.range_succ]
  ring_nf; simp
  apply not_of_between_mkSubseq n H <;> omega