import AP.RealAnalysis.Rational

namespace RealAnalysis

def unBddCnd' (p : ℕ → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ p n

def unBddCnd (p : ℝ → Prop) (a : ℕ → ℝ) : Prop :=
  unBddCnd' (p # a ·)

theorem unBddCnd'_iff_alt₁ {p} : unBddCnd' p ↔ ∀ N, ∃ n, N < n ∧ p n := by
  constructor; all_goals
    intro h N
    specialize h # N + 1
    choose n h₁ h₂ using h
    use n, by linarith, h₂

theorem unBddCnd_iff_alt₁ {a p} : unBddCnd p a ↔ ∀ N, ∃ n, N < n ∧ p (a n) := by
  constructor; all_goals
    intro h N
    specialize h # N + 1
    choose n h₁ h₂ using h
    use n, by linarith, h₂

theorem unBddCnd'_iff_alt₂ {p} : unBddCnd' p ↔ {n | p n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  simp
  rw [unBddCnd'_iff_alt₁]
  apply forall_congr'; intro N
  tauto

theorem unBddCnd_iff_alt₂ {a p} : unBddCnd p a ↔ {n | p # a n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  simp
  rw [unBddCnd_iff_alt₁]
  apply forall_congr'; intro N
  tauto

@[simp] noncomputable
def filter (p : ℝ → Prop) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  let n₀ := Nat.findRaw (p # a ·)
  match n with
  | 0 => a n₀
  | n + 1 => filter p (a # n₀ + 1 + ·) n

@[simp] noncomputable
def filterSubseq (p : ℝ → Prop) (a : ℕ → ℝ) (n : ℕ) : ℕ :=
  let n₀ := Nat.findRaw (p # a ·)
  match n with
  | 0 => n₀
  | n + 1 => n₀ + 1 + filterSubseq p (a # n₀ + 1 + ·) n

theorem unBddCnd_drop_of {a p k} (h : unBddCnd p a) : unBddCnd p (a # k + ·) := by
  intro N
  specialize h # N + k
  choose n h₁ h₂ using h
  use n - k, by omega
  simp
  rw [←Nat.add_sub_assoc # by linarith]
  simpa

theorem unBddCnd_drop_iff {a p k} : unBddCnd p (a # k + ·) ↔ unBddCnd p a := by
  symm; use unBddCnd_drop_of
  intro h N
  specialize h # N + k
  choose n h₁ h₂ using h
  use n + k, by linarith
  rwa [add_comm]

theorem subseq_filterSubseq {a p} (h : unBddCnd p a) : subseq (filterSubseq p a) := by
  rw [subseq_iff_lt_add_one]
  intro n
  simp
  induction n generalizing a
  · simp; linarith
  nm n ih
  simp
  generalize hk₁ : Nat.findRaw (p # a ·) = k₁
  exact @ih (a # k₁ + 1 + ·) # unBddCnd_drop_of h

theorem filter_eq_filterSubseq {a p} (h : unBddCnd p a) : filter p a = a ∘ filterSubseq p a := by
  ext n
  simp
  induction n generalizing a
  · simp
  nm n ih
  simp
  generalize hk : Nat.findRaw (p # a ·) = k
  exact @ih (a # k + 1 + ·) # unBddCnd_drop_of h

theorem tendsTo_filter {a L p} (h₁ : tendsTo a L) (h₂ : unBddCnd p a) : tendsTo (filter p a) L := by
  rw [filter_eq_filterSubseq h₂]
  exact tendsTo_subseq h₁ # subseq_filterSubseq h₂

theorem unBddCnd_or_of_or {a : ℕ → ℝ} {p₁ p₂ : ℝ → Prop} (h : ∀ n, p₁ (a n) ∨ p₂ (a n)) :
unBddCnd p₁ a ∨ unBddCnd p₂ a := by
  rw [or_iff_not_imp_left]
  intro h₁
  simp [unBddCnd, unBddCnd'] at h₁
  choose N h₁ using h₁
  intro N₁
  use N + N₁, by linarith
  specialize h # N + N₁
  specialize h₁ (N + N₁) # by linarith
  simp [h₁] at h
  exact h

theorem unBddCnd_le_or_ge {a M} : unBddCnd (· ≤ M) a ∨ unBddCnd (M ≤ ·) a := by
  apply unBddCnd_or_of_or; intro N; apply le_total

theorem apply_nat_findRaw_of_unBddCnd {a p} (h : unBddCnd p a) : p # a # Nat.findRaw (p # a ·) := by
  apply Nat.findRaw_spec (P := (p # a ·))
  specialize h 0
  choose n h₁ h₂ using h
  use n

theorem apply_filterSubseq {a p n} (h : unBddCnd p a) : p (a # filterSubseq p a n) := by
  induction n generalizing a
  · simp; exact apply_nat_findRaw_of_unBddCnd h
  nm n ih
  simp
  have h₁ := apply_nat_findRaw_of_unBddCnd h
  generalize hk : Nat.findRaw (p # a ·) = k at h₁ ⊢
  exact @ih (a # k + 1 + ·) # unBddCnd_drop_of h

theorem apply_filter {a p n} (h : unBddCnd p a) : p (filter p a n) := by
  rw [filter_eq_filterSubseq h]; simp; exact apply_filterSubseq h

theorem unBddCnd_filter {a p} (h : unBddCnd p a) : unBddCnd p (filter p a) :=
  λ N => ⟨N, by rfl, apply_filter h⟩

@[simp] noncomputable
def monoLtSubseq (a : ℕ → ℝ) (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 =>
    let n₀ := monoLtSubseq a n
    n₀ + Nat.findRaw (λ k => a n₀ < a (n₀ + k))

theorem exi_cnd_add_of_lt_limit {a L n m} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
∃ k, a n < a (m + k) := by
  specialize h₁ (L - a n) # by linarith [h₂ n]
  choose N h₁ using h₁
  dsimp at h₁
  specialize h₁ (m + N) # by linarith
  rw [abs_of_neg # by linarith [h₂ # m + N]] at h₁
  simp at h₁
  use N

theorem exi_cnd_of_lt_limit {a L n} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
∃ k, a n < a k := by
  have h₃ := exi_cnd_add_of_lt_limit (n := n) (m := 0) h₁ h₂
  simp at h₃; exact h₃

theorem apply_natFindRaw_of_lt_limit {a L n} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
a n < a (Nat.findRaw (a n < a ·)) :=
  Nat.findRaw_spec (P := (a n < a ·)) # exi_cnd_of_lt_limit h₁ h₂

theorem apply_natFindRaw_add_of_lt_limit {a L n m} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
a n < a (m + Nat.findRaw (λ k => a n < a (m + k))) :=
  Nat.findRaw_spec (P := λ k => a n < a (m + k)) # exi_cnd_add_of_lt_limit h₁ h₂

theorem pos_natFindRaw_add_of_lt_limit {a L n} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
0 < Nat.findRaw (λ k => a n < a (n + k)) := by
  apply Nat.findRaw_pos_of; simp; exact exi_cnd_add_of_lt_limit h₁ h₂

theorem subseq_monoLtSubseq {a L} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
subseq # monoLtSubseq a := by
  rw [subseq_iff_lt_add_one]
  intro n
  simp
  exact pos_natFindRaw_add_of_lt_limit h₁ h₂

theorem monoLt_monoLtSubseq {a L} (h₁ : tendsTo a L) (h₂ : ∀ n, a n < L) :
monoLt (a ∘ monoLtSubseq a) := by
  rw [monoLt_iff_lt_succ]
  intro n
  simp
  generalize monoLtSubseq a n = n; nm x; clear x
  exact apply_natFindRaw_add_of_lt_limit h₁ h₂
  
theorem exi_monoLt_subseq_of_forall_lt_limit {a L} (h₁ : tendsTo a L)
(h₂ : ∀ n, a n < L) : ∃ σ, subseq σ ∧ monoLt (a ∘ σ) := by
  use monoLtSubseq a
  use subseq_monoLtSubseq h₁ h₂
  use monoLt_monoLtSubseq h₁ h₂

theorem exi_monoLe_subseq_of_forall_le_limit {a L} (h₁ : tendsTo a L)
(h₂ : ∀ n, a n ≤ L) : ∃ σ, subseq σ ∧ monoLe (a ∘ σ) := by
  by_cases h₃ : unBddCnd (· < L) a
  rotate_left
  · simp [unBddCnd, unBddCnd'] at h₃
    choose N h₃ using h₃
    replace h₃ : unBddCnd (· = L) a
    · intro N₁
      specialize h₃ (N + N₁) # by linarith
      use N + N₁, by linarith
      apply le_antisymm _ h₃; apply h₂
    use filterSubseq (· = L) a, subseq_filterSubseq h₃
    simp [apply_filterSubseq h₃]
  clear h₂
  rename' h₃ => h₂
  have h₃ := tendsTo_filter h₁ h₂
  have h₄ : ∀ n, filter (· < L) a n < L
  · intro n; apply apply_filter h₂
  choose σ h₅ h₆ using exi_monoLt_subseq_of_forall_lt_limit h₃ h₄
  rw [filter_eq_filterSubseq h₂] at h₆
  use filterSubseq (· < L) a ∘ σ
  use subseq_comp (subseq_filterSubseq h₂) h₅
  exact monoLe_of_monoLt h₆

theorem exi_monoLe_subseq_of_unBddCnd_le_limit {a L} (h₁ : tendsTo a L)
(h₂ : unBddCnd (· ≤ L) a) : ∃ σ, subseq σ ∧ monoLe (a ∘ σ) := by
  have h₃ := tendsTo_filter h₁ h₂
  have h₄ : ∀ n, filter (· ≤ L) a n ≤ L
  · intro n; apply apply_filter h₂
  choose σ h₅ h₆ using exi_monoLe_subseq_of_forall_le_limit h₃ h₄
  rw [filter_eq_filterSubseq h₂] at h₆
  use filterSubseq (· ≤ L) a ∘ σ, subseq_comp (subseq_filterSubseq h₂) h₅, h₆

theorem exi_monoLt_subseq_of_unBddCnd_lt_limit {a L} (h₁ : tendsTo a L)
(h₂ : unBddCnd (· < L) a) : ∃ σ, subseq σ ∧ monoLt (a ∘ σ) := by
  have h₃ := tendsTo_filter h₁ h₂
  have h₄ : ∀ n, filter (· < L) a n < L
  · intro n; apply apply_filter h₂
  choose σ h₅ h₆ using exi_monoLt_subseq_of_forall_lt_limit h₃ h₄
  rw [filter_eq_filterSubseq h₂] at h₆
  use filterSubseq (· < L) a ∘ σ, subseq_comp (subseq_filterSubseq h₂) h₅, h₆

theorem exi_monoGe_subseq_of_unBddCnd_limit_le {a L} (h₁ : tendsTo a L)
(h₂ : unBddCnd (L ≤ ·) a) : ∃ σ, subseq σ ∧ monoGe (a ∘ σ) := by
  replace h₁ : tendsTo (-a) (-L); exact tendsTo_neg h₁
  replace h₂ : unBddCnd (· ≤ -L) (-a)
  · intro n
    specialize h₂ n
    simpa
  choose σ h₃ h₄ using exi_monoLe_subseq_of_unBddCnd_le_limit h₁ h₂
  use σ, h₃
  convert_to monoGe (-(-a) ∘ σ); ext; simp
  simp at h₄ ⊢
  exact h₄

theorem exi_monoGt_subseq_of_unBddCnd_limit_lt {a L} (h₁ : tendsTo a L)
(h₂ : unBddCnd (L < ·) a) : ∃ σ, subseq σ ∧ monoGt (a ∘ σ) := by
  replace h₁ : tendsTo (-a) (-L); exact tendsTo_neg h₁
  replace h₂ : unBddCnd (· < -L) (-a)
  · intro n
    specialize h₂ n
    simpa
  choose σ h₃ h₄ using exi_monoLt_subseq_of_unBddCnd_lt_limit h₁ h₂
  use σ, h₃
  convert_to monoGt (-(-a) ∘ σ); ext; simp
  simp at h₄ ⊢
  exact h₄

theorem exi_monoLe_or_monoGe_subseq_of_converges {a}
(h : converges a) : ∃ σ, subseq σ ∧ (monoLe (a ∘ σ) ∨ monoGe (a ∘ σ)) := by
  choose L h using h
  rcases @unBddCnd_le_or_ge a L with h₁ | h₁
  · choose σ h₂ h₃ using exi_monoLe_subseq_of_unBddCnd_le_limit h h₁
    use σ, h₂; left; exact h₃
  · choose σ h₂ h₃ using exi_monoGe_subseq_of_unBddCnd_limit_le h h₁
    use σ, h₂; right; exact h₃

theorem exi_monoLe_or_monoGe_subseq_of_bounded {a}
(h : bounded a) : ∃ σ, subseq σ ∧ (monoLe (a ∘ σ) ∨ monoGe (a ∘ σ)) := by
  obtain ⟨σ, h₁, h₂⟩ := exi_converges_subseq_of_bounded h
  obtain ⟨σ', H₁, H₂⟩ := exi_monoLe_or_monoGe_subseq_of_converges h₂
  use σ ∘ σ', subseq_comp h₁ H₁, H₂

def isPeak (a : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ n, k ≤ n → a n ≤ a k

theorem isPeak_iff_alt₁ {a k} : isPeak a k ↔ ∀ n, k < n → a n ≤ a k := by
  constructor
  · intro h N h₁
    apply h
    linarith
  · intro h N h₁
    rw [le_iff_eq_or_lt] at h₁
    rcases h₁ with rfl | h₁
    · rfl
    apply h
    exact h₁

def unBddPeaks (a : ℕ → ℝ) : Prop :=
  unBddCnd' # isPeak a

theorem exi_drop_eq_subseq {a : ℕ → ℝ} {k} : ∃ σ, subseq σ ∧ (a # k + ·) = (a ∘ σ) := by
  use (k + ·)
  simp
  intro i j h
  simpa

theorem exi_monoLe_subseq_of_not_unBddPeaks {a} (h : ¬unBddPeaks a) :
∃ σ, subseq σ ∧ monoLe (a ∘ σ) := by
  simp [unBddPeaks, unBddCnd', isPeak] at h
  choose N h using h
  change ∀ n, N ≤ n → ∃ k, n ≤ k ∧ a n < a k at h
  replace h : ∀ n, ∃ k, n ≤ k ∧ (a # N + ·) n < (a # N + ·) k
  · intro n
    simp
    specialize h (N + n) # by linarith
    choose k h₁ h₂ using h
    use k - N, by omega
    rw [←Nat.add_sub_assoc # by linarith]
    simpa
  suffices h₁ : ∃ σ, subseq σ ∧ monoLe ((a # N + ·) ∘ σ)
  · choose σ h₁ h₂ using h₁
    use (N + ·) ∘ σ
    refine ⟨?_, h₂⟩
    apply subseq_comp _ h₁
    intro i j h; simpa
  generalize (a # N + ·) = a at h ⊢; nm x; clear x
  replace h : ∀ n, ∃ k, n < k ∧ a n < a k
  · intro n
    specialize h n
    choose k h₁ h₂ using h
    refine ⟨k, ?_, h₂⟩
    rw [lt_iff_le_and_ne]; use h₁
    rintro rfl
    simp at h₂
  choose σ h₁ h₂ using h
  use (σ^[·] 0), subseq_iterate_of_id_lt h₁
  apply monoLe_of_monoLt; rw [monoLt_iff_lt_succ]
  intro n
  simp
  change _ < a (σ^[n + 1] 0)
  rw [Function.iterate_succ']
  apply h₂

theorem exi_monoGe_subseq_of_unBddPeaks {a} (h : unBddPeaks a) :
∃ σ, subseq σ ∧ monoGe (a ∘ σ) := by
  simp [unBddPeaks, unBddCnd'_iff_alt₁, isPeak] at h
  replace h : ∀ N, ∃ n, N < n ∧ ∀ k, a (n + k) ≤ a n
  · intro N
    specialize h N
    choose n h₁ h₂ using h
    use n, h₁
    intro k
    exact h₂ (n + k) # by linarith
  choose σ h₁ h₂ using h
  use (σ^[· + 1] 0), subseq_iterate_of_id_lt h₁
  rw [monoGe_iff_succ_le]
  intro n
  simp
  change a (σ^[n + 2] 0) ≤ a (σ^[n + 1] 0)
  simp_rw [Function.iterate_succ']
  simp
  generalize σ^[n] 0 = N
  specialize h₁ # σ N
  obtain ⟨k, h₃⟩ := Nat.exists_eq_add_of_le # le_of_lt h₁
  rw [h₃]
  apply h₂