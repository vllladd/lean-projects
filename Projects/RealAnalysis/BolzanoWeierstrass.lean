import Projects.RealAnalysis.Monotonicity

namespace RealAnalysis

open Classical in
@[simp] noncomputable
def bwSeq (a : ℕ → ℝ) (y₁ y₂ : ℚ) (n : ℕ) : ℚ × ℚ := match n with
| 0 => (y₁, y₂)
| n + 1 => let y := (y₁ + y₂) / 2
  if {i | y₁ ≤ a i ∧ a i ≤ y}.Infinite
  then bwSeq a y₁ y n else bwSeq a y y₂ n

open Classical in noncomputable
def bwLimit (a : ℕ → ℝ) (M : ℚ) : ℝ :=
  if h : IsCauSeq abs (bwSeq a (-M) M · |>.1)
  then Real.mk # .mk _ h
  else 0

open Classical in noncomputable
def bwSubseq (a : ℕ → ℝ) (M : ℚ) (n : ℕ) : ℕ :=
  τ i, (∀ k < n, bwSubseq a M k < i) ∧
  let (y₁, y₂) := bwSeq a (-M) M n
  y₁ ≤ a i ∧ a i ≤ y₂

-----

theorem le_bwSeq_fst {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(hy : y₁ < y₂) : y₁ ≤ (bwSeq a y₁ y₂ n).1 := by
  induction n generalizing y₁ y₂; rfl
  nm n ih
  simp
  split_ifs with h₁
  · apply ih; linarith
  trans (y₁ + y₂) / 2; linarith
  apply ih; linarith

theorem bwSeq_snd_le {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ}
(hy : y₁ < y₂) : (bwSeq a y₁ y₂ n).2 ≤ y₂ := by
  induction n generalizing y₁ y₂; simp
  nm n ih
  simp
  split_ifs with h₁
  · trans (y₁ + y₂) / 2
    · apply ih; linarith
    linarith
  apply ih; linarith

theorem bwSeq_add {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n k : ℕ} (hy : y₁ < y₂) :
bwSeq a y₁ y₂ (n + k) = bwSeq a (bwSeq a y₁ y₂ n).1 (bwSeq a y₁ y₂ n).2 k := by
  generalize hr : bwSeq a y₁ y₂ n = r
  rcases r with ⟨y₁', y₂'⟩
  dsimp
  induction n generalizing y₁ y₂ y₁' y₂'
  · simp at hr; simp [hr]
  nm n ih
  simp at hr
  simp [Nat.succ_add]
  split_ifs at hr ⊢ with h₁
  all_goals apply ih; linarith; exact hr

theorem bwSeq_fst_lt_snd' {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 < (bwSeq a y₁ y₂ n).2 := by
  induction n generalizing y₁ y₂ <;> simp; exact hy
  nm n ih; split_ifs <;> apply ih <;> linarith

theorem bwSeq_fst_le_of_le {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n m : ℕ}
(hy : y₁ < y₂) (hn : m ≤ n) :
(bwSeq a y₁ y₂ m).1 ≤ (bwSeq a y₁ y₂ n).1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ m = r
  rcases r with ⟨y₁', y₂'⟩
  apply le_bwSeq_fst
  rw [Prod.fst_eq_of_eq_mk hr, Prod.snd_eq_of_eq_mk hr]
  exact bwSeq_fst_lt_snd' hy

theorem le_bwSeq_snd_of_le {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n m : ℕ}
(hy : y₁ < y₂) (hn : m ≤ n) :
(bwSeq a y₁ y₂ n).2 ≤ (bwSeq a y₁ y₂ m).2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ m = r
  rcases r with ⟨y₁', y₂'⟩
  apply bwSeq_snd_le
  rw [Prod.fst_eq_of_eq_mk hr, Prod.snd_eq_of_eq_mk hr]
  exact bwSeq_fst_lt_snd' hy

theorem fst_lt_snd_of_bwSeq_eq {a : ℕ → ℝ} {y₁ y₂ y₁' y₂' : ℚ} {n : ℕ} (hy : y₁ < y₂)
(h : bwSeq a y₁ y₂ n = (y₁', y₂')) : y₁' < y₂' := by
  rw [Prod.fst_eq_of_eq_mk h, Prod.snd_eq_of_eq_mk h]
  exact bwSeq_fst_lt_snd' hy

theorem bwSeq_snd_sub_fst_eq {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).2 - (bwSeq a y₁ y₂ n).1 = (y₂ - y₁) / 2 ^ n := by
  induction n generalizing y₁ y₂; simp
  nm n ih
  simp only [bwSeq]
  split_ifs with h₁
  all_goals
    apply (ih # by linarith).trans
    rw [pow_succ']
    ring_nf

theorem bwSeq_fst_eq_snd_sub {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 = (bwSeq a y₁ y₂ n).2 - (y₂ - y₁) / 2 ^ n := by
  linarith [@bwSeq_snd_sub_fst_eq a y₁ y₂ n hy]

theorem bwSeq_snd_eq_fst_sub {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).2 = (bwSeq a y₁ y₂ n).1 + (y₂ - y₁) / 2 ^ n := by
  simp [bwSeq_fst_eq_snd_sub hy]

theorem bwSeq_add_fst_sub_lt {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n k : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ (n + k)).1 - (bwSeq a y₁ y₂ n).1 < (y₂ - y₁) / 2 ^ n := by
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ n = r
  rcases r with ⟨y₁', y₂'⟩
  dsimp
  apply lt_of_lt_of_le
  rotate_left; apply le_of_eq # bwSeq_snd_sub_fst_eq (a := a) hy
  simp [hr]
  have hy' := fst_lt_snd_of_bwSeq_eq hy hr
  exact lt_of_lt_of_le (bwSeq_fst_lt_snd' hy') (bwSeq_snd_le hy')

theorem isCauSeq_bwSeq_fst {a : ℕ → ℝ} {y₁ y₂ : ℚ}
(hy : y₁ < y₂) : IsCauSeq abs (bwSeq a y₁ y₂ · |>.1) := by
  have hy' : (y₁ : ℝ) < y₂; simpa
  generalize hd : y₂ - y₁ = d
  have H₁ : 0 < d; linarith
  intro ε hε
  replace hε : 0 < (ε : ℝ); simpa
  obtain ⟨N, hN⟩ : ∃ (n : ℕ), d / 2 ^ n < ε
  · by_cases h₂ : d ≤ ε; use 1
    · simp; calc
      d / 2 ≤ ε / 2 := by linarith
      _ < _ := by linarith
    push Not at h₂
    rw [←Real.ratCast_lt] at h₂
    suffices h₁ : ∃ (r : ℝ), 0 < r ∧ (d : ℝ) / 2 ^ r < ε
    · obtain ⟨r, hr, h₁⟩ := h₁
      obtain ⟨n, hn⟩ := exists_nat_gt r
      use n
      rw [←Real.ratCast_lt] at H₁ ⊢
      push_cast at H₁ ⊢
      apply h₁.trans'; clear h₁
      simp_rw [div_eq_mul_inv, mul_lt_mul_iff_right₀ H₁]
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
  clear hn
  dsimp
  rw [abs_of_nonneg]
  rotate_left
  · exact sub_nonneg_of_le # bwSeq_fst_le_of_le hy # by simp
  apply bwSeq_add_fst_sub_lt hy |>.trans
  rwa [hd]

theorem isCauSeq_bwSeq_fst_of_abs_lt {a : ℕ → ℝ} {M : ℚ}
(h : ∀ n, |a n| < M) : IsCauSeq abs (bwSeq a (-M) M · |>.1) := by
  apply isCauSeq_bwSeq_fst
  suffices h : 0 < M; linarith
  have h₁ := pos_of_abs_lt # h 0
  simp at h₁; exact h₁

theorem infinite_between_of_bwSeq_eq {a : ℕ → ℝ} {y₁ y₂ y₁' y₂' : ℚ} {n : ℕ}
(hy : y₁ < y₂) (ha : {i | y₁ ≤ a i ∧ a i ≤ y₂}.Infinite)
(hr : bwSeq a y₁ y₂ n = (y₁', y₂')) : {i | y₁' ≤ a i ∧ a i ≤ y₂'}.Infinite := by
  induction n generalizing y₁ y₂ y₁' y₂'
  · simp at hr
    simp [hr] at ha
    exact ha
  nm n ih
  simp at hr
  split_ifs at hr with h₁ <;> apply ih (by linarith) _ hr <;> clear ih
  · exact h₁
  clear! n
  simp at h₁
  rw [Set.finite_iff_bddAbove] at h₁
  obtain ⟨N, h₁⟩ := h₁
  rw [Set.infinite_iff_exists_gt] at ha
  simp at ha
  replace h₁ : ∀ n, N < n → a n < y₁ ∨ (↑y₁ + ↑y₂) / 2 < a n
  · intro n
    specialize @h₁ n
    simp at h₁
    rw [or_iff_not_imp_left]
    intro h₂ h₃
    simp at h₃
    contrapose! h₁
    use h₃
  apply Set.infinite_of_forall_exists_gt
  intro n
  specialize ha # N + n + 1
  obtain ⟨k, ⟨ha₁, ha₂⟩, hk⟩ := ha
  use k
  refine ⟨?_, by linarith⟩
  simp
  specialize h₁ k (by linarith)
  rcases h₁ with h₁ | h₁; linarith
  constructor <;> linarith

theorem infinite_between_of_bwSeq_eq_of_abs_lt {a : ℕ → ℝ} {M y₁ y₂ : ℚ} {n : ℕ}
(h : ∀ n, |a n| < M) (hr : bwSeq a (-M) M n = (y₁, y₂)) :
{i | y₁ ≤ a i ∧ a i ≤ y₂}.Infinite := by
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0
    simp at h; exact h
  have hM : -M < M; linarith
  apply infinite_between_of_bwSeq_eq hM _ hr
  apply Set.infinite_of_forall_exists_gt
  clear! n
  intro n
  simp
  use n + 1
  simp
  specialize h (n + 1)
  rw [abs_lt] at h
  constructor <;> linarith

theorem bwSubseq_cnd' {a : ℕ → ℝ} {M : ℚ} {n : ℕ} (h : ∀ n, |a n| < M) :
∃ i, (∀ k < n, bwSubseq a M k < i) ∧
let (y₁, y₂) := bwSeq a (-M) M n
y₁ ≤ a i ∧ a i ≤ y₂ := by
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  induction n
  · use 0
    simp
    specialize h 0
    rw [abs_lt] at h
    constructor <;> linarith
  nm n ih
  have h₁ := τ_spec ih
  generalize h₂ : (τ i, (∀ k < n, bwSubseq a M k < i) ∧
    match bwSeq a (-M) M n with | (y₁, y₂) => ↑y₁ ≤ a i ∧ a i ≤ ↑y₂) = i at h₁
  rcases h₁ with ⟨h₁, h₃⟩
  generalize hr : bwSeq a (-M) M n = r at h₃ ⊢
  rcases r with ⟨y₁, y₂⟩
  simp at h₃
  rcases h₃ with ⟨h₃, h₄⟩
  have hy := fst_lt_snd_of_bwSeq_eq hM hr
  rw [bwSeq_add hM, hr]
  dsimp only
  generalize hr' : bwSeq a y₁ y₂ 1 = r'
  rcases r' with ⟨y₁', y₂'⟩
  dsimp
  have hR : bwSeq a (-M) M (n + 1) = (y₁', y₂')
  · rwa [bwSeq_add hM, hr]
  have H := infinite_between_of_bwSeq_eq_of_abs_lt h hR
  generalize hN : 1 + ∑ k ∈ Finset.range (n + 1), bwSubseq a M k = N
  rw [Set.infinite_iff_exists_gt] at H
  specialize H N
  simp at H
  obtain ⟨m, H, hm⟩ := H
  use m
  refine ⟨?_, H⟩
  intro k hk
  apply hm.trans'
  rw [←hN]
  rw [Nat.lt_one_add_iff]
  replace hk : k ∈ Finset.range (n + 1)
  · simp at hk; simpa
  exact Finset.single_le_sum_of_canonicallyOrdered hk

theorem bwSubseq_cnd {a : ℕ → ℝ} {M : ℚ} {n : ℕ} (h : ∀ n, |a n| < M) :
(∀ k < n, bwSubseq a M k < bwSubseq a M n) ∧
let (y₁, y₂) := bwSeq a (-M) M n
y₁ ≤ a (bwSubseq a M n) ∧ a (bwSubseq a M n) ≤ y₂ := by
  have h₁ := @bwSubseq_cnd' a M n h
  have h₂ := τ_spec h₁
  rw [←bwSubseq] at h₂; exact h₂

theorem bwSubseq_lt_of_lt {a : ℕ → ℝ} {M : ℚ} {i j : ℕ} (h : ∀ n, |a n| < M)
(h₁ : i < j) : bwSubseq a M i < bwSubseq a M j := by
  obtain ⟨h₂, h₃, h₄⟩ := @bwSubseq_cnd a M i h
  obtain ⟨h₅, h₆, h₇⟩ := @bwSubseq_cnd a M j h
  specialize h₅ i h₁
  linarith

theorem subseq_bwSubseq {a : ℕ → ℝ} {M : ℚ} (h : ∀ n, |a n| < M) :
Subseq # bwSubseq a M := λ _ _ => bwSubseq_lt_of_lt h

theorem bwSeq_fst_lt_snd {a : ℕ → ℝ} {y₁ y₂ : ℚ} {n m : ℕ} (hy : y₁ < y₂) :
(bwSeq a y₁ y₂ n).1 < (bwSeq a y₁ y₂ m).2 := by
  by_cases hn : n ≤ m
  · exact lt_of_le_of_lt (bwSeq_fst_le_of_le hy hn) (bwSeq_fst_lt_snd' hy)
  replace hn : m ≤ n; linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
  rw [bwSeq_add hy]
  generalize hr : bwSeq a y₁ y₂ m = r
  rcases r with ⟨y₁', y₂'⟩
  have hy' := fst_lt_snd_of_bwSeq_eq hy hr
  exact lt_of_lt_of_le (bwSeq_fst_lt_snd' hy') (bwSeq_snd_le hy')

theorem bwLimit_eq_of {a : ℕ → ℝ} {M : ℚ} (h : ∀ n, |a n| < M) :
bwLimit a M = Real.mk (.mk _ # isCauSeq_bwSeq_fst_of_abs_lt h) := by
  rw [bwLimit]; generalize_proofs; split_ifs; rfl

theorem bwSeq_fst_le_bwLimit {a : ℕ → ℝ} {M : ℚ} {n} (h : ∀ n, |a n| < M) :
(bwSeq a (-M) M n).1 ≤ bwLimit a M := by
  rw [bwLimit_eq_of h]
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  change Real.mk ⟨_, _⟩ ≤ Real.mk ⟨_, _⟩
  simp
  apply CauSeq.le_of_exists
  use n
  rintro i (hi : n ≤ i)
  dsimp
  exact bwSeq_fst_le_of_le hM hi

theorem bwLimit_le_bwSeq_snd {a : ℕ → ℝ} {M : ℚ} {n} (h : ∀ n, |a n| < M) :
bwLimit a M ≤ (bwSeq a (-M) M n).2 := by
  rw [bwLimit_eq_of h]
  have hM' : 0 < M
  · replace h := pos_of_abs_lt # h 0; simp at h; exact h
  have hM : -M < M; linarith
  change Real.mk ⟨_, _⟩ ≤ Real.mk ⟨_, _⟩
  simp
  apply CauSeq.le_of_exists
  use n
  rintro i (hi : n ≤ i)
  exact le_of_lt # bwSeq_fst_lt_snd hM

theorem exi_converges_subseq_of_bounded {a} (h : bounded a) :
∃ σ, Subseq σ ∧ converges (a ∘ σ) := by
  obtain ⟨M', h⟩ := h
  unfold boundedBy at h
  obtain ⟨M, h₁⟩ := exists_rat_gt M'
  replace h : ∀ n, |a n| < M
  · intro n; specialize h n; linarith
  clear! M'
  let σ := bwSubseq a M
  have hσ : Subseq σ := subseq_bwSubseq h
  use σ, subseq_bwSubseq h, bwLimit a M
  have hM' : 0 < M; have h₁ := pos_of_abs_lt # h 0; simp at h₁; exact h₁
  have hM : -M < M; linarith
  intro ε hε
  dsimp
  obtain ⟨N, hN⟩ := exists_nat_gt # (M * 2) / ε
  use N
  intro n hn
  obtain ⟨-, h₂, h₃⟩ := @bwSubseq_cnd a M n h
  change _ ≤ a (σ n) at h₂
  change a (σ n) ≤ _ at h₃
  have h₄ := @bwSeq_fst_le_bwLimit a M n h
  have h₅ := @bwLimit_le_bwSeq_snd a M n h
  rw [abs_lt]
  have H : (↑M + ↑M) / 2 ^ n < ε
  · rw [div_lt_comm₀] <;> try positivity
    have h₆ : 2 ^ N ≤ 2 ^ n
    · exact Nat.pow_le_pow_right (by norm_num) hn
    replace h₆ : (2 ^ N : ℝ) ≤ 2 ^ n; exact_mod_cast h₆
    apply lt_of_lt_of_le _ h₆
    clear h₆
    trans (N : ℝ); rwa [←mul_two]
    suffices h₆ : N < 2 ^ N; exact_mod_cast h₆
    exact Nat.lt_two_pow_self
  constructor
  · simp; apply lt_of_le_of_lt h₅
    rw [bwSeq_snd_eq_fst_sub hM]; simp; linarith
  · suffices : a (σ n) - ↑(bwSeq a (-M) M n).1 < ε; linarith
    rw [bwSeq_fst_eq_snd_sub hM]; simp; linarith