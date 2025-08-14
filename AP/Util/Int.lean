import AP.Util.Function

namespace Int

theorem even_iff_exi {n : ℤ} : Even n ↔ ∃ k, n = k * 2 := by
  rw [Even]; ring_nf

theorem odd_iff_exi {n : ℤ} : Odd n ↔ ∃ k, n = k * 2 + 1 := by
  rw [Odd]; ring_nf

theorem mod_2_ind {P : ℤ → Prop}
(h₁ : ∀ n, P (n * 2)) (h₂ : ∀ n, P (n * 2 + 1)) (n : ℤ) : P n := by
  rcases Int.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := even_iff_exi.mp h; apply h₁
  · obtain ⟨k, rfl⟩ := odd_iff_exi.mp h; apply h₂

theorem not_even_mul_2_succ {n : ℤ} : ¬Even (n * 2 + 1) := by simp

@[simp]
theorem not_odd_mul_2 {n : ℤ} : ¬Odd (n * 2) := by simp

theorem le_one_iff {n : ℤ} (h : 0 ≤ n) : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  cases n; nm n; cases n; simp; nm n; cases n; simp; nm n; simp
  have h₁ := Int.ofNat_zero_le n; apply iff_of_not_and
  simp; simp; constructor <;> linarith; simp at h

theorem of_between_succ {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a + 1) :
b = a ∨ b = a + 1 := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h₁; simp at h₂ ⊢
  cases k; nm k; generalize hk : Int.ofNat k = k at *
  rw [le_one_iff] at h₂; exact h₂; simp [←hk]; simp at h₁

theorem add_div_eq {a b : ℤ} (h : 0 < b) : (a + b) / b = a / b + 1 := by
  rw [Int.add_ediv_of_pos h]; have h₁ : b ≠ 0 := (Int.ne_of_lt h).symm
  simp [Int.ediv_self h₁]; exact Int.emod_lt_of_pos _ h

@[simp]
theorem negSucc_succ {n : ℕ} :
Int.negSucc (n + 1) = Int.negSucc n - 1 := by rfl

@[simp]
theorem even_succ_iff {n : ℤ} : Even (n + 1) ↔ Odd n := by
  simp [Int.even_add_one]

@[simp]
theorem odd_succ_iff {n : ℤ} : Odd (n + 1) ↔ Even n := by
  rw [←Int.not_even_iff_odd, even_succ_iff]; simp

theorem succ_div_2_eq_div_iff {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 ↔ Even n := by
  induction n using mod_2_ind <;> nm n
  · simp at hp ⊢; cases n; nm n; simp; induction n; rfl
    nm n ih; specialize ih (by simp); simp [add_mul]
    rw [add_assoc]; nth_rewrite 2 [add_comm]; rw [←add_assoc]
    have h₁ := @add_div_eq ((n : ℤ) * 2 + 1) 2 # Int.zero_le_ofNat _
    rw [h₁, ih]; simp at hp
  simp; rw [add_assoc]; simp
  rw [@add_div_eq ((n : ℤ) * 2) 2 # Int.zero_le_ofNat _]
  rw [eq_comm]; simp; cases n <;> nm n
  simp at hp ⊢; induction n; simp; nm n ih
  specialize ih (by linarith); simp; rw [add_mul, add_assoc]
  nth_rewrite 2 [add_comm]; rw [←add_assoc]; simp
  rw [@add_div_eq ((n : ℤ) * 2 + 1) 2 # Int.zero_le_ofNat _]
  simpa; have h₁ := Int.negSucc_lt_zero n; linarith

theorem succ_div_2_eq_div_succ_iff {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 + 1 ↔ Odd n := by
  by_cases hn : n = 0; simp [hn]; obtain ⟨k, hk⟩ := hv # n - 1
  replace hk := congrArg (· + 1) hk; simp at hk; subst hk
  replace hp : 0 ≤ k := by
    cases k <;> nm k; simp only [Int.ofNat_eq_coe, Nat.cast_nonneg]
    cases k; simp only [Int.reduceNegSucc, neg_add_cancel,
      not_true_eq_false] at hn
    nm k; rw [negSucc_succ] at hp
    have := Int.negSucc_lt_zero k; linarith
  rw [add_assoc]; simp
  rw [@add_div_eq k 2 # Int.zero_le_ofNat _]
  rw [eq_comm]; simp; exact succ_div_2_eq_div_iff hp

theorem succ_div_2_eq_or_eq {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1 := by
  rcases Int.even_or_odd n with h | h
  · rw [←succ_div_2_eq_div_iff hp] at h; left; exact h
  · rw [←succ_div_2_eq_div_succ_iff hp] at h; right; exact h

theorem succ_div_2_eq_div_iff' {n : ℤ} (hp : 0 ≤ n) :
n / 2 = (n + 1) / 2 ↔ Even n := by
  rw [eq_comm]; exact succ_div_2_eq_div_iff hp

@[simp]
theorem succ_div_2_eq_div_succ_iff' {n : ℤ} (hp : 0 ≤ n) :
n / 2 + 1 = (n + 1) / 2 ↔ Odd n := by
  rw [eq_comm]; exact succ_div_2_eq_div_succ_iff hp

theorem mul_2_succ_div_2_eq {n : ℤ}
(hp : 0 ≤ n) : (n * 2 + 1) / 2 = n := by
  suffices (n * 2 + 1) / 2 = n * 2 / 2 by simp at this; assumption
  rw [succ_div_2_eq_div_iff # by linarith]; simp

@[simp]
theorem max_abs_eq_zero_iff {n m : ℤ} : max |n| |m| = 0 ↔ n = 0 ∧ m = 0 := by
  rw [max_def']; aesop