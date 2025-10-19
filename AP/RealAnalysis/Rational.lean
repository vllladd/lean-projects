import AP.RealAnalysis.Cauchy

namespace RealAnalysis

open Classical in noncomputable
def monoLtRatSeq (x : ℝ) (n : ℕ) : ℚ :=
match n with
| 0 => Classical.epsilon # λ r => x - 1 < r ∧ r < x
| n + 1 => Classical.epsilon # λ r => monoLtRatSeq x n < r ∧ r < x

theorem monoLtRatSeq_cnd_zero {x : ℝ} : ∃ (r : ℚ), x - 1 < r ∧ r < x := by
  apply exists_rat_btwn; linarith

theorem monoLtRatSeq_zero_btwn {x : ℝ} :
x - 1 < monoLtRatSeq x 0 ∧ monoLtRatSeq x 0 < x :=
  Classical.epsilon_spec monoLtRatSeq_cnd_zero

theorem monoLtRatSeq_cnd_succ {x : ℝ} {n : ℕ} :
∃ (r : ℚ), monoLtRatSeq x n < r ∧ r < x := by
  induction n
  · exact_mod_cast exists_rat_btwn # @monoLtRatSeq_zero_btwn x |>.2
  nm n ih
  simp [monoLtRatSeq]
  have h₁ := Classical.epsilon_spec ih
  generalize Classical.epsilon (λ (y : ℚ) =>
    monoLtRatSeq x n < y ∧ y < x) = r at h₁ ⊢
  have h₂ : r < x; linarith
  exact_mod_cast exists_rat_btwn h₂

theorem monoLtRatSeq_succ_btwn {x : ℝ} {n : ℕ} :
monoLtRatSeq x n < monoLtRatSeq x (n + 1) ∧ monoLtRatSeq x (n + 1) < x :=
  Classical.epsilon_spec # @monoLtRatSeq_cnd_succ x n

theorem monoLtRatSeq_lt₀ {x : ℝ} {n : ℕ} : monoLtRatSeq x n < x := by
  cases n
  · exact monoLtRatSeq_zero_btwn.2
  · exact monoLtRatSeq_succ_btwn.2

@[simp]
theorem monoLtRatSeq_lt_succ {x : ℝ} {n : ℕ} :
monoLtRatSeq x n < monoLtRatSeq x (n + 1) :=
  monoLtRatSeq_succ_btwn.1

theorem monoLtRatSeq_lt_of_lt {x : ℝ} {k n : ℕ} (h : k < n) :
monoLtRatSeq x k < monoLtRatSeq x n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h; clear h
  induction n; simp; nm n ih
  apply ih.trans; clear ih; simp [←add_assoc]

@[simp]
theorem monoLt_monoLtRatSeq {x : ℝ} : monoLt (monoLtRatSeq x ·) := by
  intro i j h; simp; exact monoLtRatSeq_lt_of_lt h

@[simp]
theorem tendsTo_monoLtRatSeq {x : ℝ} : tendsTo (monoLtRatSeq x ·) x := by
  intro e he
  sorry

-- #check 0 #exit

theorem exi_monoLt_rat_tendsTo_real {x : ℝ} :
∃ (a : ℕ → ℚ), monoLt (a ·) ∧ tendsTo (a ·) x := by
  use monoLtRatSeq x; simp

-- #check 0 #exit

/- todo:
* 1, 1.4, 1.41, 1.412 ... -> sqrt 2
-/