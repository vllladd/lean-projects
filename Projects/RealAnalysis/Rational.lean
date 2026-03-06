import Projects.RealAnalysis.Cauchy

namespace RealAnalysis

open Classical in noncomputable
def monoLtRatSeq (x : ℝ) (n : ℕ) : ℚ :=
Classical.epsilon # λ r => x - 1 / 2 ^ n < r ∧ r < x - 1 / 2 ^ (n + 1)

theorem monoLtRatSeq_cnd {x : ℝ} {n : ℕ} :
∃ (r : ℚ), x - 1 / 2 ^ n < r ∧ r < x - 1 / 2 ^ (n + 1) := by
  apply exists_rat_btwn; simp
  rw [inv_lt_inv₀] <;> try positivity
  suffices h : 2 ^ n < 2 ^ (n + 1); exact_mod_cast h
  rw [Nat.pow_lt_pow_iff_right] <;> linarith

theorem monoLtRatSeq_btwn {x : ℝ} {n : ℕ} :
x - 1 / 2 ^ n < monoLtRatSeq x n ∧ monoLtRatSeq x n < x - 1 / 2 ^ (n + 1) :=
  Classical.epsilon_spec monoLtRatSeq_cnd

theorem lt_monoLtRatSeq {x : ℝ} {n : ℕ} :
x - 1 / 2 ^ n < monoLtRatSeq x n := monoLtRatSeq_btwn.1

theorem monoLtRatSeq_lt {x : ℝ} {n : ℕ} :
monoLtRatSeq x n < x - 1 / 2 ^ (n + 1) := monoLtRatSeq_btwn.2

theorem lt_monoLtRatSeq₀ {x : ℝ} {n : ℕ} : x - 1 < monoLtRatSeq x n := by
  apply lt_of_le_of_lt _ lt_monoLtRatSeq
  simp; field_simp
  suffices h : (1 : ℝ) ≤ 2 ^ n; linarith
  suffices h : 1 ≤ 2 ^ n; exact_mod_cast h
  exact Nat.one_le_two_pow

theorem monoLtRatSeq_lt₀ {x : ℝ} {n : ℕ} : monoLtRatSeq x n < x := by
  apply lt_of_lt_of_le monoLtRatSeq_lt; field_simp; linarith

theorem monoLtRatSeq_lt_succ {x : ℝ} {n : ℕ} :
monoLtRatSeq x n < monoLtRatSeq x (n + 1) := by
  exact_mod_cast monoLtRatSeq_lt.trans lt_monoLtRatSeq

theorem monoLtRatSeq_lt_of_lt {x : ℝ} {k n : ℕ} (h : k < n) :
monoLtRatSeq x k < monoLtRatSeq x n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h; clear h
  induction n; simp [monoLtRatSeq_lt_succ]; nm n ih
  apply ih.trans; simp [←add_assoc, monoLtRatSeq_lt_succ]

theorem monoLt_monoLtRatSeq {x : ℝ} : monoLt (monoLtRatSeq x ·) := by
  intro i j h; simp; exact monoLtRatSeq_lt_of_lt h

theorem tendsTo_monoLtRatSeq {x : ℝ} : tendsTo (monoLtRatSeq x ·) x := by
  rw [tendsTo_iff_eps_lt_one]
  intro e he h
  obtain ⟨N, hN⟩ := exists_nat_gt # Real.logb (1 / 2) e
  use N
  intro n hn
  rw [abs_sub_lt_iff']
  symm; constructor
  · linarith [@monoLtRatSeq_lt₀ x n]
  suffices : 1 / 2 ^ n < e; linarith [@lt_monoLtRatSeq x n]
  apply lt_of_le_of_lt (b := 1 / 2 ^ N)
  · field_simp
    suffices h : 2 ^ N ≤ 2 ^ n; exact_mod_cast h
    rwa [Nat.pow_le_pow_iff_right]
    norm_num
  suffices h₁ : (1 / 2) ^ (N : ℝ) < e
  · simp at h₁ ⊢; exact h₁
  rw [Real.logb_lt_iff_lt_rpow_of_base_lt_one] at hN
    <;> try first | positivity | norm_num
  exact_mod_cast hN

theorem exi_monoLt_rat_tendsTo_real {x : ℝ} :
∃ (a : ℕ → ℚ), monoLt (a ·) ∧ tendsTo (a ·) x :=
  ⟨monoLtRatSeq x, monoLt_monoLtRatSeq, tendsTo_monoLtRatSeq⟩

theorem exi_monoLe_rat_tendsTo_real {x : ℝ} :
∃ (a : ℕ → ℚ), monoLe (a ·) ∧ tendsTo (a ·) x := by
  obtain ⟨a, h₁, h₂⟩ := @exi_monoLt_rat_tendsTo_real x
  use a, monoLe_of_monoLt h₁, h₂

noncomputable
def ratApprox (b : ℕ) (x : ℝ) (n : ℕ) : ℚ :=
  ⌊x * b ^ n⌋₊ / b ^ n

theorem ratApprox_le {b : ℕ} {x : ℝ} {n : ℕ}
(hb : 2 ≤ b) (hx : 0 ≤ x) : ratApprox b x n ≤ x := by
  simp [ratApprox]
  field_simp
  apply Nat.floor_le
  positivity

theorem lt_ratApprox {b : ℕ} {x : ℝ} {n : ℕ}
(hb : 2 ≤ b) : x - 1 / b ^ n < ratApprox b x n := by
  simp [ratApprox]
  field_simp
  apply Nat.sub_one_lt_floor

theorem tendsTo_ratApprox {b : ℕ} {x : ℝ}
(hb : 2 ≤ b) (hx : 0 ≤ x) : tendsTo (ratApprox b x ·) x := by
  rw [tendsTo_iff_eps_lt_one]
  intro e he he'
  obtain ⟨N, hN⟩ := exists_nat_gt # Real.logb (1 / b) e
  rw [Real.logb_lt_iff_lt_rpow_of_base_lt_one] at hN
  rotate_left
  · positivity
  · field_simp; simp; linarith
  · exact he
  use N
  intro n hn
  apply hN.trans'
  clear hN
  rw [abs_sub_lt_iff]
  constructor
  · suffices : 0 < (1 / b : ℝ) ^ (N : ℝ)
    · linarith [@ratApprox_le b x n hb hx]
    positivity
  suffices : 1 / (b : ℝ) ^ n ≤ (1 / b : ℝ) ^ (N : ℝ)
  · linarith [@lt_ratApprox b x n hb]
  simp
  rw [inv_le_inv₀] <;> try positivity
  suffices h : b ^ N ≤ b ^ n; exact_mod_cast h
  rwa [Nat.pow_le_pow_iff_right]
  linarith

example : tendsTo (ratApprox 10 √2 ·) √2 := by
  apply tendsTo_ratApprox <;> norm_num