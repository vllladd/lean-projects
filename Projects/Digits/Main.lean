import Projects.Digits.Basic

namespace Nat

def digSumAlt₁ (b n : ℕ) : ℕ :=
  if ¬b.Base then 0 else
  if n < b then n else
  n % b + digSumAlt₁ b (n / b)
decreasing_by nm hb h; simp_all; exact hb.div_lt h

-----

@[csimp]
theorem digSum_eq_digSumAlt₁ : digSum = digSumAlt₁ := by
  symm; ext b n
  by_cases hb : b ≤ 1
  · symm; rw [digSumAlt₁]
    simp [base_iff, hb]
  have hb' := hb
  replace hb : Base b := ⟨by omega⟩
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSumAlt₁ Nat.digSum
  simp [hb]
  split_ifs with h₁
  · rw [toDigList_of_lt_base h₁]; rfl
  simp at hb h₁
  have h₂ : n / b < n
  · rw [Nat.div_lt_iff_lt_mul (by simp)]
    rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  specialize ih _ h₂
  rw [ih]; clear ih
  rw [Nat.toDigList, if_neg (by omega)]
  rw [Nat.toDigList', if_neg (by omega), if_neg (by omega)]
  rw [add_comm, Nat.digSum, Nat.toDigList]
  simp [Nat.not_lt_of_le h₁, show n ≠ 0 by omega]