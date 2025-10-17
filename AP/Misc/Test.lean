import AP.Util

namespace Misc.Test

-- set_option linter.unusedVariables false in
-- example {a b c : ℝ}
-- (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c)
-- (ha₂ : 0 ≤ a) (hb₂ : 0 ≤ b) (hc₂ : 0 ≤ c)
-- (ha₃ : a ≠ 0) (hb₃ : b ≠ 0) (hc₃ : c ≠ 0)
-- (ha₄ : 1 < a) (hb₄ : 1 < b) (hc₄ : 1 < c) :
-- a * c < b * c ↔ a < b := by
--   exact?
-- 
-- #check 0 #exit

namespace A1

def le (n m : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), f 0 = n ∧ f k = m ∧ ∀ k, f k.succ = (f k).succ

theorem le_iff_nat_le {n m} : le n m ↔ n ≤ m := by
  constructor
  · rintro ⟨f, k, rfl, rfl, h⟩; induction k; rfl; rw [h]; linarith
  · intro h; obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    use (n + ·); simp [add_assoc]

end A1 namespace A2 -----

def f : ℕ → ℕ → ℕ
| n, 0 => n
| n, m + 1 => f (n + 1) m

theorem thm₁ {n m} : f n (m + 1) = f n m + 1 := by
  induction m generalizing n <;> simp_all [f]

theorem thm₂ {n} : f n n = n * 2 := by
  rw [Nat.mul_two]; apply n.rec (motive := λ k => f n k = n + k)
  simp_all [f]; intros; simp_all [thm₁]; rfl

end A2

-----

end Misc.Test

namespace Real

theorem aux₁ {a : ℕ → ℚ} : IsCauSeq (abs : ℚ → ℚ) a ↔
∀ (ε : ℚ), 0 < ε → ε < 1 → ∃ (N : ℕ), ∀ n ≥ N, |a n - a N| < ε := by
  use λ h ε hε _ => h ε hε
  intro h ε hε'
  by_cases hε : ε < 1
  · apply h <;> assumption
  push_neg at hε
  specialize h (ε + 1)⁻¹ (by positivity) _
  · apply inv_lt_of_inv_lt₀ rfl; linarith
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  apply h.trans
  apply lt_of_lt_of_le (b := ε⁻¹)
  · rw [inv_lt_inv₀] <;> try positivity;; simp
  exact Rat.inv_le_self_of_one_le hε

-- #check 0 #exit

theorem aux₂ : IsCauSeq (abs : ℚ → ℚ) (· + 1)⁻¹ := by
  rw [aux₁]
  intro ε hε hε'
  obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
  use n
  intro j hj
  simp
  rw [abs_of_nonpos]
  rotate_left
  · simp
    replace hj : (n : ℚ) + 1 ≤ j + 1; simpa
    rwa [inv_le_inv₀] <;> positivity
  simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  rename' j => k
  clear hj
  field_simp
  replace hn : (n + 1 : ℚ)⁻¹ < ε
  · rw [inv_lt_comm₀] <;> try positivity;; linarith
  rw [mul_comm, div_mul_eq_div_div]
  have h₁ : (k : ℚ) / (n + k + 1) < 1
  · rw [div_lt_comm₀] <;> try positivity;; linarith
  suffices : 1 / (n + 1) < ε
  · rw [div_lt_iff₀] <;> try positivity
    apply h₁.trans
    rw [inv_lt_iff_one_lt_mul₀] at hn <;> try positivity
    exact hn
  rwa [←inv_eq_one_div]

theorem aux₃ : mk ⟨_, aux₂⟩ = 0 := by
  convert_to _ = ((0 : ℕ) : ℝ); simp
  change _ = mk ⟨_, _⟩
  simp
  rw [mk_eq]
  intro e (he : 0 < e)
  dsimp
  obtain ⟨N, hN⟩ := exists_nat_gt # max e e⁻¹
  use N
  rintro n hn
  simp
  rw [abs_of_pos] <;> try positivity
  rw [max_lt_iff] at hN
  rcases hN with ⟨h₁, h₂⟩
  wlog h₃ : e ≤ 1 with ih
  · push_neg at h₃
    specialize ih e⁻¹ (by positivity) N n hn h₂ (by simpa) #
      inv_le_one_of_one_le₀ # le_of_lt h₃
    exact ih.trans # Rat.inv_lt_self_of_one_lt h₃
  rw [inv_lt_iff_one_lt_mul₀] at h₂ ⊢ <;> try positivity
  rw [mul_comm]
  apply h₂.trans
  rw [mul_lt_mul_iff_of_pos_right he]
  suffices H : N < n + 1; exact_mod_cast H
  linarith

-- #check 0 #exit

theorem aux₄ : ¬∀ {a : ℕ → ℚ} {x ε : ℝ} (ha : IsCauSeq abs a)
(_ : ∃ N, ∀ n, N ≤ n → |a n - x| < ε), |x - mk ⟨a, ha⟩| < ε := by
  push_neg
  use (· + 1)⁻¹
  use 1
  use 1
  use aux₂
  constructor
  · dsimp
    use 0
    intro n hn
    simp
    rw [abs_of_nonpos]
    rotate_left
    · simp
      rw [inv_le_one_iff₀]
      simp
    simp
    positivity
  rw [aux₃]
  norm_num