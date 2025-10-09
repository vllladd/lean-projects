import AP.Util

namespace Misc

namespace A1

open Real

noncomputable
def f (n : ℕ) : ℝ :=
  let r := (n : ℝ)
  let a := r ^ r⁻¹
  (a ^ ·)^[n] 1

example : f 2 = √2 ^ √2 := by
  simp [f, sqrt_eq_rpow]

theorem f_lt {n} (h : 1 < n) : f n < n := by
  simp [f]
  obtain ⟨k, hk⟩ := hv n
  nth_rw 3 [←hk]
  clear hk
  generalize hr : (n : ℝ) = r
  have h₂ : 1 < r; rwa [←hr, Nat.one_lt_cast]
  clear! n
  induction k; simpa
  nm k ih
  rw [Function.iterate_succ']; simp
  generalize (λ x => (r ^ r⁻¹) ^ x)^[k] 1 = a at ih ⊢
  rw [←rpow_mul # by linarith]
  convert_to _ < r ^ 1; simp
  convert @rpow_lt_rpow_left_iff r (r⁻¹ * a) 1 h₂
    |>.mpr _; simp
  rw [mul_comm, ←div_eq_mul_inv]
  rw [div_lt_iff₀ # by linarith]
  simpa

example : f 2003 < 2003 := by
  apply f_lt; simp

end A1 namespace A2 -----

def le (n m : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), f 0 = n ∧ f k = m ∧ ∀ k, f k.succ = (f k).succ

theorem le_iff_nat_le {n m} : le n m ↔ n ≤ m := by
  constructor
  · rintro ⟨f, k, rfl, rfl, h⟩; induction k; rfl; rw [h]; linarith
  · intro h; obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    use (n + ·); simp [add_assoc]

end A2 namespace A3 -----

open Real

theorem sum_mul_le_112_of_sum_eq_12 {a b c : ℝ}
(ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 12) :
a * b * c + a * b + b * c + c * a ≤ 112 := by
  have h₁ : (a * b * c) ^ (3⁻¹ : ℝ) ≤ (a + b + c) / 3
  · apply gm_le_am_3 <;> positivity
  replace h₁ : a * b * c ≤ (a + b + c) ^ 3 / 27
  · rw [←rpow_le_rpow_iff (z := 3)] at h₁ <;> try positivity
    rw [rpow_inv_rpow] at h₁ <;> try positivity
    field_simp at h₁; norm_num at h₁; exact h₁
  replace h₁ : a * b * c ≤ 64
  · rw [h] at h₁; norm_num at h₁; exact h₁
  suffices h₂ : a * b + b * c + c * a <= 48; linarith
  replace h₁ : c = 12 - (a + b); linarith
  suffices h₂ : a * b + (a + b) * (12 - (a + b)) ≤ 48
  · subst h₁; ring_nf at h₂ ⊢; exact h₂
  have h₂ : √(a * b) ≤ (a + b) / 2
  · apply gm_le_am_2 <;> positivity
  replace h₂ : a * b ≤ (a + b) ^ (2 : ℝ) / 4
  · rw [←rpow_le_rpow_iff (z := 2)] at h₂ <;> try positivity
    rw [sqrt_eq_rpow, one_div, rpow_inv_rpow] at h₂ <;> try positivity
    field_simp at h₂; norm_num at h₂; simpa
  generalize a + b = x at h₁ h₂ ⊢
  suffices h₃ : x ^ (2 : ℝ) / 4 + x * (12 - x) ≤ 48; linarith
  suffices h₃ : 0 ≤ (x - 8) ^ 2; simp; linarith
  apply sq_nonneg