import AP.Util

namespace Misc

namespace P1

noncomputable
def f (n : ℕ) : ℝ :=
  let r := (n : ℝ)
  let a := r ^ r⁻¹
  (a ^ ·)^[n] 1

example : f 2 = √2 ^ √2 := by
  simp [f, Real.sqrt_eq_rpow]

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
  rw [←Real.rpow_mul # by linarith]
  convert_to _ < r ^ 1; simp
  convert @Real.rpow_lt_rpow_left_iff r (r⁻¹ * a) 1 h₂
    |>.mpr _; simp
  rw [mul_comm, ←div_eq_mul_inv]
  rw [div_lt_iff₀ # by linarith]
  simpa

example : f 2003 < 2003 := by
  apply f_lt; simp

end P1

namespace P2

def le (n m : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), f 0 = n ∧ f k = m ∧ ∀ k, f k.succ = (f k).succ

theorem le_iff_nat_le {n m} : le n m ↔ n ≤ m := by
  constructor
  · rintro ⟨f, k, rfl, rfl, h⟩; induction k; rfl; rw [h]; linarith
  · intro h; obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    use (n + ·); simp [add_assoc]

end P2