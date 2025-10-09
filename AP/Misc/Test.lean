import AP.Util

namespace Misc.Test

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