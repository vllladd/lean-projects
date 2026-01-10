import AP.Util.Int

namespace Fin

variable {n : ℕ}

def next (k : Fin n) : Fin n := by
  let k₁ := k.1 + 1
  use if k₁ = n then 0 else k₁
  split_ifs <;> omega

theorem toNat_next_eq {k : Fin n} :
k.next.toNat = if k.toNat + 1 = n then 0 else k.toNat + 1 := by rfl

@[simp]
theorem val_eq_val_iff {a b : Fin n} : a.1 = b.1 ↔ a = b := by
  omega

end Fin

def Nat.toFin (k : ℕ) {n} [NeZero n] : Fin n := Fin.ofNat _ k
def Int.toFin (k : ℤ) {n} [NeZero n] : Fin n := k.toNat.toFin

theorem Nat.toFin_congr {n m} [hn : NeZero n] [hm : NeZero m] {k₁ k₂ : ℕ}
(h₁ : n = m) (h₂ : k₁ = k₂) : (↑(k₁.toFin : Fin n) : ℕ) = (↑(k₂.toFin : Fin m) : ℕ) := by
  subst h₁ h₂; rfl

theorem Int.toFin_congr {n m} [hn : NeZero n] [hm : NeZero m] {k₁ k₂ : ℤ}
(h₁ : n = m) (h₂ : k₁ = k₂) : (↑(k₁.toFin : Fin n) : ℕ) = (↑(k₂.toFin : Fin m) : ℕ) := by
  subst h₁ h₂; rfl

theorem Nat.toFin_eq_self_of {k n : ℕ} [hk : NeZero k] (h : n < k) : (n.toFin : Fin k) = n := by
  rw! [toFin, Fin.ofNat, Nat.mod_eq_of_lt h]; rfl

theorem Int.toFin_eq_self_of {k : ℕ} {z : ℤ} [hk : NeZero k]
(h₁ : 0 ≤ z) (h₂ : z < k) : (z.toFin : Fin k) = z := by
  rw [toFin, Nat.toFin_eq_self_of # by grind, toNat_eq_self_of h₁]

theorem Int.toFin_eq_toNat_of {k : ℕ} {z : ℤ} [hk : NeZero k]
(h₁ : 0 ≤ z) (h₂ : z < k) : (z.toFin : Fin k) = z.toNat := by
  rw [toFin, Nat.toFin_eq_self_of]; grind