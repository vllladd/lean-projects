import AP.Util.Nat

namespace Fin

def next {n} (k : Fin n) : Fin n := by
  let k₁ := k.1 + 1
  use if k₁ = n then 0 else k₁
  split_ifs <;> omega

theorem toNat_next_eq {n} {k : Fin n} :
k.next.toNat = if k.toNat + 1 = n then 0 else k.toNat + 1 := by rfl

end Fin

def Nat.toFin (k : ℕ) {n} [NeZero n] : Fin n := Fin.ofNat _ k
def Int.toFin (k : ℤ) {n} [NeZero n] : Fin n := k.toNat.toFin

theorem Nat.toFin_congr {n m} [hn : NeZero n] [hm : NeZero m] {k₁ k₂ : ℕ}
(h₁ : n = m) (h₂ : k₁ = k₂) : (↑(k₁.toFin : Fin n) : ℕ) = (↑(k₂.toFin : Fin m) : ℕ) := by
  subst h₁ h₂; rfl

theorem Int.toFin_congr {n m} [hn : NeZero n] [hm : NeZero m] {k₁ k₂ : ℤ}
(h₁ : n = m) (h₂ : k₁ = k₂) : (↑(k₁.toFin : Fin n) : ℕ) = (↑(k₂.toFin : Fin m) : ℕ) := by
  subst h₁ h₂; rfl