import AP.Util.Nat

namespace Fin

def next {n} (k : Fin n) : Fin n := by
  let k₁ := k.1 + 1
  use if k₁ = n then 0 else k₁
  split_ifs <;> omega

theorem toNat_next_eq {n} {k : Fin n} :
k.next.toNat = if k.toNat + 1 = n then 0 else k.toNat + 1 := by rfl