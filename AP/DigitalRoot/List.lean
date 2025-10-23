import AP.DigitalRoot.Basic

namespace DigitalRoot

def digRootList (b : ℕ) (xs : List ℕ) : ℕ :=
  digRoot b xs.sum

variable {b} [hb : Base b]

@[simp]
theorem digRootList_lt_base {n} : digRootList b n < b := by
  simp [digRootList]

@[simp]
theorem digRootList_le_base {n} : digRootList b n ≤ b := by
  simp [digRootList]