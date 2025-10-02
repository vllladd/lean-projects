import AP.Util

namespace DigitalRoot

def digSum (n : ℕ) : ℕ :=
  if n ≤ 9 then n else n % 10 + digSum (n / 10)

@[simp]
theorem digSum_le {n} : digSum n ≤ n := by
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSum
  split_ifs with h₁; rfl
  push_neg at h₁
  specialize ih (n / 10) # by omega
  omega

@[simp]
theorem digSum_lt_iff_10_le {n} : digSum n < n ↔ 10 ≤ n := by
  convert_to _ ↔ 9 < n
  constructor <;> intro h
  · contrapose! h; simp [digSum, h]
  unfold digSum
  rw [←ite_not]; simp [h]
  change 10 ≤ n at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp
  suffices h₂ : n % 10 + n / 10 + 1 < n + 10
  · linarith [digSum_le (n := n / 10 + 1)]
  omega

def digRoot (n : ℕ) : ℕ :=
  let s := digSum n
  if s ≤ 9 then s else digRoot s
decreasing_by
  nm h; subst s; push_neg at h
  simp; linarith [digSum_le (n := n)]

def digRoot' (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 9 = 0 then 9
  else n % 9

@[simp]
theorem digRoot_zero : digRoot 0 = 0 := by
  native_decide

@[simp]
theorem digRoot'_zero : digRoot' 0 = 0 := by
  decide

theorem digRoot_eq_digRoot' : digRoot = digRoot' := by
  ext n
  sorry