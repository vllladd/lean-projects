import Projects.Paramodulator.Defs

namespace Paramodulator

open Node

theorem zero_def : (0 : Node) = nil := rfl
theorem one_def : (1 : Node) = pair 0 0 := rfl

@[simp] theorem sizeOf_zero : sizeOf (0 : Node) = 1 := rfl
@[simp] theorem sizeOf_one : sizeOf (1 : Node) = 3 := rfl

@[simp]
theorem pair_ne_zero {a b} : pair a b ≠ 0 := by
  intro h; cases h

@[simp]
theorem zero_ne_pair {a b} : 0 ≠ pair a b :=
  ne_symm' pair_ne_zero

@[simp]
theorem pair_eq_one_iff {a b} : pair a b = 1 ↔ a = 0 ∧ b = 0 := by
  simp [one_def]

@[simp]
theorem one_eq_pair_iff {a b} : 1 = pair a b ↔ a = 0 ∧ b = 0 := by
  nth_rw 1 [eq_comm]; simp

@[simp]
theorem const_ne_zero {n} : const n ≠ 0 := by
  cases n <;> simp

@[simp]
theorem zero_ne_const {n} : 0 ≠ const n :=
  ne_symm' const_ne_zero

@[simp]
theorem const_eq_one_iff {n} : const n = 1 ↔ n = 0 := by
  cases n <;> simp

@[simp]
theorem one_eq_const_iff {n} : 1 = const n ↔ n = 0 := by
  nth_rw 1 [eq_comm]; simp

theorem const_eq_iff {n m} : const n = const m ↔ n = m := by
  symm; constructor; rintro rfl; rfl; intro h
  induction n generalizing m <;> simp at h; rw [h]
  nm n ih; cases m <;> simp at h; nm m; simp; exact ih h