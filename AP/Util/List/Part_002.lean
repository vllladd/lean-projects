import AP.Util.List.Part_001
import AP.Util.List.BirdWadler

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

@[simp]
theorem sequence_singleton : sequence [xs] = xs.map ({·}) := by
  simp [sequence_cons]

@[simp]
theorem combinations_one : xs.combinations 1 = xs.map ([·]) := by
  simp [combinations]

theorem combinations_succ {n} : xs.combinations (n + 1) =
xs.flatMap (λ x => xs.combinations n |>.map (x :: ·)) := by
  simp [combinations, replicate_succ, sequence_cons]

@[simp]
theorem length_combinations {n} : (xs.combinations n).length = xs.length ^ n := by
  induction n
  · simp
  nm n ih
  rw [combinations_succ]
  simp [ih, pow_succ']

@[simp]
theorem mem_combinations {n} : ys ∈ xs.combinations n ↔ ys.length = n ∧ ys ⊆ xs := by
  induction n generalizing xs ys
  · simp
    rintro rfl; simp
  nm n ih
  simp [combinations_succ, ih]; clear ih
  constructor
  · rintro ⟨x, hx, ys, ⟨h₁, h₂⟩, rfl⟩
    simp; tauto
  · rintro ⟨h₁, h₂⟩
    cases ys <;> simp at h₁
    nm y ys
    simp at h₂
    choose hy h₂ using h₂
    use y, hy, ys

section

variable [ha : LinearOrder α]
include ha

@[simp]
theorem sortedLe_cons {x} : (x :: xs).SortedLE ↔ (∀ y ∈ xs, x ≤ y) ∧ xs.SortedLE := by
  simp [sortedLE_iff_pairwise]

@[simp]
theorem sortedLt_cons {x} : (x :: xs).SortedLT ↔ (∀ y ∈ xs, x < y) ∧ xs.SortedLT := by
  simp [sortedLT_iff_pairwise]

@[simp]
theorem sortedLe_snoc {x} : (xs ++ [x]).SortedLE ↔ xs.SortedLE ∧ ∀ y ∈ xs, y ≤ x := by
  simp [sortedLE_iff_pairwise]

@[simp]
theorem sortedLT_snoc {x} : (xs ++ [x]).SortedLT ↔ xs.SortedLT ∧ ∀ y ∈ xs, y < x := by
  simp [sortedLT_iff_pairwise]

@[grind =]
theorem sortedLE_append : (xs ++ ys).SortedLE ↔
xs.SortedLE ∧ ys.SortedLE ∧ ∀ x ∈ xs, ∀ y ∈ ys, x ≤ y := by
  simp [sortedLE_iff_pairwise, pairwise_append]

@[grind =]
theorem sortedLT_append : (xs ++ ys).SortedLT ↔
xs.SortedLT ∧ ys.SortedLT ∧ ∀ x ∈ xs, ∀ y ∈ ys, x < y := by
  simp [sortedLT_iff_pairwise, pairwise_append]

end

theorem head!_eq_getd_head [ha : Inhabited α] : xs.head! = xs.head?.getd := by
  cases xs <;> rfl

@[simp]
theorem head!_mem_iff [ha : Inhabited α] : xs.head! ∈ xs ↔ xs ≠ [] := by
  cases xs <;> simp

theorem head!_mem [ha : Inhabited α] (h : xs ≠ []) : xs.head! ∈ xs := by
  simpa