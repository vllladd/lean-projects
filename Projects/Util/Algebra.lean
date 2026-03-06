import Projects.Util.Logic

def linearIndep {α β : Type*} [One α] [Mul α] [HPow α ℤ α] [Membership α β] (set : β) : Prop :=
  ∀ x ∈ set, ∀ (xs : List # α × ℤ), xs ≠ [] ∧ (∀ y ∈ xs, y.1 ∈ set ∧ y.1 ≠ x) →
  (xs.map # λ y => y.1 ^ y.2).prod ≠ x

variable {α : Type*} [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α]

@[simp]
theorem Set.linearIndep_empty : linearIndep (∅ : Set α) := by
  simp [linearIndep]

@[simp]
theorem Set.linearIndep_singleton {x} : linearIndep ({x} : Set α) := by
  simp [linearIndep]; intro xs hx h; cases xs; simp at hx
  nm y xs; specialize h y.1 y.2; simp at h

theorem add_eq_iff_eq_sub {α : Type*} [AddGroup α] {a b c : α} : a + b = c ↔ a = c - b :=
  eq_sub_iff_add_eq.symm