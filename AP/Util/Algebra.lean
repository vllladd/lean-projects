import AP.Util.Logic

def linearIndep {α β : Type*} [One α] [Mul α] [HPow α ℤ α] [Membership α β] (set : β) : Prop :=
  ∀ x ∈ set, ∀ (xs : List # α × ℤ), (∀ y ∈ xs, y.1 ∈ set ∧ y.1 ≠ x) →
  (xs.map # λ y => y.1 ^ y.2).prod ≠ x

variable {α : Type*} [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α]

@[simp]
theorem Set.linearIndep_empty : linearIndep (∅ : Set α) := by
  simp [linearIndep]

@[simp]
theorem Finset.linearIndep_empty : linearIndep (∅ : Finset α) := by
  simp [linearIndep]

@[simp]
theorem List.linearIndep_nil : linearIndep ([] : List α) := by
  simp [linearIndep]

@[simp]
theorem Set.linearIndep_singleton_iff {x} : linearIndep ({x} : Set α) ↔ x ≠ 1 := by
  simp [linearIndep]; constructor
  · rintro h rfl; specialize h []; simp at h
  · intro hx xs h; cases xs; simp [ne_symm' hx]; nm y xs; specialize h y.1 y.2; simp at h

@[simp]
theorem Finset.linearIndep_singleton_iff {x} : linearIndep ({x} : Finset α) ↔ x ≠ 1 := by
  simp [linearIndep]; constructor
  · rintro h rfl; specialize h []; simp at h
  · intro hx xs h; cases xs; simp [ne_symm' hx]; nm y xs; specialize h y.1 y.2; simp at h

@[simp]
theorem List.linearIndep_singleton_iff {x : α} : linearIndep [x] ↔ x ≠ 1 := by
  simp [linearIndep]; constructor
  · rintro h rfl; specialize h []; simp at h
  · intro hx xs h; cases xs; simp [ne_symm' hx]; nm y xs; specialize h y.1 y.2; simp at h