import AP.Util.Logic

def linearIndep {α β : Type*} [One α] [Mul α] [HPow α ℤ α] [Membership α β] (set : β) : Prop :=
  ∀ x ∈ set, ∀ (xs : List # α × ℤ), (∀ y ∈ xs, y.1 ∈ set ∧ y.1 ≠ x) →
  (xs.map # λ y => y.1 ^ y.2).prod ≠ x

@[simp]
theorem linearIndep_empty_set {α : Type*} [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α] :
linearIndep (∅ : Set α) := by simp [linearIndep]

@[simp]
theorem linearIndep_empty_finset {α : Type*} [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α] :
linearIndep (∅ : Finset α) := by simp [linearIndep]

@[simp]
theorem linearIndep_empty_list {α : Type*} [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α] :
linearIndep ([] : List α) := by simp [linearIndep]