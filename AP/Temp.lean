import AP.Util

section logic

theorem ne_def {α : Type*} {x y : α} : x ≠ y ↔ ¬(x = y) := by rfl

-- #check 0 #exit

end logic

namespace Set

variable {α β γ : Type*}
variable {s s₁ s₂ : Set α}

theorem ssubset_of (x : α) (h₁ : s₁ ⊆ s₂) (h₂ : x ∉ s₁) (h₃ : x ∈ s₂) : s₁ ⊂ s₂ := by
  use h₁; contrapose! h₂; exact h₂ h₃

theorem ncard_eq_ite : s.ncard =
have := Classical.propDecidable
if s.Finite then s.ncard else 0 := by
  simp; exact Infinite.ncard

-- #check 0 #exit

end Set

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}

theorem ssubset_of (x : α) (h₁ : s₁ ⊆ s₂) (h₂ : x ∉ s₁) (h₃ : x ∈ s₂) : s₁ ⊂ s₂ := by
  use h₁; rintro rfl; contradiction

-- #check 0 #exit

end Set'