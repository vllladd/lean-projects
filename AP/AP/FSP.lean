import AP.AP.MkFold

namespace AP

structure FSP : Type where
  get : ℕ → Set PointZ

namespace FSP

variable {a b c : FSP}

instance : EmptyCollection FSP := ⟨⟨λ _ => ∅⟩⟩
theorem empty_def : (∅ : FSP) = ⟨λ _ => ∅⟩ := rfl

instance : Inhabited FSP := ⟨∅⟩
theorem default_def : (default : FSP) = ∅ := rfl

instance : Union FSP := ⟨λ a b => ⟨λ i => a.get i ∪ b.get i⟩⟩
theorem union_def : a ∪ b = ⟨λ i => a.get i ∪ b.get i⟩ := rfl

instance : Inter FSP := ⟨λ a b => ⟨λ i => a.get i ∩ b.get i⟩⟩
theorem inter_def : a ∩ b = ⟨λ i => a.get i ∩ b.get i⟩ := rfl

def next (a : FSP) : FSP := .mk # λ i =>
  match i with
  | 0 => a.get 0 ∪ a.get 1
  | n + 1 => a.get # n + 2

def hasLe (a : FSP) (n : ℕ) (p : PointZ) : Prop :=
  ∀ k ≤ n, p ∉ a.get k
  
@[simp]
theorem hasLe_next {n p} : a.next.hasLe n p ↔ a.hasLe (n + 1) p := by
  dsimp [next, hasLe]
  constructor <;> intro h k hk
  · specialize h (k - 1) # Nat.sub_le_of_le_add hk
    iterate 2 cases k; simp at h; simp [h]; nm k
    simp at h; simp [h]
  · have h₁ := h k (by linarith)
    have h₂ := h (k + 1) (by simpa)
    cases k <;> simp_all