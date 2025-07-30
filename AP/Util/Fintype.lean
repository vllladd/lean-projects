import AP.Util.Logic

noncomputable
def Finite.toFintype {α : Type*} (ha : Finite α) : Fintype α :=
  Fintype.ofFinite α

-----

namespace Fintype

theorem exi_iter_cycle {α : Type*} [ha : Fintype α]
{f : α → α} {x : α} : ∃ n m, n < m ∧ f^[n] x = f^[m] x := by
  obtain ⟨g, hg⟩ := hv # λ n => f^[n] x
  suffices h : ∃ n m, g n = g m ∧ n ≠ m by
    subst hg
    obtain ⟨n, m, h₁, h₂⟩ := h
    wlog h₃ : n < m with ih
    · symm at h₁ h₂
      apply @ih α _ f x m n h₁ h₂ _
      simp at h₃
      exact Nat.lt_of_le_of_ne h₃ h₂
    use n, m
  by_contra! h₁
  exact Fintype.false # Fintype.ofInjective g h₁

@[simp]
theorem complete' {α : Type*} [Fintype α] {x : α} : x ∈ Fintype.elems := by
  apply Fintype.complete x

instance {α : Type*} [h : IsEmpty α] : Fintype α := ⟨{}, by simp⟩

noncomputable
instance {α : Type*} [h : Fintype α] {β : Type*} {f : α → β} :
Fintype # Set.range f := by apply Fintype.ofFinite

@[simp]
theorem elems_eq_empty_iff {α : Type*} [ha : Fintype α] :
ha.elems = ∅ ↔ ∀ (_ : α), false := by simp [Finset.ext_iff]

noncomputable
instance {α : Type*} [Fintype α] {s : Set α} : Fintype s := by
  exact Fintype.ofFinite ↑s