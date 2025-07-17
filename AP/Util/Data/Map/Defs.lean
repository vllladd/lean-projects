import AP.Util.Basic

universe u v

namespace Util.Data

section type_defs

variable (α : Type u) [hh₁ : LinearOrder α] [hh₂ : Hashable α] (β : α → Type v)

instance DMap.equiv {α : Type u} {β : α → Type v}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] :
@Equivalence (Std.DHashMap α β) #
Std.DHashMap.Equiv (α := α) (β := β) := by
  constructor
  · intro x
    exact Std.DHashMap.Equiv.of_forall_get?_eq (congrFun rfl)
  · intro x y h
    exact h.symm
  intro x y z h₁ h₂
  exact (Std.DHashMap.Equiv.congr_right h₂).mp h₁

instance DMap.setoid : Setoid (Std.DHashMap α β) :=
  ⟨_, DMap.equiv (α := α) (β := β)⟩

def DMap : Type (max u v) :=
  Quotient # DMap.setoid α β

def Map (β : Type v) : Type (max u v) :=
  DMap α # λ _ => β

end type_defs

namespace DMap

variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type v}

def empty : DMap α β := ⟦∅⟧

instance : EmptyCollection (DMap α β) := ⟨empty⟩

theorem empty_def : (∅ : DMap α β) = ⟦(∅ : Std.DHashMap α β)⟧ := rfl

end DMap namespace Map

variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : Type v}

def empty : Map α β := DMap.empty

instance {β : Type v} : EmptyCollection (Map α β) := ⟨empty⟩

theorem empty_def : (∅ : Map α β) = (∅ : DMap α (λ _ => β)) := rfl