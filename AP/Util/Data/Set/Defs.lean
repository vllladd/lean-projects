import AP.Util.Data.Map.Main

universe u

namespace Util.Data

section type_defs

variable (α : Type u) [hh₁ : LinearOrder α] [hh₂ : Hashable α]

def Set : Type u
  := Map α Unit

end type_defs

namespace Set

variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α]

def empty : Set α := (∅ : Map α _)

instance : EmptyCollection (Set α) := ⟨empty⟩

theorem empty_def : (∅ : Set α) = (∅ : Map α _) := rfl

end Set