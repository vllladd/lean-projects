import Projects.Util

section logic

variable {α β γ : Type*}

-- #check 0 #exit

end logic

namespace Nat

-- #check 0 #exit

end Nat

namespace Int

attribute [simp] not_ofNat_neg

-- #check 0 #exit

end Int

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

-- #check 0 #exit

end List

namespace Set

variable {α β γ : Type*}
variable {s s₁ s₂ : Set α}

-- #check 0 #exit

end Set

namespace Std.DHashMap

open Std

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp mp₁ mp₂ : DHashMap α β}

-- #check 0 #exit

end Std.DHashMap

namespace Std.ExtDHashMap

open Std

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp mp₁ mp₂ : ExtDHashMap α β}
variable [ha : LinearOrder α]
omit ha

-- #check 0 #exit

end Std.ExtDHashMap

namespace Map

open Std

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Map α β}
variable [ha : LinearOrder α]
omit ha

-- #check 0 #exit

end Map

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}
variable [ha : LinearOrder α]
omit ha

-- #check 0 #exit

end Set'