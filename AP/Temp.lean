import AP.Util

section logic

variable {α β γ : Type*}

-- #check 0 #exit

end logic

namespace Nat

-- #check 0 #exit

end Nat

namespace Int

-- #check 0 #exit

end Int

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

theorem nodup_take {n} (h : xs.Nodup) : (xs.take n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp
  nm n
  simp
  split_ands
  · contrapose! h₁
    exact mem_of_mem_take h₁
  exact ih h₂

theorem nodup_drop {n} (h : xs.Nodup) : (xs.drop n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp [h₁, h₂]
  nm n
  simp
  exact ih h₂

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