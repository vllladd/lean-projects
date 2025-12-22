import AP.Util

section logic

-- #check 0 #exit

end logic

namespace Set

variable {α β γ : Type*}
variable {s s₁ s₂ : Set α}

-- #check 0 #exit

end Set

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}

-- #check 0 #exit

end Set'