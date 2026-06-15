import Projects.Util.Monad

namespace Sum

variable {α β γ : Type}

@[simp]
theorem pure_eq {x : β} : (pure x : α ⊕ β) = .inr x := rfl