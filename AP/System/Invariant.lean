import AP.System.Reachability

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem invariant {p : S → Prop} {a b}
(h₁ : p a) (h₂ : sys.Reachable a b)
(h₃ : ∀ {x t y}, p x → sys.trTo x t y → p y) : p b := by
  induction h₂; exact h₁
  clear a b
  nm a b c t h₂ h₄ ih
  apply ih
  exact h₃ h₁ h₂

theorem invariant_init {p : S → Prop} {a}
(h₁ : sys.Valid a) (h₂ : ∀ {a}, sys.Initial a → p a)
(h₃ : ∀ {x y t}, p x → sys.trTo x t y → p y) : p a := by
  rw [valid_iff] at h₁
  obtain ⟨s₀, h₁, h₄⟩ := h₁
  exact invariant (h₂ h₁) h₄ h₃