import AP.System.Reachability

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem invariant {p : S → Prop} {a b}
(h₁ : p a) (h₂ : sys.Reachable a b)
(h₃ : ∀ {x y t}, p x → sys.tr x t = some y → p y) : p b := by
  induction h₂; exact h₁
  clear a b
  nm a b c t h₂ h₄ ih
  apply ih
  exact h₃ h₁ h₂

theorem invariant_init {p : S → Prop} {a}
(h₁ : sys.WF a) (h₂ : ∀ {a}, sys.Initial a → p a)
(h₃ : ∀ {x y t}, p x → sys.tr x t = some y → p y) : p a := by
  rw [wf_iff] at h₁
  obtain ⟨s₀, h₁, h₄⟩ := h₁
  exact invariant (h₂ h₁) h₄ h₃

theorem invariant_val {α : Type*} {a b} {f : S → α} (h₁ : sys.Reachable a b)
(h₂ : ∀ {x y t}, sys.tr x t = some y → f y = f x) : f b = f a := by
  apply invariant (p := (f · = f a)) rfl h₁
  intro x y t h₃ h₄
  rw [←h₃]
  exact h₂ h₄