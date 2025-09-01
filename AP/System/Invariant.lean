import AP.System.Reachability

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem invariant {p : S → Prop} {a b} [ha : sys.WF a]
(h₁ : p a) (h₂ : sys.Reachable a b)
(h₃ : ∀ {x y t} [sys.WF x] [sys.WF y], p x → sys.tr x t = some y → p y) : p b := by
  revert ha; induction h₂; exact h₁
  clear! a b
  nm a b c t h₂ h₄ ih
  intro ha
  have hb := wf_of_tr h₂
  apply ih
  exact h₃ h₁ h₂

theorem invariant_wf {p : S → Prop} {a}
(h₁ : sys.WF a) (h₂ : ∀ {a}, sys.Initial a → p a)
(h₃ : ∀ {x y t} [sys.WF x] [sys.WF y], p x → sys.tr x t = some y → p y) : p a := by
  rw [wf_def] at h₁
  obtain ⟨s₀, h₁, h₄⟩ := h₁
  exact invariant (h₂ h₁) h₄ h₃

theorem invariant_val {α : Type*} {a b} [ha : sys.WF a] {f : S → α} (h₁ : sys.Reachable a b)
(h₂ : ∀ {x y t} [sys.WF x] [sys.WF y], sys.tr x t = some y → f y = f x) : f b = f a := by
  apply invariant (p := (f · = f a)) rfl h₁
  intro x y t ha hb h₃ h₄
  rw [←h₃]
  exact h₂ h₄