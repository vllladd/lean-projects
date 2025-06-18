import AP.System.Defs

namespace System

@[refl]
theorem Reachable.refl' {S T} {sys : System S T} {a} : sys.Reachable a a :=
  Reachable.refl

@[trans]
theorem Reachable.trans {S T} {sys : System S T} {a b c}
(h₁ : sys.Reachable a b) (h₂ : sys.Reachable b c) : sys.Reachable a c := by
  induction h₂; exact h₁
  nm x y t h₂ h₃ ih
  exact Reachable.step h₂ ih