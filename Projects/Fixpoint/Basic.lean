import Projects.Fixpoint.Defs

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*} {f : α → α} {x y z : α}
variable [ha : CompleteLattice α]

@[scoped grind →]
theorem fixpoint_of_preFixpoint_and_postFixpoint
(h₁ : PreFixpoint f x) (h₂ : PostFixpoint f x) : Fixpoint f x := by
  grind

@[scoped grind →]
theorem preFixpoint_of_fixpoint (h : Fixpoint f x) : PreFixpoint f x := by
  grind

@[scoped grind →]
theorem postFixpoint_of_fixpoint (h : Fixpoint f x) : PostFixpoint f x := by
  grind

@[scoped grind =]
theorem fixpoint_iff_preFixpoint_and_postFixpoint :
Fixpoint f x ↔ PreFixpoint f x ∧ PostFixpoint f x := by
  grind