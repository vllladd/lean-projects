import AP.Util

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}
variable [LE α]

@[scoped grind =]
def PreFixpoint (f : α → α) (x : α) : Prop :=
  f x ≤ x

@[scoped grind =]
def PostFixpoint (f : α → α) (x : α) : Prop :=
  x ≤ f x

@[scoped grind =]
def Fixpoint (f : α → α) (x : α) : Prop :=
  f x = x