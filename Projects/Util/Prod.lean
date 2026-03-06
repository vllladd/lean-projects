import Projects.Util.Logic

namespace Prod

variable {α β : Type*}
variable {a b c : α × β}
variable {x x₁ x₂ x₃ : α}
variable {y y₁ y₂ y₃ : β}

theorem fst_eq_of_eq_mk (h : a = (x, y)) : x = a.1 :=
  congrArg (·.1) h |>.symm

theorem snd_eq_of_eq_mk (h : a = (x, y)) : y = a.2 :=
  congrArg (·.2) h |>.symm