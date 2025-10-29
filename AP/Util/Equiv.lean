import AP.Util.List

namespace Equiv

variable {α β : Type*}
variable {e : α ≃ β}

theorem option_eq_iff_map {x y : Option α} :
x = y ↔ x.map e = y.map e := by cases x <;> cases y <;> simp