import Projects.Util.List

namespace Equiv

variable {α β : Type*}
variable {e : α ≃ β}

theorem option_eq_iff_map {x y : Option α} :
x = y ↔ x.map e = y.map e := by cases x <;> cases y <;> simp

@[simp]
theorem symm_one : (1 : Equiv α α).symm = 1 := rfl