import AP.Paramodulator.Defs

namespace Paramodulator

open Node

theorem zero_def : (0 : Node) = nil := rfl
theorem one_def : (1 : Node) = pair 0 0 := rfl

@[simp] theorem sizeOf_zero : sizeOf (0 : Node) = 1 := rfl
@[simp] theorem sizeOf_one : sizeOf (1 : Node) = 3 := rfl