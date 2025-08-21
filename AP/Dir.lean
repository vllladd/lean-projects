import AP.Point

inductive Dir where
| up : Dir
| left : Dir
| right : Dir
| down : Dir
deriving Inhabited, DecidableEq, Fintype

namespace Dir

def point : Dir → PointZ
| .up => ⟨0, -1⟩
| .down => ⟨0, 1⟩
| .left => ⟨-1, 0⟩
| .right => ⟨1, 0⟩

@[simp] theorem point_up : Dir.up.point = ⟨0, -1⟩ := rfl
@[simp] theorem point_down : Dir.down.point = ⟨0, 1⟩ := rfl
@[simp] theorem point_left : Dir.left.point = ⟨-1, 0⟩ := rfl
@[simp] theorem point_right : Dir.right.point = ⟨1, 0⟩ := rfl

@[simp]
theorem point_ne_zero {t : Dir} : t.point ≠ 0 := by
  cases t <;> decide