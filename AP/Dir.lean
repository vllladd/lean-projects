import AP.Point

inductive Dir where
| up : Dir
| left : Dir
| right : Dir
| down : Dir
deriving Inhabited, DecidableEq, Fintype

namespace Dir

open Dir

def point : Dir → PointZ
| up => ⟨0, -1⟩
| down => ⟨0, 1⟩
| left => ⟨-1, 0⟩
| right => ⟨1, 0⟩

@[simp] theorem point_up : up.point = ⟨0, -1⟩ := rfl
@[simp] theorem point_down : down.point = ⟨0, 1⟩ := rfl
@[simp] theorem point_left : left.point = ⟨-1, 0⟩ := rfl
@[simp] theorem point_right : right.point = ⟨1, 0⟩ := rfl

@[simp]
theorem point_ne_zero {t : Dir} : t.point ≠ 0 := by
  cases t <;> decide

def hor : Dir → Prop
| left => True
| right => True
| _ => False

def vert : Dir → Prop
| up => True
| down => True
| _ => False

@[simp] theorem not_hor_up : ¬up.hor := λ h => h
@[simp] theorem not_hor_down : ¬down.hor := λ h => h
@[simp] theorem hor_left : left.hor := trivial
@[simp] theorem hor_right : right.hor := trivial

@[simp] theorem vert_up : up.vert := trivial
@[simp] theorem vert_down : down.vert := trivial
@[simp] theorem not_vert_left : ¬left.vert := λ h => h
@[simp] theorem not_vert_right : ¬right.vert := λ h => h

@[simp] theorem not_hor {d : Dir} : ¬d.hor ↔ d.vert := by cases d <;> simp
@[simp] theorem not_vert {d : Dir} : ¬d.vert ↔ d.hor := by cases d <;> simp

instance {d : Dir} : Decidable d.hor :=
  match d with
  | up => .isFalse # λ h => h
  | down => .isFalse # λ h => h
  | left => .isTrue trivial
  | right => .isTrue trivial

instance {d : Dir} : Decidable d.vert :=
  match d with
  | up => .isTrue trivial
  | down => .isTrue trivial
  | left => .isFalse # λ h => h
  | right => .isFalse # λ h => h