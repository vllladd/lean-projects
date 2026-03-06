import Projects.Point

inductive Dir where
| up : Dir
| left : Dir
| right : Dir
| down : Dir
deriving Inhabited, DecidableEq, Fintype

namespace Dir

variable {d : Dir}

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
theorem point_ne_zero : d.point ≠ 0 := by
  cases d <;> decide

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

@[simp] theorem not_hor : ¬d.hor ↔ d.vert := by cases d <;> simp
@[simp] theorem not_vert : ¬d.vert ↔ d.hor := by cases d <;> simp

instance : Decidable d.hor :=
  match d with
  | up => .isFalse # λ h => h
  | down => .isFalse # λ h => h
  | left => .isTrue trivial
  | right => .isTrue trivial

instance : Decidable d.vert :=
  match d with
  | up => .isTrue trivial
  | down => .isTrue trivial
  | left => .isFalse # λ h => h
  | right => .isFalse # λ h => h

def rotRight : Dir → Dir
| up => right
| right => down
| down => left
| left => up

def rotLeft : Dir → Dir
| up => left
| right => up
| down => right
| left => down

def inv : Dir → Dir
| up => down
| right => left
| down => up
| left => right

instance : Inv Dir := ⟨inv⟩
theorem inv_def : d⁻¹ = d.inv := rfl

@[simp] theorem rotRight_up : rotRight up = right := rfl
@[simp] theorem rotRight_right : rotRight right = down := rfl
@[simp] theorem rotRight_down : rotRight down = left := rfl
@[simp] theorem rotRight_left : rotRight left = up := rfl

@[simp] theorem rotLeft_up : rotLeft up = left := rfl
@[simp] theorem rotLeft_right : rotLeft right = up := rfl
@[simp] theorem rotLeft_down : rotLeft down = right := rfl
@[simp] theorem rotLeft_left : rotLeft left = down := rfl

@[simp] theorem inv_up : up⁻¹ = down := rfl
@[simp] theorem inv_right : right⁻¹ = left := rfl
@[simp] theorem inv_down : down⁻¹ = up := rfl
@[simp] theorem inv_left : left⁻¹ = right := rfl

@[simp] theorem rotRight_rotRight : d.rotRight.rotRight = d⁻¹ := by cases d <;> rfl
@[simp] theorem rotLeft_rotLeft : d.rotLeft.rotLeft = d.inv := by cases d <;> rfl
@[simp] theorem rotLeft_rotRight : d.rotLeft.rotRight = d := by cases d <;> rfl
@[simp] theorem rotRight_rotLeft : d.rotRight.rotLeft = d := by cases d <;> rfl
@[simp] theorem rotLeft_inv : d.rotLeft⁻¹ = d.rotRight := by cases d <;> rfl
@[simp] theorem rotRIght_inv : d.rotRight⁻¹ = d.rotLeft := by cases d <;> rfl
@[simp] theorem inv_rotLeft : d⁻¹.rotLeft = d.rotRight := by cases d <;> rfl
@[simp] theorem inv_rotRIght : d⁻¹.rotRight = d.rotLeft := by cases d <;> rfl
@[simp] theorem inv_inv : d⁻¹⁻¹ = d := by cases d <;> rfl

theorem hor_iff : d.hor ↔ d = left ∨ d = right := by cases d <;> simp
theorem vert_iff : d.vert ↔ d = up ∨ d = down := by cases d <;> simp

end Dir

namespace Point

variable {α : Type*} {p : Point α} [ha : Neg α]
omit ha

def coord' (p : Point α) (d : Dir) : α :=
  match d with
  | .up => p.y
  | .down => p.y
  | .left => p.x
  | .right => p.x

def coord (p : Point α) (d : Dir) : α :=
  match d with
  | .up => -p.y
  | .down => p.y
  | .left => -p.x
  | .right => p.x

@[simp] theorem coord'_up : p.coord' .up = p.y := rfl
@[simp] theorem coord'_down : p.coord' .down = p.y := rfl
@[simp] theorem coord'_left : p.coord' .left = p.x := rfl
@[simp] theorem coord'_right : p.coord' .right = p.x := rfl

include ha

@[simp] theorem coord_up : p.coord .up = -p.y := rfl
@[simp] theorem coord_down : p.coord .down = p.y := rfl
@[simp] theorem coord_left : p.coord .left = -p.x := rfl
@[simp] theorem coord_right : p.coord .right = p.x := rfl

end Point

namespace Dir

@[simp] theorem hor_rotRight {d : Dir} : d.rotRight.hor = d.vert := by cases d <;> rfl
@[simp] theorem vert_rotRight {d : Dir} : d.rotRight.vert = d.hor := by cases d <;> rfl
@[simp] theorem hor_rotLeft {d : Dir} : d.rotLeft.hor = d.vert := by cases d <;> rfl
@[simp] theorem vert_rotLeft {d : Dir} : d.rotLeft.vert = d.hor := by cases d <;> rfl
@[simp] theorem hor_inv {d : Dir} : d⁻¹.hor = d.hor := by cases d <;> rfl
@[simp] theorem vert_inv {d : Dir} : d⁻¹.vert = d.vert := by cases d <;> rfl

def univList : List Dir :=
  [.up, .left, .right, .down]

@[simp]
theorem nodup_univList : univList.Nodup := by
  decide

@[simp]
theorem mem_univList {d} : d ∈ univList := by
  cases d <;> decide