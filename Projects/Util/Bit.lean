import Projects.Util.Nat

inductive Bit where
| B₀ : Bit
| B₁ : Bit

namespace Bit

@[simp] instance : OfNat Bit 0 := ⟨B₀⟩
@[simp] instance : OfNat Bit 1 := ⟨B₁⟩

@[simp] theorem B₀_eq : B₀ = 0 := rfl
@[simp] theorem B₁_eq : B₁ = 1 := rfl

theorem bit_ind (R : Bit → Prop) (B0 : R 0) (B1 : R 1) b : R b := by
  cases b <;> assumption

instance : {a b : Bit} → Decidable (a = b)
| 0, 0 => Decidable.isTrue (by rfl)
| 0, 1 => Decidable.isFalse (by simp)
| 1, 0 => Decidable.isFalse (by simp)
| 1, 1 => Decidable.isTrue (by rfl)

@[simp]
def not : Bit → Bit
| 0 => 1
| 1 => 0

@[simp]
def imp : Bit → Bit → Bit
| 0, _ => 1
| 1, a => a

@[simp]
def or : Bit → Bit → Bit
| 0, a => a
| 1, _ => 1

@[simp]
def and : Bit → Bit → Bit
| 0, _ => 0
| 1, a => a

@[simp]
def iff : Bit → Bit → Bit
| 0, a => a.not
| 1, a => a

@[simp]
def xor : Bit → Bit → Bit
| 0, a => a
| 1, a => a.not

@[simp]
def ofBool (b : Bool) : Bit :=
  match b with
  | true => 1
  | false => 0

instance : Coe Bool Bit := ⟨ofBool⟩

-----

variable {b b₁ b₂ b₃ : Bit}

@[simp]
theorem eq_zero_or_eq_one : b = 0 ∨ b = 1 := by
  cases b <;> simp

@[simp]
theorem eq_one_or_eq_zero : b = 1 ∨ b = 0 := by
  cases b <;> simp

instance : Inhabited Bit where
  default := 0

instance : Fintype Bit where
  elems := {0, 1}
  complete := by simp

@[simp]
theorem default_def : (default : Bit) = 0 := rfl