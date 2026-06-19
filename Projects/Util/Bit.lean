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

def ofBool (b : Bool) : Bit :=
  match b with
  | true => 1
  | false => 0

instance : Coe Bool Bit := ⟨ofBool⟩

instance [∀ p, Decidable p] : Coe Prop Bit := ⟨(ofBool ·)⟩

def ite {α : Type*} (b : Bit) (x y : α) : α :=
  match b with
  | B₁ => x
  | B₀ => y

def toBool (b : Bit) : Bool :=
  b.ite true false

instance : Coe Bit Bool := ⟨toBool⟩

def toNat (b : Bit) : ℕ :=
  match b with
  | 0 => 0
  | 1 => 1

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

@[simp] theorem not_0 : (0 : Bit).not = 1 := rfl
@[simp] theorem not_1 : (1 : Bit).not = 0 := rfl

@[simp]
theorem ne_iff_eq_not {a b : Bit} : a ≠ b ↔ a = b.not := by
  cases a <;> cases b <;> simp

@[simp]
theorem not_not {b : Bit} : b.not.not = b := by
  cases b <;> rfl

@[simp] theorem ofBool_false : ofBool false = 0 := rfl
@[simp] theorem ofBool_true : ofBool true = 1 := rfl
@[simp] theorem toBool_0 : toBool 0 = false := rfl
@[simp] theorem toBool_1 : toBool 1 = true := rfl

@[simp]
theorem ofBool_eq_zero_iff {b : Bool} : ofBool b = 0 ↔ b = false := by
  cases b <;> simp

@[simp]
theorem ofBool_eq_one_iff {b : Bool} : ofBool b = 1 ↔ b = true := by
  cases b <;> simp

@[simp]
theorem toBool_eq_false_iff {b : Bit} : b.toBool = false ↔ b = 0 := by
  cases b <;> simp

@[simp]
theorem toBool_eq_true_iff {b : Bit} : b.toBool = true ↔ b = 1 := by
  cases b <;> simp

@[simp]
theorem toBool_ofBool {b : Bool} : (ofBool b).toBool = b := by
  cases b <;> rfl

@[simp]
theorem ofBool_toBool {b : Bit} : ofBool b.toBool = b := by
  cases b <;> rfl

@[simp]
theorem ofBool_eq_iff {b₁ b₂} : ofBool b₁ = ofBool b₂ ↔ b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp

@[simp] theorem toNat_zero : toNat 0 = 0 := rfl
@[simp] theorem toNat_one : toNat 1 = 1 := rfl