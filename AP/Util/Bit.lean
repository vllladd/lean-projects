import AP.Util.Nat

inductive Bit where
| Bit0 : Bit
| Bit1 : Bit

open Bit

@[simp] instance : OfNat Bit 0 := ⟨Bit0⟩
@[simp] instance : OfNat Bit 1 := ⟨Bit1⟩

@[simp] theorem Bit0_eq : Bit0 = 0 := rfl
@[simp] theorem Bit1_eq : Bit1 = 1 := rfl

theorem bit_ind (R : Bit → Prop) (B0 : R 0) (B1 : R 1) b : R b := by
  cases b <;> assumption

instance : {a b : Bit} → Decidable (a = b)
| 0, 0 => Decidable.isTrue (by rfl)
| 0, 1 => Decidable.isFalse (by simp)
| 1, 0 => Decidable.isFalse (by simp)
| 1, 1 => Decidable.isTrue (by rfl)

instance : DecidableEq Bit := by
  intro a b; exact instDecidableEqBit

@[simp]
def Bit.not : Bit → Bit
| 0 => 1
| 1 => 0

@[simp]
def Bit.imp : Bit → Bit → Bit
| 0, _ => 1
| 1, a => a

@[simp]
def Bit.or : Bit → Bit → Bit
| 0, a => a
| 1, _ => 1

@[simp]
def Bit.and : Bit → Bit → Bit
| 0, _ => 0
| 1, a => a

@[simp]
def Bit.iff : Bit → Bit → Bit
| 0, a => a.not
| 1, a => a

@[simp]
def Bit.xor : Bit → Bit → Bit
| 0, a => a
| 1, a => a.not