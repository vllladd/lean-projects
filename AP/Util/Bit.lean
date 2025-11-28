import AP.Util.Nat

inductive Bit where
| B₀ : Bit
| B₁ : Bit

open Bit

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