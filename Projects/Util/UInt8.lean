import Projects.Util.BitVec

namespace UInt8

def ofBit (b : Bit) : UInt8 :=
  match b with
  | 0 => 0
  | 1 => 1

def lowestBit (x : UInt8) : Bit :=
  .ofBool # Odd x.toNat

def ofBits (bs : List Bit) : UInt8 :=
  bs.foldr (λ bit x => (x <<< 1) ||| ofBit bit) 0

def toBits (x : UInt8) : List Bit :=
  List.range 8 |>.map # λ n => (x >>> ofNat n).lowestBit

-----

variable {x y z : UInt8}
variable {bs : List Bit}

attribute [simp] UInt8.toNat_lt_size

@[simp]
theorem mk_eq_mk_iff {x y : BitVec 8} : (⟨x⟩ : UInt8) = ⟨y⟩ ↔ x = y := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; rfl

theorem eq_iff_mk : x = y ↔ x.toBitVec = y.toBitVec := by
  cases x; cases y; simp

@[simp]
theorem ofNatLT_eq_ofNatLT_iff {n m hn hm} : ofNatLT n hn = ofNatLT m hm ↔ n = m := by
  simp_rw [ofNatLT, mk_eq_mk_iff]; simp

attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp]
theorem ofBit_eq_mk {b} : ofBit b = ⟨.ofBit _ b⟩ := by
  cases b <;> rfl

@[simp]
theorem lowestBit_mk {x : BitVec 8} : lowestBit ⟨x⟩ = x.lowestBit := rfl

theorem or_eq_mk : x ||| y = ⟨x.toBitVec ||| y.toBitVec⟩ := rfl

@[simp]
theorem ofBits_eq_mk {bs : List Bit} : ofBits bs = ⟨.ofBits _ bs⟩ := by
  simp [eq_iff_mk, ofBits, BitVec.ofBits]
  rw [List.foldr_apply toBitVec ofBitVec]; simp
  rintro ⟨x⟩; simp

@[simp]
theorem toBitVec_eq_iff : x.toBitVec = y.toBitVec ↔ x = y := by
  cases x; cases y; simp

@[simp]
theorem toBits_eq_mk : x.toBits = x.toBitVec.toBits := rfl

@[simp]
theorem one_shl_one : (1 : UInt8) <<< (1 : UInt8) = 2 := rfl

instance : LinearOrder UInt8 where
  le_refl {x} := by simp
  le_trans {x y z} (h₁ h₂) := by trans y <;> assumption
  le_antisymm {x y} (h₁ h₂) := UInt8.le_antisymm h₁ h₂
  le_total {x y} := UInt8.le_total x y
  toDecidableLE {x y} := inferInstance
  lt_iff_le_not_ge {x y} := Std.LawfulOrderLT.lt_iff x y
  min_def {x y} := by rfl
  max_def {x y} := by rfl

@[simp]
theorem ofBits_snoc {bs : List Bit} {b : Bit} : ofBits (bs ++ [b]) =
ofBits bs ||| (if bs.length < 8 then ofBit b <<< UInt8.ofNat bs.length else 0) := by
  apply UInt8.eq_of_toBitVec_eq
  simp
  congr
  split_ifs with h
  · simp [Nat.mod_eq_of_lt h]
  simp
  apply BitVec.shiftLeft_eq_zero
  omega

@[simp]
theorem ofNat_eq_zero_iff {n : ℕ} : UInt8.ofNat n = 0 ↔ n % 256 = 0 := by
  simp [ofNat, UInt8.eq_iff_toBitVec_eq]

@[simp]
theorem ofNat_eq_one_iff {n : ℕ} : UInt8.ofNat n = 1 ↔ n % 256 = 1 := by
  simp [ofNat, UInt8.eq_iff_toBitVec_eq]

@[simp]
theorem one_shiftLeft_ne_zero {n : ℕ} : 1 <<< (UInt8.ofNat n) ≠ 0 := by
  simp [UInt8.ext_iff, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt]; simp
  change 2 ^ (n % 8) < 2 ^ 8
  rw [Nat.pow_lt_pow_iff_right (by simp)]
  apply Nat.mod_lt; simp

@[simp]
theorem one_shiftLeft_eq_one_iff {n : ℕ} : 1 <<< (UInt8.ofNat n) = 1 ↔ n % 8 = 0 := by
  simp [ofNat, UInt8.eq_iff_toBitVec_eq]