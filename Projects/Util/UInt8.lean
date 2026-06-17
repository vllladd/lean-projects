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