import Projects.Util.Basic
import Projects.Util.Serializable.Serializer

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

-- #check 0 #exit

end List

namespace Bit

variable {b b₁ b₂ b₃ : Bit}
variable {bs : List Bit}

namespace BitVec

variable {w : ℕ}
variable {x y z : BitVec w}

@[simp]
theorem ofNatLT_eq_ofNatLT_iff {n m hn hm} :
(.ofNatLT n hn : BitVec w) = .ofNatLT m hm ↔ n = m := by
  simp [BitVec.ofNatLT]

-- #check 0 #exit

end BitVec

end Bit

namespace UInt8

@[simp]
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

theorem forall_iff {p : UInt8 → Prop} [hp : DecidablePred p] :
(∀ x, p x) ↔ (List.range 256 |>.all (p # ofNat ·)) := by
  constructor
  · intro h
    simp [h]
  intro h x
  simp at h
  specialize h x.toNat # by simp
  simp at h
  exact h

instance {p : UInt8 → Prop} [hp : DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff' _ forall_iff

@[simp]
theorem mk_eq_mk_iff {x y : BitVec 8} : (⟨x⟩ : UInt8) = ⟨y⟩ ↔ x = y := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; rfl

@[simp]
theorem ofNatLT_eq_ofNatLT_iff {n m hn hm} : ofNatLT n hn = ofNatLT m hm ↔ n = m := by
  simp_rw [ofNatLT, mk_eq_mk_iff]
  simp

@[simp]
theorem ofBits_toBits : ofBits x.toBits = x := by
  native_decide +revert

-- #check 0 #exit

@[simp]
theorem length_toBits : x.toBits.length = 8 := by
  simp [toBits]

@[simp]
theorem toBits_eq_iff : x.toBits = y.toBits ↔ x = y := by
  native_decide +revert

@[simp]
theorem list_subset_zero_one {bs : List Bit} : bs ⊆ [0, 1] := by
  intro; simp

theorem forall_list_of_length_eq_iff {p : List Bit → Prop} [hp : DecidablePred p] {n} :
(∀ (bs : List Bit), bs.length = n → p bs) ↔ ([0, 1].combinations n).all (p ·) := by
  simp

theorem forall_list_of_length_le_iff {p : List Bit → Prop} [hp : DecidablePred p] {n} :
(∀ (bs : List Bit), bs.length ≤ n → p bs) ↔ ∀ (k : Fin (n + 1)),
([0, 1].combinations k).all (p ·) := by
  simp
  constructor
  · intro h ⟨k, hk⟩ bs h₁
    simp at h₁
    apply h
    omega
  · intro h bs h₁
    exact h ⟨bs.length, by omega⟩ bs rfl

theorem forall_list_of_length_lt_iff {p : List Bit → Prop} [hp : DecidablePred p] {n} :
(∀ (bs : List Bit), bs.length < n → p bs) ↔ ∀ (k : Fin n),
([0, 1].combinations k).all (p ·) := by
  simp
  constructor
  · intro h ⟨k, hk⟩ bs h₁
    simp at h₁
    apply h
    omega
  · intro h bs h₁
    exact h ⟨bs.length, by omega⟩ bs rfl

instance {p : List Bit → Prop} [hp : DecidablePred p] {n} :
Decidable # ∀ (bs : List Bit), bs.length = n → p bs :=
  decidable_of_iff' _ forall_list_of_length_eq_iff

instance {p : List Bit → Prop} [hp : DecidablePred p] {n} :
Decidable # ∀ (bs : List Bit), bs.length ≤ n → p bs :=
  decidable_of_iff' _ forall_list_of_length_le_iff

instance {p : List Bit → Prop} [hp : DecidablePred p] {n} :
Decidable # ∀ (bs : List Bit), bs.length < n → p bs :=
  decidable_of_iff' _ forall_list_of_length_lt_iff

theorem toBits_ofBits_of_length_eq_8 (h : bs.length = 8) : (ofBits bs).toBits = bs := by
  native_decide +revert

theorem toBits_ofBits_of_length_le_8 (h : bs.length ≤ 8) :
(ofBits bs).toBits = bs ++ List.replicate (8 - bs.length) 0 := by
  native_decide +revert

@[simp]
theorem toBits_ne_nil : x.toBits ≠ [] := by
  apply ne_of_congr (·.length); simp

-- #check 0 #exit

end UInt8

namespace ByteArray

def ofBits' (acc : List UInt8) (bs : List Bit) : List UInt8 :=
  if bs = [] then acc else
  match _h : bs.splitAt 8 with
  | (xs, bs') => ofBits' (.ofBits xs :: acc) bs'
termination_by bs.length
decreasing_by have : bs.length ≠ 0; simpa; grind

def ofBits (bs : List Bit) : ByteArray :=
  ⟨⟨ofBits' [] bs |>.reverse⟩⟩

def toBits (bs : ByteArray) : List Bit :=
  bs.1.1.flatMap UInt8.toBits

-----

theorem empty_def : (∅ : ByteArray) = ⟨⟨[]⟩⟩ := rfl

@[simp]
theorem ofBits_nil : ofBits [] = ∅ := by
  ext <;> simp [ofBits, ofBits']

@[simp]
theorem ofBits'_nil {acc} : ofBits' acc [] = acc := by
  simp [ofBits']

@[simp]
theorem ofBits_toBits {bs : ByteArray} : ofBits bs.toBits = bs := by
  rcases bs with ⟨⟨bs⟩⟩
  simp [ofBits, toBits]
  suffices h : ∀ acc, ofBits' acc (bs.flatMap UInt8.toBits) = bs.reverse ++ acc
  · specialize h []
    simp at h
    simp [h]
  intro acc
  induction bs generalizing acc
  · simp
  nm x bs ih
  simp
  unfold ofBits'
  simp [ih]

-- #check 0 #exit

end ByteArray

structure Deserializer where
  bytes : ByteArray
  bitIndex : ℕ
deriving DecidableEq

abbrev DSer := StateM Deserializer

namespace Deserializer

open Serializer

def init (bytes : ByteArray) : Deserializer where
  bytes := bytes
  bitIndex := 0

def byteIndex : DSer ℕ :=
  gets (·.bitIndex >>> 3)

def inByteBitIndex : DSer UInt8 :=
  gets (·.bitIndex &&& 7 |>.toUInt8)

def curByte : DSer UInt8 := do
  pure # (←get).bytes.getD 0 (←byteIndex)

def next' : DSer Unit := modify # λ d =>
  { bytes := d.bytes
    bitIndex := d.bitIndex + 1
  }

def eof : DSer Bool :=
  gets # λ d => d.bytes.size ≤ d.bitIndex

def toEof : DSer Unit := modify # λ d =>
  { bytes := d.bytes
    bitIndex := d.bytes.size
  }

def next : DSer Unit := do
  if ←eof then pure () else next'

def readBit' : DSer Bit := do
  pure # ((←curByte) >>> (←inByteBitIndex)) &&& 1 != 0

def readBit : DSer Bit := do
  let b ← readBit'
  next; pure b

def drop (n : ℕ) : DSer Unit := modify # λ d =>
  { bytes := d.bytes
    bitIndex := min d.bytes.size # d.bitIndex + n
  }

def queryAllBits' (d : Deserializer) (n : ℕ) : List Bit :=
  match n with
  | 0 => []
  | n + 1 =>
    let (b, d') := d.readBit
    b :: d'.queryAllBits' n

def queryAllBits : DSer # List Bit :=
  gets # λ d => queryAllBits' d # d.bytes.size - d.bitIndex

def skipBits (n : ℕ) : DSer Unit := modify # λ d =>
  { bytes := d.bytes
    bitIndex := d.bitIndex + n
  }

-----

variable {α β γ : Type}
variable {d : Deserializer}

@[simp]
theorem skipBits_zero : skipBits 0 = pure () := rfl

@[simp]
theorem const_fmap_queryAllBits {x : α} : (λ _ => x) <$> queryAllBits = pure x := rfl

@[simp]
theorem run_queryAllBits_init_empty : queryAllBits.run (init ∅) = ([], init ∅) := rfl

-- @[simp]
-- theorem queryAllBits_init_bytes_ofBits {bs} : queryAllBits.run (init # .ofBits bs) =
-- (bs ++ .replicate (bs.length % 8) 0, init (ofBits bs).bytes) := by
--   generalize hn : bs.length = n
--   induction n using Nat.strong_induction_on generalizing bs
--   nm n ih
--   by_cases h₁ : n < 8
--   ·
--     clear ih
--     subst hn
--     have : bs = [0]; sorry
--     subst this
--     clear h₁
--     reduce
--     simp