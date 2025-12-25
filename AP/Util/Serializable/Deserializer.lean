import AP.Util.Basic
import AP.Util.Serializable.Serializer

structure Deserializer where
  bytes : ByteArray
  bitIndex : ℕ

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

@[simp]
theorem queryAllBits_init_bytes_ofBits {bs} : queryAllBits.run (init (ofBits bs).bytes) =
(bs ++ .replicate (bs.length % 8) 0, init (ofBits bs).bytes) := by
  unfold ofBits
  induction bs
  ·
    simp
  nm b bs ih
  sorry