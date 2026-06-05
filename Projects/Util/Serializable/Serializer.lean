import Projects.Util.Basic

section Id

variable {α β γ : Type}

-- #check 0 #exit

end Id

namespace Nat

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

-- #check 0 #exit

end List

namespace Bit

-- #check 0 #exit

end Bit

namespace BitVec

variable {w : ℕ}
variable {x y z : BitVec w}

-- #check 0 #exit

end BitVec

namespace UInt8

-- #check 0 #exit

end UInt8

namespace ByteArray

attribute [-simp] List.getElem!_eq_getElem?_getD

-- #check 0 #exit

-- @[simp]
-- theorem toList_mk {bs} : (⟨bs⟩ : ByteArray).toList = bs.toList := by
--   rcases bs with ⟨bs⟩
--   simp [toList]
--   rw [show [] = (bs.take 0).reverse by simp]
--   nth_rw 3 [show bs = bs.drop 0 by simp]
--   generalize 0 = i
--   generalize hx : (⟨⟨bs⟩⟩ : ByteArray) = xs
--   
--   clear hx
--   
--   -- replace hx : xs.size = bs.length; simp [←hx]
--   induction bs generalizing xs i
--   ·
--     unfold toList.loop
--     simp
--   nm b bs ih

-- #check 0 #exit

-- theorem toList_eq_toList_data {bs : ByteArray} : bs.toList = bs.data.toList := by
--   cases bs; simp

-- theorem ofBits_of_le_length {bs : List Bit} (h : 8 ≤ bs.length) :
-- ofBits bs = ⟨⟨.ofBits (bs.take 8) :: (ofBits (bs.drop 8)).toList⟩⟩ := by
--   nth_rw 1 [ofBits]
--   rw [ofBits']
--   simp [show bs ≠ [] by grind]
--   rw [ofBits'_eq_append]
--   simp [ofBits]

-- #check 0 #exit

end ByteArray

structure Serializer where
  bytes : ByteArray
  curByte : UInt8
  bitMask : UInt8
deriving DecidableEq

namespace Serializer

abbrev Ser := StateM Serializer

def empty : Serializer where
  bytes := ∅
  curByte := 0
  bitMask := 1

instance : EmptyCollection Serializer := ⟨empty⟩
theorem empty_def : (∅ : Serializer) = empty := rfl

def flush' : Ser Unit := modify # λ s =>
  { bytes := s.bytes.push s.curByte
    curByte := 0
    bitMask := 1
  }

def flush : Ser Unit := do
  bif (←get).bitMask != 0 then pure () else flush'

def writeBit' (b : Bit) : Ser Unit := modify # λ s =>
  { bytes := s.bytes
    curByte := match b with
      | .B₀ => s.curByte
      | .B₁ => s.curByte ||| s.bitMask
    bitMask := s.bitMask <<< 1
  }

def writeBit (b : Bit) : Ser Unit := do
  writeBit' b; flush

def writeBits (bs : List Bit) : Ser Unit :=
  bs.forM writeBit

def getOutput : Ser ByteArray := do
  flush; gets (·.bytes)

def ofBits (bs : List Bit) : Serializer :=
  StateT.run (m := Id) (writeBits bs) ∅ |>.2

-- #check 0 #exit

-----

variable {α β γ : Type}
variable {s : Serializer}

@[simp]
theorem writeBits_nil : writeBits [] = pure () := rfl

@[simp]
theorem getOutput_empty : getOutput.run ∅ = (∅, ∅) := rfl

@[simp low]
theorem writeBits_empty {bs} : (writeBits bs).run ∅ = ((), ofBits bs) := rfl

@[simp]
theorem ofBits_nil : ofBits [] = ∅ := rfl

@[simp]
theorem flush_empty : flush.run ∅ = ((), ∅) := rfl

@[simp]
theorem writeBits_cons {b bs} : writeBits (b :: bs) = (do writeBit b; writeBits bs) := rfl

@[simp]
theorem writeBits_append {bs₁ bs₂} :
writeBits (bs₁ ++ bs₂) = (do writeBits bs₁; writeBits bs₂) := by
  simp [writeBits]

@[simp]
theorem flush_flush' : flush.run (flush'.run s).2 = flush'.run s := rfl

@[simp]
theorem flush_flush : flush.run (flush.run s).2 = flush.run s := by
  nth_rw 2 [flush]; simp
  split_ifs with h <;> simp
  simp [flush, h]

@[simp]
theorem flush_ofBits {bs} : flush.run (ofBits bs) = ((), ofBits bs) := by
  induction bs using List.reverseRecOn; simp
  unfold ofBits; simp [writeBit, writeBit']; rfl

@[simp]
theorem getOutput_ofBits {bs} : getOutput.run (ofBits bs) = (ofBits bs |>.bytes, ofBits bs) := by
  simp [getOutput]

@[simp]
theorem bytes_empty : (∅ : Serializer).bytes = ∅ := rfl

@[simp]
theorem ofBits_append {bs₁ bs₂} :
ofBits (bs₁ ++ bs₂) = (writeBits bs₂ |>.run (ofBits bs₁) |>.2) := by
  unfold ofBits; simp

-- @[simp]
-- theorem bytes_ofBits {bs : List Bit} : (ofBits bs).bytes = .ofBits bs := by
--   generalize hn : bs.length = n
--   induction n using Nat.strong_induction_on generalizing bs
--   nm n ih
--   subst hn
--   by_cases h : bs = []
--   ·
--     subst h
--     simp
--   by_cases h₁ : bs.length < 8
--   ·
--     rw [ByteArray.ofBits'_of_length_le]
--   sorry