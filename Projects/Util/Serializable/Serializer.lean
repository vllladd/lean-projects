import Projects.Util.Basic

section Id

variable {α β γ : Type}

-- #check 0 #exit

end Id

namespace Nat

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type}
variable {xs ys zs : List α}
variable {M : Type → Type} [H₁ : Monad M] [H₂ : LawfulMonad M]

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

def finish : Ser Unit := do
  bif (←get).bitMask == 1 then pure () else flush'

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
  finish; gets (·.bytes)

def ofBits (bs : List Bit) : Serializer :=
  StateT.run (m := Id) (writeBits bs) ∅ |>.2

-- #check 0 #exit

-----

variable {α β γ : Type}
variable {s : Serializer}

@[simp]
theorem writeBits_nil : writeBits [] = pure () := rfl

@[simp]
theorem finish_empty : finish.run ∅ = ((), ∅) := rfl

@[simp]
theorem getOutput_empty : getOutput.run ∅ = (∅, ∅) := rfl

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
theorem finish_finish {s} : finish.run (finish.run s).2 = finish.run s := by
  simp [finish]; split_ifs <;> simp_all [flush']

@[simp]
theorem flush_ofBits {bs} : flush.run (ofBits bs) = ((), ofBits bs) := by
  induction bs using List.reverseRecOn; simp
  unfold ofBits; simp [writeBit, writeBit']; rfl

@[simp]
theorem bytes_empty : (∅ : Serializer).bytes = ∅ := rfl

@[simp]
theorem ofBits_append {bs₁ bs₂} :
ofBits (bs₁ ++ bs₂) = (writeBits bs₂ |>.run (ofBits bs₁) |>.2) := by
  unfold ofBits; simp

@[simp]
theorem bitMask_empty : (∅ : Serializer).bitMask = 1 := rfl

-- #check 0 #exit

-- @[simp]
-- theorem fst_getOutput_ofBits {bs : List Bit} :
-- (getOutput.run (ofBits bs)).1 = .ofBits bs := by
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
--     clear ih
--     rw [ByteArray.ofBits_of_length_le h (by omega)]
--     
--     -- rw [ofBits, writeBits, List.forM_eq_sequence']
--     -- simp
--     -- cases bs
--     -- ·
--     --   simp at h
--     -- clear h
--     -- nm b₀ bs
--     -- simp at h₁
--     -- replace h₁ : bs.length ≤ 6; omega
--     -- 
--     -- induction bs
--     -- ·
--     --   -- simp [writeBit, writeBit', flush, getOutput, finish, flush']
--     --   -- split <;> rfl
--     --   cases b₀ <;> rfl
--     -- nm b₁ bs ih
--     -- specialize ih (by grind)
--     -- simp at h₁
--     -- replace h₁ : bs.length ≤ 5; omega
--     
--   sorry