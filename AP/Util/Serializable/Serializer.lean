import AP.Util.Basic

structure Serializer where
  bytes : ByteArray
  curByte : UInt8
  bitMask : UInt8

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