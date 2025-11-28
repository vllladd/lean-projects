import AP.Util.Data

structure Serializer where
  bytes : ByteArray
  curByte : UInt8
  bitMask : UInt8

namespace Serializer

variable (s : Serializer)

def empty : Serializer where
  bytes := ∅
  curByte := 0
  bitMask := 1

instance : EmptyCollection Serializer := ⟨empty⟩
theorem empty_def : (∅ : Serializer) = empty := rfl

def flush' : Serializer :=
  { s with
    bytes := s.bytes.push s.curByte
    curByte := 0
    bitMask := 1
  }

def flush : Serializer :=
  bif s.bitMask != 0 then s else s.flush'

def writeBit' (b : Bit) : Serializer :=
  { s with
    curByte := match b with
      | .B₀ => s.curByte
      | .B₁ => s.curByte ||| s.bitMask
    bitMask := s.bitMask <<< 1
  }

def writeBit (b : Bit) : Serializer :=
  s.writeBit' b |>.flush

def getOutput : ByteArray :=
  s.flush.bytes