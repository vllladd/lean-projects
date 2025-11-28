import AP.Util.Basic

namespace Bit

@[simp]
def ofBool (b : Bool) : Bit :=
  match b with
  | true => 1
  | false => 0

instance : Coe Bool Bit := ⟨ofBool⟩

-- #check 0 #exit

end Bit

structure Deserializer where
  bytes : ByteArray
  bitIndex : ℕ

namespace Deserializer

variable (d : Deserializer)

def init (bytes : ByteArray) : Deserializer where
  bytes := bytes
  bitIndex := 0

def byteIndex : ℕ :=
  d.bitIndex >>> 3

def inByteBitIndex : UInt8 :=
  d.bitIndex &&& 7 |>.toUInt8

def curByte : UInt8 :=
  d.bytes.getD 0 d.byteIndex

def next' : Deserializer where
  bytes := d.bytes
  bitIndex := d.bitIndex + 1

def eof : Bool :=
  d.bytes.size ≤ d.bitIndex

def toEof : Deserializer where
  bytes := d.bytes
  bitIndex := d.bytes.size

def next : Deserializer :=
  if d.eof then d else d.next'

def readBit' : Bit :=
  (d.curByte >>> d.inByteBitIndex) &&& 1 != 0

def readBit : Bit × Deserializer where
  fst := d.readBit'
  snd := d.next

def drop (n : ℕ) : Deserializer where
  bytes := d.bytes
  bitIndex := min d.bytes.size # d.bitIndex + n

def getBits' (d : Deserializer) (n : ℕ) : List Bit :=
  match n with
  | 0 => []
  | n + 1 =>
    let (b, d') := d.readBit
    b :: d'.getBits' n

def getBits : List Bit :=
  d.getBits' # d.bytes.size - d.bitIndex