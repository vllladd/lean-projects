import AP.Util.Basic

structure Deserializer where
  bytes : ByteArray
  bitIndex : ℕ

namespace Deserializer

variable (d : Deserializer)

def init (bytes : ByteArray) : Deserializer where
  bytes := bytes
  bitIndex := 0

-- def readBit : Bit × Deserializer where
--   fst := d.bytes.get! d.bitIndex