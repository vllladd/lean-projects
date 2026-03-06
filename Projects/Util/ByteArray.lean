import Projects.Util.Bit
import Projects.Util.Array

namespace ByteArray

def getD (bs : ByteArray) (z : UInt8) (i : ℕ) : UInt8 :=
  if h : i < bs.size then bs[i] else z

-- #check 0 #exit

-----