import Projects.Util

namespace RealEquiv

@[ext]
structure Bits : Type where
  get : ℕ → Bit
deriving Inhabited

def Bits.map (bs : Bits) (f : Bit → Bit) : Bits where
  get i := f # bs.get i

def Bits.drop (bs : Bits) (n : ℕ) : Bits where
  get i := bs.get # n + i

def Bits.tail (bs : Bits) : Bits :=
  bs.drop 1

open Classical in noncomputable
def Bits.indexOf (bs : Bits) (b : Bit) : Option ℕ :=
  Nat.find! λ n => bs.get n = b

def Bits.take (bs : Bits) (n : ℕ) : List Bit :=
  List.range n |>.map bs.get

def Bits.invert (bs : Bits) : Bits :=
  bs.map .not

def Bits.cons (bs : Bits) (b : Bit) : Bits where
  get i := match i with
    | 0 => b
    | i + 1 => bs.get i

def Bits.prepend (bs : Bits) (bs₀ : List Bit) : Bits :=
  bs₀.foldr (λ b bs => bs.cons b) bs

open Classical in noncomputable
def Bits.getNat (bs : Bits) : ℕ × Bits :=
  let n := bs.indexOf 0 |>.getd
  (n, bs.drop # n + 1)

def Bits.inc (bs : Bits) : Bits :=
  bs.cons 1

open Classical in noncomputable
def Bits.end (bs : Bits) : Option Bit :=
  choose? λ b => eventually (bs.get · = b)

-- #check 0 #exit

-----

def bitsToRat (bs : List Bit) : ℚ :=
  Nat.ofBits (bs.reverse.map Bit.toBool).toVec / 2 ^ bs.length

open Classical in noncomputable
def ofBitsAux₁ (bs : Bits) : ℝ :=
  Real.mk! # bitsToRat ∘ bs.take

open Classical in noncomputable
def ofBitsAux₂ (neg : Bit) (bs : Bits) : ℝ :=
  let (n, bs) := bs.getNat
  neg.ite (-1) 1 * (n + ofBitsAux₁ bs)

open Classical in noncomputable
def ofBits (bs : Bits) : ℝ :=
  match bs.end with
  | none => ofBitsAux₂ (bs.get 0) bs.tail
  | some 0 => ofBitsAux₂ 0 bs
  | some 1 => ofBitsAux₂ 1 bs.invert.inc

open Classical in noncomputable
def toBitsAux₁ (r : ℝ) : Bits where
  get i := 1 < r * 2 ^ (i + 1)

open Classical in noncomputable
def toBits (r : ℝ) : Bits :=
  let neg : Bit := r < 0
  let r := |r|
  let n := ⌊r⌋.toNat
  let bs := toBitsAux₁ # r - n
  let bs := bs.cons 0 |>.prepend # .replicate n 1
  match bs.end with
    | none => bs.cons neg
    | some 0 => bs
    | some 1 => bs.invert.inc