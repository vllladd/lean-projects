import Projects.Util.Order

namespace Nat

class Base (b : ℕ) : Prop where
  h : 2 ≤ b

def Base.decide (b : ℕ) : Bool :=
  2 ≤ b

def toDigList' (b n : ℕ) : List ℕ :=
  if b ≤ 1 then [] else if n = 0 then []
  else (n % b) :: toDigList' b (n / b)
decreasing_by
  nm h₁ h₂; rw [Nat.div_lt_iff_lt_mul (by omega)]
  cases n; simp at h₂; simp; omega

def toDigList (b n : ℕ) : List ℕ :=
  if b ≤ 1 then [] else if n = 0 then [0] else (toDigList' b n).reverse

def ofDigList (b : ℕ) (ds : List ℕ) : ℕ :=
  ds.foldl (λ n d => n * b + d) 0

def digSum (b n : ℕ) : ℕ :=
  toDigList b n |>.sum

def digRev (b n : ℕ) : ℕ :=
  ofDigList b (toDigList b n).reverse

def digsNum (b n : ℕ) : ℕ :=
  toDigList b n |>.length