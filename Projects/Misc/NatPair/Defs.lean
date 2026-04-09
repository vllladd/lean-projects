import Projects.Util

namespace NatPair

def pair (n m : ℕ) : ℕ :=
  2 ^ n * (m * 2 + 1) - 1

def fst (r : ℕ) : ℕ :=
  if h : Even r then 0 else 1 + fst (r / 2)
decreasing_by cases r; simp at h; omega

def snd (r : ℕ) : ℕ :=
  ((r + 1) / 2 ^ fst r - 1) / 2

def f (p : ℕ × ℕ) : ℕ :=
  pair p.1 p.2

def g (r : ℕ) : ℕ × ℕ :=
  (fst r, snd r)