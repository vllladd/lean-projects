import Projects.Util

namespace KolakoskiSequence

variable {α : Type*}

noncomputable
def setToSeq (s : Set ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon fun k => k ∈ s ∧ (s.filter (· < k)).ncard = n

noncomputable
def runs (a : ℕ → α) : ℕ → ℕ :=
  setToSeq {n | n = 0 ∨ a (n - 1) ≠ a n}

def lengths (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (n + 1) - a n

-- The Kolakoski sequence is a sequence of 1's and 2's
-- such that if you take the lengths of each run of the sequence
-- the result is the same as the original sequence
def IsKolakoski (K : ℕ → ℕ) : Prop :=
  Set.range K = {1, 2} ∧ lengths (runs K) = K

noncomputable
def kolakoski : ℕ → ℕ :=
  Classical.epsilon fun K => IsKolakoski K ∧ K 0 = 1