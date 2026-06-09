import Projects.Digits

namespace DigitalRoot

noncomputable
def digRoot (b n : ℕ) : ℕ :=
  Nat.digSum b |>.fix n

def digRootAlt₁' (b n g : ℕ) : ℕ :=
  match g with
  | 0 => n
  | g + 1 => if n < b then n else digRootAlt₁' b (Nat.digSum b n) g

def digRootAlt₁ (b n : ℕ) : ℕ :=
  digRootAlt₁' b n n

open Classical in noncomputable
def digRootAlt₂ (b n : ℕ) : ℕ :=
  if ¬b.Base then 0 else
  if n < b then n else
  digRootAlt₂ b # Nat.digSum b n
decreasing_by
  nm hb h; push Not at hb h; rwa [Nat.digSum_lt_iff_base_le]

def digRootAlt₃ (b n : ℕ) : ℕ :=
  if b ≤ 1 ∨ n = 0 then 0
  else if n % (b - 1) = 0 then b - 1
  else n % (b - 1)