import Projects.Digits

namespace DigitalRoot

noncomputable
def digRoot (b n : ℕ) : ℕ :=
  Nat.digSum b |>.fix n

def digRootComp' (b n g : ℕ) : ℕ :=
  match g with
  | 0 => n
  | g + 1 => if n < b then n else digRootComp' b (Nat.digSum b n) g

def digRootComp (b n : ℕ) : ℕ :=
  digRootComp' b n n