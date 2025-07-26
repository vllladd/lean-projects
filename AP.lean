import AP.Util.Basic
import Mathlib.Tactic

@[ext]
structure S where
  x : ℤ
  y : ℤ
deriving Inhabited, DecidableEq, Repr

inductive Btn where
| A : Btn
| B : Btn
| C : Btn
deriving Inhabited, DecidableEq

open Btn

instance : Repr Btn := Repr.mk # λ b _ =>
  Std.Format.text # match b with
  | A => "A"
  | B => "B"
  | C => "C"

def S.btn (s : S) : Btn → S
| A => if s = ⟨1, 1⟩ then s else {s with x := s.x + 1}
| B => if s = ⟨1, 1⟩ then s else {s with y := s.y + 1}
| C => if s = ⟨1, 1⟩ ∨ s.x * s.y = 0 then s else
  ⟨s.x - 1, s.y - 1⟩

def S.run (s : S) (xs : List Btn) : S :=
  xs.foldl S.btn s

def S.find (s₁ s₂ : S) (n : ℕ) : Option (List Btn) :=
  List.head? # do
  let xs ← sequence # List.replicate n [A, B, C]
  guard # s₁.run xs = s₂
  return xs

def S.find! {s₁ s₂ : S} (h : ∃ n, (s₁.find s₂ n).isSome) : List Btn :=
  (s₁.find s₂ # Nat.find h).getD []

def s₁ : S := ⟨1, 0⟩
def s₂ : S := ⟨0, 1⟩

theorem exi_find_10_01 : ∃ n, (s₁.find s₂ n).isSome := by
  use 6; native_decide

def main : IO Unit := do
  IO.println # repr # S.find! exi_find_10_01