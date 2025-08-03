import AP.Util.Main
import Mathlib.Tactic

def mp₁ : Map ℕ String :=
  .ofList [(5, "x"), (7, "y")]

def mp₂ : Map ℕ String :=
  .ofList [(7, "y"), (5, "x")]

def main : IO Unit := do
  IO.println # mp₁.toList
  IO.println # mp₂.toList
  IO.println # decide # mp₁ = mp₂