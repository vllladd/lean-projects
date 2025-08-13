import AP.AP
import AP.Sokoban

namespace AP

def getPs (r : ℕ) : List PointZ := do
  let d : ℕ := r * 2 + 1
  let cs := (List.range d).map # λ i => (i : ℤ) - (r : ℤ)
  let y ← cs
  let x ← cs
  return ⟨x, y⟩

def aStrat : AStrat := .mk # λ s =>
  let ⟨x, y⟩ := s.a_pos
  ⟨1 - x, y⟩

def dStrat : DStrat := .mk # λ s =>
  let xs := do
    let p ← getPs 3
    guard # s.dMove p |>.isSome
    return p
  match xs with
  | [] => s.dChooseMove
  | (p :: _) => p

def strat : Strat := ⟨aStrat, dStrat⟩

def State.toStr (s : State) : String := String.mk # do
  let d := 5
  let p ← getPs 5
  let ⟨x, y⟩ := p
  let sp := do
    guard # x + d = 0 ∧ y + d ≠ 0
    return '\n'
  let c := if p = s.a_pos then '@'
    else if p ∈ s.taken then '#'
    else '.'
  sp ++ [c]

instance : ToString State := ⟨State.toStr⟩

def logb : IO Unit := do
  IO.println ""
  IO.println # String.mk # List.replicate 100 '='
  IO.println ""

def _root_.main : IO Unit := do
  let n := 100
  let (res, k) := sys.simulate strat.f (initState 1) n
  IO.println # toString n ++ " ---> " ++ toString k
  logb
  IO.println # res