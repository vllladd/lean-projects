import AP.AP
import AP.Misc
import AP.Sokoban

namespace AP

def getPs (d : ℕ) : List PointZ :=
  (⟨0, 0⟩ : PointZ).nbhd d

def aStrat : AStrat := .mk' # λ s =>
  let ⟨x, y⟩ := s.aPos
  ⟨1 - x, y⟩

def dStrat : DStrat := .mk # λ s =>
  let xs := do
    let p ← getPs 7
    guard # s.dMove p |>.isSome
    return p
  xs.head?

def strat : Strat := ⟨aStrat, dStrat⟩

def State.toStr (s : State) : String := String.mk # do
  let d := 10
  let p ← getPs d
  let ⟨x, y⟩ := p
  let sp := do
    guard # x + d = 0 ∧ y + d ≠ 0
    return '\n'
  let c := if p = s.aPos then '@'
    else if p ∈ s.taken then '#'
    else '.'
  sp ++ [c]

instance : ToString State := ⟨State.toStr⟩

def logb : IO Unit := do
  IO.println ""
  IO.println # String.mk # List.replicate 100 '='
  IO.println ""

def _root_.main : IO Unit := do
  let n := 1000
  let (res, k) := sys.simulate strat.f (initState 1) n
  IO.println # toString n ++ " ---> " ++ toString k
  logb
  IO.println # res