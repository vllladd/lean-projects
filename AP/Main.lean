import AP.Util
import AP.Misc
import AP.Analysis
import AP.Sokoban
import AP.AP

namespace AP

def getPs (d : ℕ) : List PointZ :=
  (⟨0, 0⟩ : PointZ).nbhd d

def State.toStr (s : State) : String := String.mk # do
  let d := 5
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

def state₀ : State :=
  initState 1 0

def aStrat : AStrat := .mkFold (α := Dir)
  state₀ Dir.up (fd := λ _ _ z => z) # λ s d =>
  (s.aPos + d.point, d.rotRight)

def dStrat : DStrat := .mkFold (α := PointZ × Dir)
  state₀ (⟨-2, -2⟩, Dir.up) (fa := λ _ _ z => z) # λ _ ⟨p, d⟩ =>
  let cnd := |p.coord d| = 2
  let d₁ := if cnd then d.rotRight else d
  let p₁ := p + d₁.point
  (p, (p₁, d₁))

def strat : Strat := ⟨aStrat, dStrat⟩

def run (s : State) (n : ℕ) : IO Unit := do
  IO.println s.toStr
  match n with
  | 0 => pure ()
  | n + 1 => match sys.tr s (strat.f s) with
    | none => pure ()
    | some s₁ => do
      IO.println ""
      run s₁ n

def _root_.main : IO Unit := do
  run state₀ 100