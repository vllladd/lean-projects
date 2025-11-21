import AP.Util
import AP.Misc
import AP.AP
import AP.Sokoban
import AP.RatRect
import AP.RealAnalysis
import AP.DigitalRoot
import AP.Physics
import AP.Knowledge
import AP.Inference

namespace AP

def center : PointZ :=
  ⟨0, -6⟩

def getPs (d : ℕ) : List PointZ :=
  center.nbhd d

def State.toStr (s : State) : String := String.mk # do
  let d := 7
  let p ← getPs d
  let ⟨x, y⟩ := p - center
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

-----

def state₀ : State :=
  initState 1 center

-- def defense : Defense :=
--   Edge.edge₀.defense

def defense : Defense where
  cnd := λ _ => True
  ps := ∅
  f := λ _ => none

def mkDigit (d : ℕ) : Char :=
  let c := '0'.val + d.toUInt32
  if h : c.isValidChar then ⟨c, h⟩ else default

def movesMp : Map Char PointZ :=
  Map.ofList # List.range 9 |>.map # λ i =>
    (mkDigit # i + 1, ⟨i % 3 - 1, 1 - i / 3⟩)

def parseAMove (inp : String) : Option PointZ :=
  match inp.toList with
  | [] => none
  | _ :: _ :: _ => none
  | [c] => movesMp.get? c

def readAMove : IO (Option PointZ) := do
  let stdin ← IO.getStdin
  IO.print "\n> "
  let inp ← stdin.getLine
  pure # parseAMove ⟨inp.1.filter (· ∉ "\r\n".1)⟩

-- instance {s} : Decidable # Edge.cnd₀ s := by
--   simp [Edge.cnd₀]; split <;> all_goals infer_instance

def run (s : State) (isFst : Bool) (n : ℕ) : IO Unit := do
  match n with
  | 0 => pure ()
  | n + 1 => do
    let p? ← match s.aTurn with
    | false => pure # some # match defense.f s with
      | some p => p
      | none => s.chooseDMove + 100
    | true => do
      if !isFst then logb else pure ()
      IO.println s.toStr
      
      -- IO.println # "\n" ++ repr (Edge.edge₀.dist s.aPos)
      
      let p ← readAMove
      pure # p.map (s.aPos + ·)
    match p? with
    | none => do
      IO.println "Invalid command"
      run s false n
    | some p => do
      -- IO.println # repr p
      match sys.tr s p with
      | none => do
        IO.println "Illegal move"
        run s false n
      | some s' => run s' false n

def _root_.main : IO Unit := do
  run state₀ true # 2 ^ 30

-----

theorem toList_movesMp : movesMp.toList =
[ ('1', ⟨-1, 1⟩), ('2', ⟨0, 1⟩), ('3', ⟨1, 1⟩)
, ('4', ⟨-1, 0⟩), ('5', ⟨0, 0⟩), ('6', ⟨1, 0⟩)
, ('7', ⟨-1, -1⟩), ('8', ⟨0, -1⟩), ('9', ⟨1, -1⟩)
] := by native_decide

theorem parseAMove_8 : parseAMove "8" = some Dir.up.point := by native_decide
theorem parseAMove_6 : parseAMove "6" = some Dir.right.point := by native_decide
theorem parseAMove_2 : parseAMove "2" = some Dir.down.point := by native_decide
theorem parseAMove_4 : parseAMove "4" = some Dir.left.point := by native_decide

-- theorem cnd_state₀ : Edge.cnd₀ state₀ := by native_decide