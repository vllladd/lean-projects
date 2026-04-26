import Projects.Util
import Projects.Misc
import Projects.AP
import Projects.Sokoban
import Projects.RatRect
import Projects.RealAnalysis
import Projects.RealEquiv
import Projects.DigitalRoot
import Projects.Physics
import Projects.Knowledge
import Projects.Inference
import Projects.Fixpoint
import Projects.Paramodulator
import Projects.Esolangs
import Projects.SK
import Projects.Kolakoski

-- namespace AP
-- 
-- def State.toStr (s : State) : String := String.ofList # do
--   let d := 7
--   let p ← s.aPos.nbhd d
--   let ⟨x, y⟩ := p - s.aPos
--   let sp := do
--     guard # x + d = 0 ∧ y + d ≠ 0
--     return '\n'
--   let c := if p = s.aPos then '@'
--     else if p ∈ s.taken then '#'
--     else '.'
--   sp ++ [c]
-- 
-- instance : ToString State := ⟨State.toStr⟩
-- 
-- def logb : IO Unit := do
--   IO.println ""
--   IO.println # String.ofList # List.replicate 100 '='
--   IO.println ""
-- 
-- -----
-- 
-- def state₀ : State :=
--   initState 1 ⟨0, 0⟩
-- 
-- def mkDigit (d : ℕ) : Char :=
--   let c := '0'.val + d.toUInt32
--   if h : c.isValidChar then ⟨c, h⟩ else default
-- 
-- def movesMp : Map Char PointZ :=
--   Map.ofList # List.range 9 |>.map # λ i =>
--     (mkDigit # i + 1, ⟨i % 3 - 1, 1 - i / 3⟩)
-- 
-- def parseAMove (inp : String) : Option PointZ :=
--   match inp.toList with
--   | [] => none
--   | _ :: _ :: _ => none
--   | [c] => movesMp.get? c
-- 
-- def readAMove : IO # Option # Option PointZ := do
--   let stdin ← IO.getStdin
--   IO.print "\n> "
--   let inp ← stdin.getLine
--   let inp := String.ofList # inp.toList.filter (· ∉ "\r\n".toList)
--   
--   if inp = "q" then
--     return none
--   
--   pure # some # parseAMove inp
-- 
-- -- instance {s} : Decidable # Edge.cnd₀ s := by
-- --   simp [Edge.cnd₀]; split <;> all_goals infer_instance
-- 
-- def run (s : State) (isFst : Bool) (n : ℕ) : IO Unit := do
--   match n with
--   | 0 => pure ()
--   | n + 1 => do
--     let p? ← match s.aTurn with
--     | false => pure # some # King.dKingOp.f s
--     | true => do
--       if !isFst then logb else pure ()
--       IO.println s.toStr
--       match ←readAMove with
--       | none => return
--       | some p => pure # p.map (s.aPos + ·)
--     match p? with
--     | none => do
--       IO.println "Invalid command"
--       run s false n
--     | some p => do
--       -- IO.println # repr p
--       match sys.tr s p with
--       | none => do
--         IO.println "Illegal move"
--         run s false n
--       | some s' => run s' false n
-- 
-- def _root_.main : IO Unit := do
--   let st : Strat := ⟨.mk # λ s => some # s.aPos + ⟨1, 1⟩, King.dKingOp⟩
--   let state := sys.simulate st.f state₀ 200 |>.1
--   run state true # 2 ^ 30
-- 
-- -----
-- 
-- theorem toList_movesMp : movesMp.toList =
-- [ ('1', ⟨-1, 1⟩), ('2', ⟨0, 1⟩), ('3', ⟨1, 1⟩)
-- , ('4', ⟨-1, 0⟩), ('5', ⟨0, 0⟩), ('6', ⟨1, 0⟩)
-- , ('7', ⟨-1, -1⟩), ('8', ⟨0, -1⟩), ('9', ⟨1, -1⟩)
-- ] := by native_decide
-- 
-- theorem parseAMove_8 : parseAMove "8" = some Dir.up.point := by native_decide
-- theorem parseAMove_6 : parseAMove "6" = some Dir.right.point := by native_decide
-- theorem parseAMove_2 : parseAMove "2" = some Dir.down.point := by native_decide
-- theorem parseAMove_4 : parseAMove "4" = some Dir.left.point := by native_decide
-- 
-- -- theorem cnd_state₀ : Edge.cnd₀ state₀ := by native_decide

def main : IO Unit := do
  IO.println "ok"