import AP.Sokoban.Basic

namespace Sokoban

private structure FinState (w h : ℕ) where
  mp : Map (Fin w × Fin h) Tile
  player : Fin w × Fin h
deriving Fintype

-- private def State.supReach (s : State) : Finset State := List.toFinset do
--   let grid ← do
--   { s with
--     grid := grid
--   }

-- theorem finite_reachable {s : State} [hs : s.Valid] :
-- {s' | sys.Reachable s s'}.Finite := by
--   apply Set.finite_of_subset_finset (s := s.supReach)