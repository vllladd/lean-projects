import Projects.Sokoban.MovableBoxConjecture.Defs

namespace Sokoban.MovableBoxConjecture.Alt₁

open State

inductive Tile where
| Floor | Player | Box | Wall
deriving DecidableEq

open Sokoban.MovableBoxConjecture.Alt₁.Tile

structure State where
  get : ℤ × ℤ → Tile
  finite : {p | get p ≠ Wall}.Finite
  player : ∃! p, get p = Player

structure Step (s t : State) where
  (p d : ℤ × ℤ)
  dist : |d.1| + |d.2| = 1
  player₁ : s.get p = Player
  player₂ : t.get (p + d) = Player
  floor : t.get p = Floor
  box : if s.get (p + d) = Box
    then s.get (p + d * 2) = Floor ∧ t.get (p + d * 2) = Box
    else s.get (p + d) = Floor ∧ s.get (p + d * 2) = t.get (p + d * 2)
  congr : ∀ q (k : Fin 3), q ≠ p + d * k → s.get p = t.get p

inductive Reachable : State → State → Prop where
| refl {s} : Reachable s s
| step {s t t'} : Reachable s t → Step t t' → Reachable s t'

def Conjecture : Prop :=
  ∃ s, ∀ t, Reachable s t → ∃ t' p, Reachable t t' ∧ t.get p = Box ↔ t'.get p ≠ Box