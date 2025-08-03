import AP.Point
import AP.System.Main

namespace Sokoban

structure Tile where
  player : Bool
  box : Bool
  target : Bool
  wall : Bool
deriving Inhabited

structure State where
  width : ℕ
  height : ℕ
  grid : Map PointZ Tile
  player : PointZ
deriving Inhabited

inductive Move where
| up : Move
| left : Move
| right : Move
| down : Move
deriving Inhabited

-----

structure Tile.Valid (d : Tile) : Prop where
  h₁ : [d.player, d.box, d.wall].atMostOne
  h₂ : [d.target, d.wall].atMostOne

structure State.Valid (s : State) : Prop where
  h₁ : ∀ p, p ∈ s.grid ↔ 0 ≤ p.x ∧ 0 ≤ p.y ∧
    p.x < s.width ∧ p.y < s.height
  h₂ : ∀ d ∈ s.grid.values, d.Valid
  h₃ : ∀ p ∈ s.grid, (s.grid.get! p).player ↔ s.player = p

structure State.ValidTargets (s : State) extends State.Valid s where
  h₄ : s.grid.values.countP (·.box) = s.grid.values.countP (·.target)

-----

def Move.toPoint : Move → PointZ
| .up => ⟨0, -1⟩
| .left => ⟨-1, 0⟩
| .right => ⟨1, 0⟩
| .down => ⟨0, 1⟩

def State.solved (s : State) : Bool :=
  s.grid.all # λ _ d => d.target → d.box