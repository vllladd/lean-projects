import AP.Point
import AP.System.Main

namespace Sokoban

@[ext]
structure Tile where
  player : Bool
  box : Bool
  target : Bool
  wall : Bool
deriving Inhabited

@[ext]
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
deriving Inhabited, Fintype

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

def State.movePlayer (s : State) (p : PointZ) : State :=
  { s with
    player := p
    grid := s.grid.modifyMany
      [ (s.player, λ d => {d with player := false})
      , (p, λ d => {d with player := true})
      ]
  }

def State.moveBox (s : State) (p₁ p₂ : PointZ) : State :=
  { s with
    grid := s.grid.modifyMany
      [ (p₁, λ d => {d with box := false})
      , (p₂, λ d => {d with box := true})
      ]
  }

def State.move (s : State) (m : Move) : Option State := do
  let p_dif := m.toPoint
  let p₁ := s.player + p_dif
  let d₁ ← s.grid.get? p₁
  guard # !d₁.wall
  if !d₁.box then s.movePlayer p₁ else do
    let p₂ := p₁ + p_dif
    let d₂ ← s.grid.get? p₂
    guard # !(d₂.box || d₂.wall)
    s.moveBox p₁ p₂ |>.movePlayer p₁

def State.solved (s : State) : Bool :=
  s.grid.all # λ _ d => d.target → d.box

-----

def sys : System State Move :=
  { initial := {s | s.Valid}
  , tr := State.move
  }