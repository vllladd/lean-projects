import Projects.Dir
import Projects.System

namespace Sokoban

@[ext]
structure Tile where
  player : Bool
  box : Bool
  target : Bool
  wall : Bool
deriving Inhabited, DecidableEq, Fintype

@[ext]
structure State where
  width : ℕ
  height : ℕ
  grid : Map PointZ Tile
  player : PointZ
  unsolvedNum : ℕ
deriving Inhabited, DecidableEq

abbrev Move := Dir

def State.points (s : State) : Set' PointZ :=
  s.grid.keysSet

def State.boxes (s : State) : Set' PointZ :=
  s.points.filter # λ p => s.grid.get! p |>.box

def State.targets (s : State) : Set' PointZ :=
  s.points.filter # λ p => s.grid.get! p |>.target

-----

@[class]
structure State.Get (s : State) (p : PointZ) (d : outParam Tile) : Prop where
  h : s.grid.get? p = d

@[class]
structure State.Get' (s : State) (d : Tile) : Prop where
  h : ∃ p, s.Get p d

@[class]
structure Tile.WF (d : Tile) : Prop where
  tw : [d.target, d.wall].atMostOne
  pbw : [d.player, d.box, d.wall].atMostOne

@[class]
structure State.WF (s : State) : Prop where
  mem_grid_iff_bounds {p} : p ∈ s.grid ↔ 0 ≤ p.x ∧ 0 ≤ p.y ∧
    p.x < s.width ∧ p.y < s.height
  wf_get {d} : s.Get' d → d.WF
  player_mem : s.player ∈ s.grid
  tile_player_iff {p d} : s.Get p d → (d.player ↔ s.player = p)
  unsolvedNum_eq : s.unsolvedNum = s.grid.values.countP (λ d => d.box && !d.target)
  size_boxes_eq_size_targets : s.boxes.size = s.targets.size

-----

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
    unsolvedNum := s.unsolvedNum +
      (if s.grid.get! p₁ |>.target then 1 else 0) -
      (if s.grid.get! p₂ |>.target then 1 else 0)
  }

def State.move (s : State) (m : Move) : Option State := do
  let p_dif := m.point
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
  { initial := {s | s.WF}
  , tr := State.move
  }