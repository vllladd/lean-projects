import AP.Util

noncomputable section
open scoped Classical

def Point := ℤ × ℤ

@[simp] abbrev Point.x (p : Point) := p.1
@[simp] abbrev Point.y (p : Point) := p.2

def point₀ : Point := (0, 0)
instance : Inhabited Point := ⟨point₀⟩

def Point.dist (a b : Point) : ℕ :=
  Int.toNat # max |a.x - b.x| |a.y - b.y|

abbrev Grid := Set Point

def grid₀ : Grid := Set.univ

@[ext]
structure State' where
  pw : ℕ
  grid : Grid
  a_pos : Point

@[ext]
structure State extends State' where
  hist : List State'

def state'₀ (pw : ℕ) : State' :=
  { pw := pw
  , grid := grid₀
  , a_pos := point₀
  }

def state₀ (pw : ℕ) : State :=
  {state'₀ pw with hist := []}

instance : Inhabited State' := ⟨state'₀ 0⟩
instance : Inhabited State := ⟨state₀ 0⟩

def State.push (st : State) (s : State') : State :=
  {s with hist := st.hist.snoc st.toState'}

abbrev Moves := State' → State' → Prop
abbrev Strat' := State → Option State'

@[ext]
structure StratT where
  moves : Moves
  f : Strat'
  h : ∀ (s : State),
    let g := moves s.toState'
    match f s with
    | none => ∀ s₁, ¬g s₁
    | some s₁ => g s₁

def State'.a_move (s s₁ : State') := ∃ (a₁ : Point),
  s₁ = {s with a_pos := a₁} ∧
  a₁ ∈ s.grid ∧
  a₁ ≠ s.a_pos ∧
  a₁.dist s.a_pos ≤ s.pw

def State'.d_move (s s₁ : State') := ∃ (p : Point),
  s₁ = {s with grid := s.grid.erase p} ∧
  p ∈ s.grid ∧
  p ≠ s.a_pos

@[simp] def AMoves (s : State') := s.a_move
@[simp] def DMoves (s : State') := s.d_move

def Strat (moves : Moves) := {st : StratT // st.moves = moves}
def AStrat := Strat AMoves
def DStrat := Strat DMoves

def Strat.ap {ms} (a : Strat ms) := a.1.f

instance {moves : Moves} : Inhabited (Strat moves) := by
  refine' ⟨⟨moves, _, _⟩, by simp⟩
  · intro s; exact if h : ∃ x, moves s.toState' x then
      some # Classical.choose h else none
  · intro s; simp; split_ifs with h <;> simp
    · apply Classical.choose_spec
    · simp at h; exact h

instance : Inhabited AStrat := ⟨(default : Strat _)⟩
instance : Inhabited DStrat := ⟨(default : Strat _)⟩

@[ext]
structure Game extends State where
  a : AStrat
  d : DStrat
  a_turn : Prop
  ended : Prop

def Game.dflt : Game :=
  { a := default
  , d := default
  , toState := default
  , a_turn := default
  , ended := default
  }

instance : Inhabited Game := ⟨Game.dflt⟩

abbrev Game.d_turn (g : Game) := ¬g.a_turn

def game₀ (pw : ℕ) (a : AStrat) (d : DStrat) : Game :=
  { a := a
  , d := d
  , toState := state₀ pw
  , a_turn := False
  , ended := False
  }

@[simp]
def Game.f (g : Game) := if g.a_turn then g.a.ap else g.d.ap

def Game.move (g : Game) : Game :=
  if g.ended then g else
  match g.f g.toState with
  | none => {g with ended := True}
  | some s => {g with toState := g.toState.push s, a_turn := g.d_turn}

def Game.play (n : ℕ) (g : Game) := Game.move^[n] g

def Game.a_wins (g : Game) := ∀ n, ¬(g.play n).ended
def Game.d_wins (g : Game) := ¬g.a_wins

def a_hws (pw : ℕ) := ∃ a, ∀ d, (game₀ pw a d).a_wins
def d_hws (pw : ℕ) := ∃ d, ∀ a, (game₀ pw a d).d_wins