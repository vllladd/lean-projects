import AP.Util

noncomputable section
open scoped Classical

@[ext]
structure Point where
  x : ℤ
  y : ℤ

def point₀ : Point := ⟨0, 0⟩

instance : Inhabited Point := ⟨point₀⟩

def Point.dist (a b : Point) : ℕ :=
  Int.toNat # |a.x - b.x| + |a.y - b.y|

abbrev Grid := Set Point

def grid₀ : Grid := Set.univ

@[ext]
structure State' where
  pw : ℕ
  grid : Grid
  a : Point

@[ext]
structure State where
  state : State'
  hist : List State'

def state'₀ (pw : ℕ) : State' :=
  { pw := pw
  , grid := grid₀
  , a := point₀
  }

def state₀ (pw : ℕ) : State :=
  {state := state'₀ pw, hist := []}

instance : Inhabited State' := ⟨state'₀ 0⟩
instance : Inhabited State := ⟨state₀ 0⟩

def State.push (st : State) (s : State') : State :=
  {st with state := s, hist := st.hist.snoc st.state}

abbrev Moves := State' → Set State'

@[ext]
structure Strat where
  moves : Moves
  f : State → Option State'
  h : ∀ (s : State),
    let set := moves s.state
    match f s with
    | none => set = ∅
    | some s₁ => s₁ ∈ set

def State'.a_move (s s₁ : State') := ∃ (a₁ : Point),
  s₁ = {s with a := a₁} ∧
  a₁ ∈ s.grid ∧
  a₁ ≠ s.a ∧
  a₁.dist s.a ≤ s.pw

def State'.d_move (s s₁ : State') := ∃ (p : Point),
  s₁ = {s with grid := s.grid.erase p} ∧
  p ∈ s.grid ∧
  p ≠ s.a

def A_moves (s : State') := setOf s.a_move
def D_moves (s : State') := setOf s.d_move

def StratT (moves : Moves) := {st : Strat // st.moves = moves}
def A_strat := StratT A_moves
def D_strat := StratT D_moves

instance {moves : Moves} : Inhabited (StratT moves) := by
  refine' ⟨⟨moves, _, _⟩, by simp⟩
  · intro s; exact if h : ∃ x, x ∈ moves s.state then
      some # Classical.choose h else none
  · intro s; simp; split_ifs with h <;> simp
    · apply Classical.choose_spec
    · exact Set.not_nonempty_iff_eq_empty.mp h

instance : Inhabited A_strat := ⟨(default : StratT _)⟩
instance : Inhabited D_strat := ⟨(default : StratT _)⟩

@[ext]
structure Game where
  a : A_strat
  d : D_strat
  state : State
  a_turn : Prop
  ended : Prop

def Game.dflt : Game :=
  { a := default
  , d := default
  , state := default
  , a_turn := default
  , ended := default
  }

instance : Inhabited Game := ⟨Game.dflt⟩

abbrev State.pw (s : State) := s.state.pw
abbrev Game.pw (g : Game) := g.state.pw
abbrev Game.d_turn (g : Game) := ¬g.a_turn
abbrev Game.state' (g : Game) := g.state.state

def game₀ (pw : ℕ) (a : A_strat) (d : D_strat) : Game :=
  { a := a
  , d := d
  , state := state₀ pw
  , a_turn := False
  , ended := False
  }

@[simp]
def Game.f (g : Game) := if g.a_turn then g.a.1.f else g.d.1.f

def Game.move (g : Game) : Game :=
  if g.ended then g else
  match g.f g.state with
  | none => {g with ended := True}
  | some s => {g with state := g.state.push s, a_turn := g.d_turn}

def Game.play (n : ℕ) (g : Game) := Game.move^[n] g

def Game.a_wins (g : Game) := ∀ n, ¬(g.play n).ended
def Game.d_wins (g : Game) := ¬g.a_wins

def a_hws (pw : ℕ) := ∃ a, ∀ d, (game₀ pw a d).a_wins
def d_hws (pw : ℕ) := ∃ d, ∀ a, (game₀ pw a d).d_wins