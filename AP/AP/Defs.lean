import AP.Point
import AP.System.Main

namespace AP

structure State : Type where
  pw : ℕ
  taken : Set' PointZ
  a_pos : PointZ
  a_turn : Bool
  hist : List PointZ
deriving Inhabited, DecidableEq

structure AStrat : Type where
  f : State → PointZ
deriving Inhabited

structure DStrat : Type where
  f : State → PointZ
deriving Inhabited

structure Strat : Type where
  a : AStrat
  d : DStrat
deriving Inhabited

-----

def state₀ (pw : ℕ) : State :=
  { pw := pw
  , taken := ∅
  , a_pos := 0
  , a_turn := false
  , hist := []
  }

def State.a_move (s : State) (p : PointZ) : Option State := do
  guard # s.a_pos ≠ p
  guard # p ∉ s.taken
  guard # p.dist s.a_pos ≤ s.pw
  return {s with a_pos := p, a_turn := false}

def State.d_move (s : State) (p : PointZ) : Option State := do
  guard # s.a_pos ≠ p
  guard # p ∉ s.taken
  return {s with taken := insert p s.taken, a_turn := true}

def State.move (s : State) (p : PointZ) : Option State :=
  if s.a_turn then s.a_move p else s.d_move p

def sys : System State PointZ :=
  { initial := {s | ∃ pw, state₀ pw = s}
  , tr := State.move
  }

@[class]
structure AStrat.Valid (a : AStrat) : Prop where
  h : ∀ {s} [sys.Valid s], sys.hasTr s → s.a_turn → sys.validTr s (a.f s)

@[class]
structure DStrat.Valid (d : DStrat) : Prop where
  h : ∀ {s} [sys.Valid s], sys.hasTr s → s.a_turn = false → sys.validTr s (d.f s)

def Strat.f (st : Strat) (s : State) : PointZ :=
  if s.a_turn then st.a.f s else st.d.f s

@[class]
structure Strat.Valid (st : Strat) : Prop where
  h : ∀ {s} [sys.Valid s], sys.hasTr s → sys.validTr s (st.f s)

def State.a_wins (s : State) (st : Strat) : Prop :=
  ∀ n, (sys.simulate st.f s n).2 = 0

def State.d_wins (s : State) (st : Strat) : Prop :=
  ¬s.a_wins st

def State.a_hws (s : State) : Prop :=
  ∃ (a : AStrat), a.Valid ∧ ∀ (d : DStrat), d.Valid → s.a_wins ⟨a, d⟩

def State.d_hws (s : State) : Prop :=
  ∃ (d : DStrat), d.Valid ∧ ∀ (a : AStrat), a.Valid → s.d_wins ⟨a, d⟩

def a_hws_pw (pw : ℕ) : Prop :=
  (state₀ pw).a_hws

def d_hws_pw (pw : ℕ) : Prop :=
  (state₀ pw).d_hws