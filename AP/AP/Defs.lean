import AP.Point
import AP.System

namespace AP

structure State : Type where
  pw : ℕ
  taken : Set' PointZ
  a_pos : PointZ
  aTurn : Bool
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

def initState (pw : ℕ) : State :=
  { pw := pw
  , taken := ∅
  , a_pos := 0
  , aTurn := false
  , hist := []
  }

def State.aMove (s : State) (p : PointZ) : Option State := do
  guard # s.a_pos ≠ p
  guard # p ∉ s.taken
  guard # p.dist s.a_pos ≤ s.pw
  return {s with a_pos := p}

def State.dMove (s : State) (p : PointZ) : Option State := do
  guard # s.a_pos ≠ p
  guard # p ∉ s.taken
  return {s with taken := insert p s.taken}

def State.move (s : State) (p : PointZ) : Option State := do
  let s' ← if s.aTurn then s.aMove p else s.dMove p
  return { s' with aTurn := ¬s.aTurn, hist := p :: s.hist}

def sys : System State PointZ :=
  { initial := {s | ∃ pw, initState pw = s}
  , tr := State.move
  }

@[class]
structure AStrat.WF (a : AStrat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → s.aTurn → sys.validTr s (a.f s)

@[class]
structure DStrat.WF (d : DStrat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → s.aTurn = false → sys.validTr s (d.f s)

def Strat.f (st : Strat) (s : State) : PointZ :=
  if s.aTurn then st.a.f s else st.d.f s

@[class]
structure Strat.WF (st : Strat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → sys.validTr s (st.f s)

def State.a_wins (s : State) (st : Strat) : Prop :=
  ∀ n, (sys.simulate st.f s n).2 = 0

def State.d_wins (s : State) (st : Strat) : Prop :=
  ¬s.a_wins st

def State.a_hws (s : State) : Prop :=
  ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩

def State.d_hws (s : State) : Prop :=
  ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩

def a_hws_pw (pw : ℕ) : Prop :=
  (initState pw).a_hws

def d_hws_pw (pw : ℕ) : Prop :=
  (initState pw).d_hws