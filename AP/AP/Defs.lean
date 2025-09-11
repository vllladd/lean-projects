import AP.Point
import AP.System

namespace AP

@[ext]
structure State : Type where
  pw : ℕ
  taken : Set' PointZ
  aPos : PointZ
  aTurn : Bool
  hist : List PointZ
deriving DecidableEq

@[ext]
structure AStrat : Type where mk' ::
  f : State → PointZ

@[ext]
structure DStrat : Type where mk' ::
  f : State → PointZ

@[ext]
structure Strat : Type where
  a : AStrat
  d : DStrat

-----

def initState (pw : ℕ) (aPos : PointZ) : State :=
  { pw := pw
  , taken := ∅
  , aPos := aPos
  , aTurn := false
  , hist := [aPos]
  }

def State.aMove (s : State) (p : PointZ) : Option State := do
  guard # s.aPos ≠ p
  guard # p ∉ s.taken
  guard # p.dist s.aPos ≤ s.pw
  return {s with aPos := p}

def State.dMove (s : State) (p : PointZ) : Option State := do
  guard # s.aPos ≠ p
  guard # p ∉ s.taken
  return {s with taken := s.taken.insert p}

def State.move (s : State) (p : PointZ) : Option State := do
  let s' ← if s.aTurn then s.aMove p else s.dMove p
  return {s' with aTurn := ¬s.aTurn, hist := p :: s.hist}

def sys : System State PointZ :=
  { initial := {s | ∃ pw p, initState pw p = s}
  , tr := State.move
  }

class AStrat.WF (a : AStrat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → s.aTurn → sys.validTr s (a.f s)

class DStrat.WF (d : DStrat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → s.aTurn = false → sys.validTr s (d.f s)

def Strat.f (st : Strat) (s : State) : PointZ :=
  if s.aTurn then st.a.f s else st.d.f s

class Strat.WF (st : Strat) : Prop where
  h : ∀ {s} [sys.WF s], sys.hasTr s → sys.validTr s (st.f s)

def State.a_wins (s : State) (st : Strat) : Prop :=
  ∀ n, (sys.simulate st.f s n).2 = 0

def State.d_wins (s : State) (st : Strat) : Prop :=
  ∃ n, (sys.simulate st.f s n).2 ≠ 0

def State.aHws (s : State) : Prop :=
  ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩

def State.dHws (s : State) : Prop :=
  ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩

def aHwsPw (pw : ℕ) : Prop :=
  ∀ p, (initState pw p).aHws

def dHwsPw (pw : ℕ) : Prop :=
  ∀ p, (initState pw p).dHws