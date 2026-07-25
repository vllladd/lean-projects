import Projects.AP.Reachability

namespace AP

-- Given function `f` and states `s` and `s₁`,
-- determines whether `s₁` is reachable from `s` via `f`
def State.ReachableVia' (f : State → PointZ) (s s₁ : State) : Prop :=
  ∃ n, sys.simulate f s n = (s₁, 0)

-- Given strategy `st` and states `s` and `s₁`,
-- determines whether `s₁` is reachable from `s` via `st`
def State.ReachableVia (st : Strat) (s s₁ : State) : Prop :=
  s.ReachableVia' st.f s₁

instance {s s₁ : State} {st} : Decidable # s.ReachableVia st s₁ := by
  apply decidable_of_bool # sys.simulate st.f s (s.diff s₁) = (s₁, 0)
  simp [State.ReachableVia, State.ReachableVia']; constructor; tauto
  rintro ⟨n, h⟩; simpa [State.diff_eq_of_simulate h]

-- Given start state `s`, strategy `st` and future state `s₁`,
-- if `s₁` can be reached from `s` via `st`,
-- returns either A move or D move performed is `s₁`
def State.moveSim (s : State) (st : Strat) (s₁ : State) :
Option # (PointZ × State) ⊕ (PointZ × State) := do
  guard # s.ReachableVia st s₁
  let p := st.f s₁
  let s₂ ← sys.tr s₁ p
  pure # ite s₁.aTurn Sum.inr Sum.inl (p, s₂)

-- Given start state `s`, strategy `st` and future state `s₁`,
-- if `s₁` is A state and can be reached from `s` via `st`,
-- returns A move performed in `s₁`
def State.aMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inr r => some r
  | _ => none

-- Given start state `s`, strategy `st` and future state `s₁`,
-- if `s₁` is D state and can be reached from `s` via `st`,
-- returns D move performed in `s₁`
def State.dMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inl r => some r
  | _ => none

-- Given state `s` and strategy `st`,
-- returns the set of all future A states and moves at these states
def State.aSimPairs (s : State) (st : Strat) : Set (State × PointZ) :=
  {(s₁, p) | ∃ s₂, s.aMoveSim st s₁ = some (p, s₂)}

-- Given state `s` and strategy `st`,
-- returns the set of all future A moves
def State.aSimPts (s : State) (st : Strat) : Set PointZ :=
  Prod.snd '' s.aSimPairs st

-- Given state `s` and strategy `st`,
-- returns the set of all future states
def State.simStates (s : State) (st : Strat) : Set State :=
  Set.ofPred # s.ReachableVia st

def State.simStatesRangeAuxVia (r : ℕ → ℕ → Prop) [hs : DecidableRel r]
(st : Strat) (s s₁ : State) : Finset State :=
  if ¬s.ReachableVia st s₁ then ∅ else
  Finset.Icc 0 (s.diff s₁) |>.image (λ n => sys.simulate st.f s n |>.1)
    |>.filter λ s₂ => r s₂.hist.length s₁.hist.length

-- Interval of states `[s, s₁]` via strategy `st`
def State.simStatesIccVia (st : Strat) (s s₁ : State) : Finset State :=
  s.simStatesRangeAuxVia (· ≤ ·) st s₁

-- Interval of states `[s, s₁)` via strategy `st`
def State.simStatesIcoVia (st : Strat) (s s₁ : State) : Finset State :=
  s.simStatesRangeAuxVia (· < ·) st s₁

-- A states in interval `[s, s₁]` via strategy `st`
def State.aSimStatesIccVia (st : Strat) (s s₁ : State) : Finset State :=
  s.simStatesIccVia st s₁ |>.filter (·.aTurn)

-- A states in interval `[s, s₁)` via strategy `st`
def State.aSimStatesIcoVia (st : Strat) (s s₁ : State) : Finset State :=
  s.simStatesIcoVia st s₁ |>.filter (·.aTurn)

-- Set of all future A states via strategy `st`
def State.aSimStates (s : State) (st : Strat) : Set State :=
  s.simStates st |>.filter (·.aTurn)

-- Initial state of the given state
def State.init (s : State) : State :=
  initState s.pw s.aPos₀

-- Previous state
def State.prev (s : State) : State :=
  sys.trs s.init (s.init.diffTrs s |>.init) |>.1

-- Last move
def State.lastMove (s : State) : PointZ :=
  s.prev.diffTrs s |>.getLast!

-- Checks whether the state is initial
def State.IsInit (s : State) : Prop :=
  sys.Initial s

-- The cardinality of the set of all future A moves
noncomputable
def State.aSimPtsNcard (s : State) (st : Strat) (set : Set PointZ) : Option ℕ :=
  s.aSimPairs st |>.filter (·.2 ∈ set) |>.ncard?

-- Create a strategy from a function
def Strat.ofFn (f : State → Option PointZ) : Strat where
  a := .mk f
  d := .mk f

-- Returns a strategy that goes from `s` to `s₁` (if it exists)
def State.diffStrat (s s₁ : State) : Strat :=
  .ofFn λ s' => (s.diffTrs s₁)[s.diff s']?

-- Interval of states `[s, s₁]`
def State.simStatesIcc (s s₁ : State) : Finset State :=
  s.simStatesIccVia (s.diffStrat s₁) s₁

-- Interval of states `[s, s₁)`
def State.simStatesIco (s s₁ : State) : Finset State :=
  s.simStatesIcoVia (s.diffStrat s₁) s₁

-- A states in interval `[s, s₁]`
def State.aSimStatesIcc (s s₁ : State) : Finset State :=
  s.aSimStatesIccVia (s.diffStrat s₁) s₁

-- A states in interval `[s, s₁)`
def State.aSimStatesIco (s s₁ : State) : Finset State :=
  s.aSimStatesIcoVia (s.diffStrat s₁) s₁

def State.aVisitedIcc' (s : State) (ps : List PointZ) : Set' PointZ :=
  match ps with
  | [] => ∅
  | p :: ps =>
    let set := sys.tr s p |>.getd.aVisitedIcc' ps
    if s.aTurn then set.insert p else set

-- Set of all `aPos` from `[s, s₁]`
def State.aVisitedIcc (s s₁ : State) : Set' PointZ :=
  if sys.Reachable s s₁ then State.aVisitedIcc' s (s.diffTrs s₁) |>.insert s.aPos else ∅

-- Set of all `aPos` from `[s, s₁)`
def State.aVisitedIco (s s₁ : State) : Set' PointZ :=
  if s = s₁ then ∅ else s.aVisitedIcc s₁.prev

def State.aVisitedIcoPrev (s s₁ : State) : Set' PointZ :=
  if s.diff s₁ ≤ 1 then ∅ else s.aVisitedIco s₁.prev

def State.aNbhdsIcoPrev (s s₁ : State) : Set' PointZ :=
  s.aVisitedIcoPrev s₁ |>.bind (·.nbhd s.pw)