import Projects.Sokoban.MovableBoxConjecture.Basic

namespace Sokoban

class AlwaysMovable1 (s : State) extends AlwaysMovable s where
  h₂ : s.boxes.size = 1

class MovableBoxConjecture1 : Prop where
  h : ∃ (s : State), AlwaysMovable1 s

namespace MovableBoxConjecture1

open State MovableBoxConjecture

def stateCnd₀ (n : ℕ) (s : State) : Prop :=
  AlwaysMovable1 s ∧ s.boxesReachable.size = n

open Classical in noncomputable
def size₀ : ℕ :=
  Nat.find! λ n => ∃ s, stateCnd₀ n s

open Classical in noncomputable
def state₀ : State :=
  τ s, stateCnd₀ size₀ s

open Classical in noncomputable
def trBox₁ : PointZ :=
  state₀.trBox

open Classical in noncomputable
def state₁ : State :=
  τ s, sys.Reachable state₀ s ∧ s.boxes = .singleton trBox₁

open Classical in noncomputable
def state₂ : State :=
  τ s, sys.Reachable state₁ s ∧ s.boxes ≠ .singleton trBox₁

open Classical in noncomputable
def _root_.Sokoban.State.box (s : State) : PointZ :=
  τ p, p ∈ s.boxes

open Classical in noncomputable
def state₃ : State :=
  τ s, s.box = trBox₁ ∧ ∃ s', sys.Reachable state₂ s' ∧ s'.BoxPushed s

open Classical in noncomputable
def state₃' : State :=
  τ s, sys.Reachable state₂ s ∧ s.BoxPushed state₃