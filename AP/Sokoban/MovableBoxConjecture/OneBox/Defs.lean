import AP.Sokoban.MovableBoxConjecture.Basic

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
  Classical.epsilon # stateCnd₀ size₀

open Classical in noncomputable
def trBox₁ : PointZ :=
  state₀.trBox

open Classical in noncomputable
def state₁ : State :=
  Classical.epsilon # λ s => sys.Reachable state₀ s ∧ s.boxes = .singleton trBox₁

open Classical in noncomputable
def state₂ : State :=
  Classical.epsilon # λ s => sys.Reachable state₁ s ∧ s.boxes ≠ .singleton trBox₁