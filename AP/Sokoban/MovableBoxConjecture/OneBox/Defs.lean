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