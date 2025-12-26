import AP.Sokoban.MovableBoxConjecture.Basic

namespace Sokoban

class AlwaysMovable1 (s : State) extends AlwaysMovable s where
  h₂ : s.boxes.size = 1

class MovableBoxConjecture1 : Prop where
  h : ∃ (s : State), AlwaysMovable1 s

namespace MovableBoxConjecture1

open State MovableBoxConjecture

def stateAM1Cnd (n : ℕ) (s : State) : Prop :=
  AlwaysMovable1 s ∧ s.boxesReachable.size = n

open Classical in noncomputable
def sizeAM1Min : ℕ :=
  Nat.find! λ n => ∃ s, stateAM1Cnd n s

open Classical in noncomputable
def stateAM1Min : State :=
  Classical.epsilon # stateAM1Cnd sizeAM1Min