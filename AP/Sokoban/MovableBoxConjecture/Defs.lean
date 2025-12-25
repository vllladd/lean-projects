import AP.Sokoban.Card

namespace Sokoban

def State.AlwaysMovable (s : State) : Prop :=
  sys.WF s ∧ ∀ s₁, sys.Reachable s s₁ → ∃ s₂, sys.Reachable s₁ s₂ ∧ s₁.boxes ≠ s₂.boxes

def MovableBoxConjecture : Prop :=
  ∃ (s : State), s.AlwaysMovable