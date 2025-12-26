import AP.Sokoban.Card

namespace Sokoban

class AlwaysMovable (s : State) extends sys.WF s where
  h₁ : ∀ s₁, sys.Reachable s s₁ → ∃ s₂, sys.Reachable s₁ s₂ ∧ s₁.boxes ≠ s₂.boxes

class MovableBoxConjecture : Prop where
  h : ∃ (s : State), AlwaysMovable s