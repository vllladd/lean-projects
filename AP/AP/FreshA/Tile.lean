import AP.AP.FreshA.CurrentTile
import AP.AP.Moves

namespace AP

def AStrat.Fresh1A (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁

-----