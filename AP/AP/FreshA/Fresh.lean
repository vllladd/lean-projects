import AP.AP.FreshA.Nbhd

namespace AP

def AStrat.Fresh (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  -- a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  -- ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁
  sorry

-- #check 0 #exit

-----