import AP.AP.HistBlind.A

namespace AP

@[ext]
structure Defense : Type where
  cnd : State → Prop
  ps : Set PointZ
  f : State → Option PointZ

namespace Defense

def st (dse : Defense) (d : DStrat) : DStrat :=
  .mk # λ s => dse.f s |>.getD (d.f s)

class WF (dse : Defense) : Prop where
  h : ∀ s [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF], ∀ (d : DStrat) [d.WF] n,
    (sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps