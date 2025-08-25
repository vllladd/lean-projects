import AP.AP.Determinacy

namespace AP

def AStrat.histBlind (a : AStrat) : Prop :=
  ∀ s hist, AState s → sys.WF (s.setHist hist) →
  sys.hasTr s → a.f (s.setHist hist) = a.f s

def DStrat.histBlind (d : DStrat) : Prop :=
  ∀ s hist, DState s → sys.WF (s.setHist hist) →
  sys.hasTr s → d.f (s.setHist hist) = d.f s