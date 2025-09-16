import AP.AP.Trap

namespace AP

class AStrat.HistBlind (a : AStrat) : Prop where
  wf : a.WF
  h : ∀ s hist, AState s → sys.WF (s.setHist hist) →
    sys.hasTr s → a.f (s.setHist hist) = a.f s

class DStrat.HistBlind (d : DStrat) : Prop where
  wf : d.WF
  h : ∀ s hist, DState s → sys.WF (s.setHist hist) →
    sys.hasTr s → d.f (s.setHist hist) = d.f s