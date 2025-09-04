import AP.AP.HistBlind.Defs

namespace AP

theorem AStrat.histBlind_def {a : AStrat} :
a.HistBlind ↔ a.WF ∧ ∀ s hist, AState s → sys.WF (s.setHist hist) →
sys.hasTr s → a.f (s.setHist hist) = a.f s :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem DStrat.histBlind_def {d : DStrat} :
d.HistBlind ↔ d.WF ∧ ∀ s hist, DState s → sys.WF (s.setHist hist) →
sys.hasTr s → d.f (s.setHist hist) = d.f s :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

instance {a : AStrat} [ha : a.HistBlind] : a.WF := ha.wf
instance {d : DStrat} [hd : d.HistBlind] : d.WF := hd.wf

instance : (default : AStrat).HistBlind := by
  simp [AStrat.histBlind_def]; infer_instance

instance : (default : DStrat).HistBlind := by
  simp [DStrat.histBlind_def]; infer_instance