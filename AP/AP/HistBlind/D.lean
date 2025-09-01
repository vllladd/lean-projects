import AP.AP.HistBlind.A

namespace AP

instance : (default : DStrat).histBlind := by
  simp [DStrat.histBlind]

-- #check 0 #exit

theorem State.d_hws_histBlind_of_d_hws {s} [hs : sys.WF s] (h : s.d_hws) :
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ := by
  sorry

-- #check 0 #exit

theorem State.d_hws_iff_d_hws_histBlind {s} [hs : sys.WF s] : s.d_hws ↔
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ :=
  ⟨d_hws_histBlind_of_d_hws, λ ⟨d, Hd, h₁, h₂⟩ => by use d⟩