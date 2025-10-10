import AP.AP.HistBlind.D

namespace AP

theorem State.aHws_iff_aHws_histBlind_both {s} [hs : sys.WF s] : s.aHws ↔
∃ (a : AStrat), a.HistBlind ∧ ∀ (d : DStrat), d.HistBlind → s.aWins ⟨a, d⟩ := by
  constructor
  · intro h
    rw [aHws_iff_aHws_histBlind] at h
    obtain ⟨a, ha, h⟩ := h
    use a, ha
    intro d hd
    apply h
    infer_instance
  · rintro ⟨a, ha, h⟩
    rw [←not_dHws_iff, dHws_iff_dHws_histBlind]
    push_neg
    simp
    intro d hd
    use a, inferInstance
    apply h
    exact hd

theorem State.dHws_iff_dHws_histBlind_both {s} [hs : sys.WF s] : s.dHws ↔
∃ (d : DStrat), d.HistBlind ∧ ∀ (a : AStrat), a.HistBlind → s.dWins ⟨a, d⟩ := by
  constructor
  · intro h
    rw [dHws_iff_dHws_histBlind] at h
    obtain ⟨a, ha, h⟩ := h
    use a, ha
    intro d hd
    apply h
    infer_instance
  · rintro ⟨a, ha, h⟩
    rw [←not_aHws_iff, aHws_iff_aHws_histBlind]
    push_neg
    simp
    intro d hd
    use a, inferInstance
    apply h
    exact hd