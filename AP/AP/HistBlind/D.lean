import AP.AP.HistBlind.A

namespace AP

instance : (default : DStrat).histBlind := by
  simp [DStrat.histBlind]

noncomputable
def State.dwn (s : State) : ℕ :=
  Nat.findRaw # λ n => ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
  (sys.simulate (Strat.f ⟨a, d⟩) s n).2 ≠ 0

theorem State.dwn_eq_zero_of_a_hws {s} [hs : sys.WF s] (h : s.a_hws) : s.dwn = 0 := by
  apply Nat.findRaw_eq_zero_of
  rw [←not_d_hws_iff, d_hws_iff_d_hws_bounded] at h
  push_neg at h ⊢; exact h

@[simp]
theorem State.dwn_histBlind {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).dwn = s.dwn := by
  by_cases h₁ : s.a_hws
  · have h₂ : s.setHist hist |>.a_hws; simpa
    rw [dwn_eq_zero_of_a_hws h₁, dwn_eq_zero_of_a_hws h₂]
  simp at h₁
  have H₁ : s.setHist hist |>.d_hws; simpa
  rw [d_hws_iff_d_hws_bounded] at h₁ H₁
  have ⟨⟨d, hd, h₂⟩, h₃⟩ := Nat.findRaw_spec' h₁
  have ⟨⟨d', hd', H₂⟩, H₃⟩ := Nat.findRaw_spec' H₁
  rw [←dwn] at h₂ h₃ H₂ H₃
  generalize h₄ : s.setHist hist = s' at hs' H₂ H₃ ⊢
  generalize hn : s.dwn = n at h₂ h₃ ⊢
  generalize hn' : s'.dwn = n' at H₂ H₃ ⊢
  clear h₁ H₁
  
  symm; by_contra H'
  wlog H : n < n' with ih
  · specialize @ih s' s.hist hs' d' hd' d hd s (by simp [←h₄])
      hs _ hn' H₂ H₃ _ hn h₂ h₃ (ne_symm' H')
    simp at H ih; exact H' # le_antisymm ih H
  clear H'
  
  rename' d' => d₀
  rename' hd' => hd₀
  
  suffices h : ∃ (d' : DStrat), d'.WF ∧ ∀ (a : AStrat), a.WF →
    (sys.simulate (Strat.f ⟨a, d'⟩) s' n).2 ≠ 0
  · specialize H₃ n h; linarith
  
  sorry

-- #check 0 #exit

theorem State.d_hws_histBlind_of_d_hws {s} [hs : sys.WF s] (h : s.d_hws) :
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ := by
  sorry

-- #check 0 #exit

theorem State.d_hws_iff_d_hws_histBlind {s} [hs : sys.WF s] : s.d_hws ↔
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ :=
  ⟨d_hws_histBlind_of_d_hws, λ ⟨d, Hd, h₁, h₂⟩ => by use d⟩