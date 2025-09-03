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
  clear! H' d'
  
  suffices h : ∃ (d' : DStrat), d'.WF ∧ ∀ (a : AStrat), a.WF →
    (sys.simulate (Strat.f ⟨a, d'⟩) s' n).2 ≠ 0
  · specialize H₃ n h; linarith
  
  generalize hd' : DStrat.mk' (λ sd => some # d.f # sd.setHistAt hist s.hist) = d'
  have Hd' : d'.WF; rw [←hd']; infer_instance
  
  use d', Hd'
  intro a Ha
  
  generalize ha' : AStrat.mk' (λ sa => some # a.f # sa.setHistAt s.hist hist) = a'
  have Ha' : a'.WF; rw [←ha']; infer_instance
  specialize h₂ a' Ha'
  
  have h₄' : s'.setHist s.hist = s
  · simp [←h₄]
  
  contrapose! h₂
  apply sys.simulate_congr_rel' (r := λ s₁ s₂ => s₁.setHistAt hist s.hist = s₂) h₂
  · subst h₄; simp
  intro k hk s₁' s₁ s₂ H₁ H₂ H₄ H₅
  have H₄' : s₁.setHistAt s.hist hist = s₁'
  · rw [←H₄]
    sorry
  have hs₁' := sys.wf_of_simulate_eq H₁
  have hs₁ := sys.wf_of_simulate_eq H₂
  dsimp at hs₁' hs₁
  replace hs₁' := s₁'.aState_or_dState
  rcases hs₁' with hs₁' | hs₁'
  · replace hs₁ : AState s₁
    · use hs₁; rw [←H₄]; simp
    simp [-AState.tr_eq_some_iff] at H₅
    use s₁'.setHistAt hist s.hist
    simp [-AState.tr_eq_some_iff, ←ha']
    sorry
  · replace hs₁ : DState s₁
    · use hs₁; rw [←H₄]; simp
    sorry

-- #check 0 #exit

theorem State.d_hws_histBlind_of_d_hws {s} [hs : sys.WF s] (h : s.d_hws) :
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ := by
  sorry

-- #check 0 #exit

theorem State.d_hws_iff_d_hws_histBlind {s} [hs : sys.WF s] : s.d_hws ↔
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ :=
  ⟨d_hws_histBlind_of_d_hws, λ ⟨d, Hd, h₁, h₂⟩ => by use d⟩