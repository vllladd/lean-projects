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
theorem State.dwn_setHist {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
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
  intro k hk s₁' s₁ s₂' H₁ H₂ H₄ H₅
  have H₆ : sys.WF # s₁'.setHistAt' hist s.hist
  · by_contra H₆
    simp [setHistAt, H₆] at H₄
    subst H₄
    simp [setHistAt'] at H₆
    apply H₆; clear H₆
    have H₆ := @wf_setHist_take_append_of_reachable s' s₁' s.hist hs'
      (by simpa [h₄']) (by exact System.reachable_of_simulate_full H₁)
    simp [←h₄] at H₆
    exact H₆
  have H₇ := sys.wf_of_simulate_eq H₁; dsimp at H₇
  have G₃ : hist = s'.hist; simp [←h₄]
  subst G₃
  have H₈' := hist_suffix_of_reachable # System.reachable_of_simulate_full H₁
  have H₈ := hist_suffix_of_reachable # System.reachable_of_simulate_full H₂
  have H₉ := H₈'.trans # hist_suffix_of_tr H₅
  have H₄' : s₁.setHistAt s.hist s'.hist = s₁'
  · rw [←H₄]; exact setHistAt_cancel_of_suffix H₈'
  have hs₁' := sys.wf_of_simulate_eq H₁
  have hs₁ := sys.wf_of_simulate_eq H₂
  dsimp at hs₁' hs₁
  have G₃ : sys.WF # s'.setHist s.hist; simpa [h₄']
  have G₂ : sys.WF # s₂'.setHistAt' s'.hist s.hist
  · rw [setHistAt']
    apply wf_setHist_take_append_of_reachable
    trans s₁'
    · exact System.reachable_of_simulate_full H₁
    · exact System.reachable_of_tr H₅
  replace hs₁' := s₁'.aState_or_dState
  rcases hs₁' with hs₁' | hs₁'
  · replace hs₁ : AState s₁
    · use hs₁; rw [←H₄]; simp
    simp [-AState.tr_eq_some_iff] at H₅
    use s₂'.setHistAt s'.hist s.hist
    simp [-AState.tr_eq_some_iff, ←ha', H₄', guard]
    simp [setHistAt, H₆, H₈'] at H₄
    have G₁ : sys.tr s₁ (a.f s₁') = some (s₂'.setHistAt' s'.hist s.hist)
    · simp [-AState.tr_eq_some_iff, ←H₄, setHistAt']
      use s₂', H₅
      simp [hist_eq_of_tr H₅]
      rw [Nat.succ_sub]
      simp
      exact List.IsSuffix.length_le H₈'
    have G₁' : sys.validTr s₁ # a.f s₁' := ⟨_, G₁⟩
    simp [-AState.tr_eq_some_iff, G₁']
    rw [←H₄]
    simp [-AState.tr_eq_some_iff, setHistAt, H₄, H₉, G₂]
    simp [-AState.tr_eq_some_iff, ←H₄, setHistAt']
    use s₂', H₅
    simp [hist_eq_of_tr H₅]
    rw [Nat.succ_sub]
    simp; exact H₈'.length_le
  · replace hs₁ : DState s₁
    · use hs₁; rw [←H₄]; simp
    simp [-DState.tr_eq_some_iff] at H₅
    use s₂'.setHistAt s'.hist s.hist
    simp [-DState.tr_eq_some_iff]
    have G₄ : sys.WF # s.setHist s'.hist; simpa [h₄]
    have H₆' : sys.WF # s₁.setHistAt' s.hist s'.hist
    · unfold setHistAt'
      apply wf_setHist_take_append_of_reachable
      exact System.reachable_of_simulate_full H₂
    simp [setHistAt, H₆, H₆', H₈, H₈'] at H₄ H₄'
    have G₁ : sys.tr s₁' (d.f s₁) = some s₂'
    · simp [-DState.tr_eq_some_iff, ←hd', H₄, setHistAt, H₈', hs₁.wf_s] at H₅
      replace H₅ : sys.tr s₁' (((guard (f := Option)
        (sys.validTr (s₁.setHistAt' s.hist s'.hist) (d.f s₁))).bind #
        λ x => some (d.f s₁)).getD s₁'.chooseDMove) = some s₂'
      · simp [←H₄'] at H₅ ⊢; exact H₅
      simp [-DState.tr_eq_some_iff, setHistAt'] at H₅
      exact H₅
    have G₁' : sys.validTr s₁' # d.f s₁ := ⟨_, G₁⟩
    have G₄ : sys.WF # s₂'.setHistAt' s'.hist s.hist
    · unfold setHistAt'
      apply wf_setHist_take_append_of_reachable
      trans s₁'
      · exact System.reachable_of_simulate_full H₁
      · exact System.reachable_of_tr H₅
    nth_rw 1 [←H₄]
    simp [-DState.tr_eq_some_iff, setHistAt']
    use s₂', G₁
    simp [setHistAt, H₉, G₄]
    simp [setHistAt', hist_eq_of_tr G₁]
    rw [Nat.succ_sub]
    simp
    exact List.IsSuffix.length_le H₈'

-- #check 0 #exit

theorem State.d_hws_histBlind_of_d_hws {s} [hs : sys.WF s] (h : s.d_hws) :
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ := by
  sorry

-- #check 0 #exit

theorem State.d_hws_iff_d_hws_histBlind {s} [hs : sys.WF s] : s.d_hws ↔
∃ (d : DStrat), d.WF ∧ d.histBlind ∧ ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩ :=
  ⟨d_hws_histBlind_of_d_hws, λ ⟨d, Hd, h₁, h₂⟩ => by use d⟩