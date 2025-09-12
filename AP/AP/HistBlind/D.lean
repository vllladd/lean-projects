import AP.AP.HistBlind.A

namespace AP

noncomputable
def State.dwn (s : State) : ℕ :=
  Nat.findRaw # λ n => ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
  (sys.simulate (Strat.f ⟨a, d⟩) s n).2 ≠ 0

theorem State.dwn_eq_zero_of_aHws {s} [hs : sys.WF s] (h : s.aHws) : s.dwn = 0 := by
  apply Nat.findRaw_eq_zero_of
  rw [←not_dHws_iff, dHws_iff_dHws_bounded] at h
  push_neg at h ⊢; exact h

@[simp]
theorem State.dwn_setHist {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).dwn = s.dwn := by
  by_cases h₁ : s.aHws
  · have h₂ : s.setHist hist |>.aHws; simpa
    rw [dwn_eq_zero_of_aHws h₁, dwn_eq_zero_of_aHws h₂]
  simp at h₁
  have H₁ : s.setHist hist |>.dHws; simpa
  rw [dHws_iff_dHws_bounded] at h₁ H₁
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
  generalize hd' : DStrat.mk (λ sd => some # d.f # sd.setHistAt hist s.hist) = d'
  have Hd' : d'.WF; rw [←hd']; infer_instance
  use d', Hd'
  intro a Ha
  generalize ha' : AStrat.mk (λ sa => some # a.f # sa.setHistAt s.hist hist) = a'
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
    · simp [-DState.tr_eq_some_iff, ←hd', H₄, setHistAt, H₈', hs₁.wf] at H₅
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
    exact H₈'.length_le

theorem State.aHws_of_dwn_eq_zero {s} [hs : sys.WF s]
(h : s.dwn = 0) : s.aHws := by
  by_contra h₁
  simp at h₁
  rw [dHws_iff_dHws_bounded] at h₁
  replace h₁ := Nat.findRaw_spec' h₁
  rw [←dwn] at h₁
  simp [h] at h₁
  exact h₁.2 default inferInstance

theorem State.dwn_eq_zero_iff_aHws {s} [hs : sys.WF s] : s.dwn = 0 ↔ s.aHws :=
  ⟨aHws_of_dwn_eq_zero, dwn_eq_zero_of_aHws⟩

theorem State.dHws_iff_dwn_ne_zero {s} [hs : sys.WF s] : s.dHws ↔ s.dwn ≠ 0 := by
  simp [dwn_eq_zero_iff_aHws]

theorem State.dwn_pos_of_dHws {s} [hs : sys.WF s] (h : s.dHws) : 0 < s.dwn := by
  simpa [zero_lt_iff, dwn_eq_zero_iff_aHws]

theorem AState.dwn_lt_of_tr {sa sd p} [hsa : AState sa]
(h₁ : sa.dHws) (h₂ : sys.tr sa p = some sd) : sd.dwn < sa.dwn := by
  have hsd := sys.wf_of_tr h₂
  have h₃ := dHws_of_tr h₂ h₁
  have hp₁ := State.dwn_pos_of_dHws h₁
  rw [State.dHws_iff_dHws_bounded] at h₁ h₃
  replace h₁ := Nat.findRaw_spec' h₁
  replace h₃ := Nat.findRaw_spec' h₃
  rw [←State.dwn] at h₁ h₃
  generalize hn : sa.dwn = n at h₁ h₃ hp₁ ⊢
  generalize hn' : sd.dwn = n' at h₁ h₃ hp₁ ⊢
  obtain ⟨⟨d, Hd, h₁⟩, h₄⟩ := h₁
  replace h₃ := h₃.2
  by_contra! h₅
  specialize h₃ (n - 1) _
  rotate_left; contrapose! h₃; cases n; simp at hp₁; simpa
  clear h₃
  use d, Hd
  intro a Ha
  specialize h₁ (a.set sa p) # a.wf_set_of_tr h₂
  contrapose! h₁
  cases n; simp at hp₁; nm n
  dsimp at h₁
  simp [h₂]
  convert h₁ using 2
  apply simulate_set_a_eq_of_length_hist_lt ⟨_, h₂⟩
  exact State.length_hist_lt_of_tr h₂

theorem DState.exi_tr_dHws_and_dwn_lt {sd} [hsd : DState sd]
(h₁ : sd.dHws) : ∃ p sa, sys.tr sd p = some sa ∧ sa.dHws ∧ sa.dwn < sd.dwn := by
  have hp₁ := State.dwn_pos_of_dHws h₁
  rw [State.dHws_iff_dHws_bounded] at h₁
  replace h₁ := Nat.findRaw_spec' h₁
  rw [←State.dwn] at h₁
  rcases h₁ with ⟨⟨d, Hd, h₁⟩, h₂⟩
  obtain ⟨sa, h₃⟩ := Hd.validTr sd
  use d.f sd, sa, h₃
  generalize hn : sd.dwn = n at h₁ h₂ hp₁ ⊢
  have hsa := AState.of_tr h₃
  have h₄ : sa.dHws
  · use d, Hd
    intro a Ha
    specialize h₁ a Ha
    use n - 1
    cases n; simp at hp₁; nm n
    simp [h₃] at h₁
    exact h₁
  rw [State.dHws_iff_dHws_bounded] at h₄
  replace h₄ := Nat.findRaw_spec' h₄
  rw [←State.dwn] at h₄
  generalize hn' : sa.dwn = n' at h₁ h₂ hp₁ h₄ ⊢
  rcases h₄ with ⟨h₄, h₅⟩
  by_contra! h₆
  specialize h₆ _
  · clear h₆
    cases n; simp at hp₁; nm n
    use d, Hd
    intro a Ha
    specialize h₁ a Ha
    use n
    simp [h₃] at h₁
    exact h₁
  specialize h₅ (n - 1) _
  rotate_left; cases n; simp at hp₁; omega
  clear h₅
  obtain ⟨d', Hd', h₄⟩ := h₄
  use d, Hd
  intro a Ha
  specialize h₁ a Ha
  contrapose! h₁
  cases n; simp at hp₁; nm n
  simpa [h₃]

theorem DState.exi_tr_dwn_lt {sd} [hsd : DState sd]
(h₁ : sd.dHws) : ∃ p sa, sys.tr sd p = some sa ∧ sa.dwn < sd.dwn := by
  have h₂ := hsd.exi_tr_dHws_and_dwn_lt h₁; tauto

open Classical in noncomputable
def dHistBlind : DStrat := .mk # λ s => do
  let sd ← choose? # λ (sd : State) => sys.WF sd ∧ sd.setHist s.hist = s
  choose? # λ p => ∃ sa, sys.tr sd p = some sa ∧ sa.dHws ∧ sa.dwn < sd.dwn

instance : dHistBlind.WF := by unfold dHistBlind; infer_instance

theorem histBlind_dHistBlind : dHistBlind.HistBlind := by
  use inferInstance
  intro s hist hs hs' h₁
  have h₂ : ∃ (sd : State), sys.WF sd ∧ sd.setHist hist = s.setHist hist; use s, hs.wf
  generalize h₃ : Classical.epsilon (λ (sd : State) =>
    sys.WF sd ∧ sd.setHist hist = s.setHist hist) = sd
  have h₄ := Classical.epsilon_spec h₂
  rw [h₃] at h₄
  rcases h₄ with ⟨hsd, h₄⟩
  replace hsd : DState sd
  · use hsd
    apply congrArg (·.setHist sd.hist) at h₄
    simp at h₄
    rw [h₄]
    simp
  have h₅ : ∃ (sd : State), sys.WF sd ∧ sd.setHist s.hist = s; use s, hs.wf; simp
  generalize h₆ : Classical.epsilon (λ (sd : State) =>
    sys.WF sd ∧ sd.setHist s.hist = s) = sd'
  have h₇ := Classical.epsilon_spec h₅
  rw [h₆] at h₇
  rcases h₇ with ⟨hsd', h₇⟩
  replace hsd' : DState sd'
  · use hsd'
    apply congrArg (·.setHist sd'.hist) at h₇
    simp at h₇
    rw [h₇]
    simp
  simp [-DState.tr_eq_some_iff, dHistBlind, choose?_eq_ite, h₃, h₅, h₆]
  have h₇' := setHist_eq_comm.mp h₇
  have H₃ : sd.setHist s.hist = s
  · apply congrArg (·.setHist s.hist) at h₄
    simp at h₄
    exact h₄
  have H₆ : sd.setHist sd'.hist = sd'
  · trans s.setHist sd'.hist
    rotate_left; exact h₇'
    apply congrArg (·.setHist sd'.hist) at h₄
    simp at h₄
    exact h₄
  have H₃' := setHist_eq_comm.mp H₃
  have h₈ : ∀ p, (∃ sa, sys.tr sd p = some sa ∧ sa.dHws ∧ sa.dwn < sd.dwn) ↔
    ∃ sa, sys.tr sd' p = some sa ∧ sa.dHws ∧ sa.dwn < sd'.dwn
  · intro p
    rw [←h₇']
    simp [-DState.tr_eq_some_iff]
    constructor <;> rintro ⟨sa, H₁, H₂, H₂'⟩
    · use sa.setHist # p :: s.hist
      have H₅ : sys.tr sd' p = some (sa.setHist # p :: sd'.hist)
      · rw [←H₆]
        simp [-DState.tr_eq_some_iff]
        use sa
      apply and_of
      · rw [←h₇]
        simp [-DState.tr_eq_some_iff]
        use sa.setHist # p :: sd'.hist, H₅
        rfl
      intro H₄
      simp
      have hsa := AState.of_tr H₁
      have H₇ := sys.wf_of_tr H₅
      have H₈ : sys.WF # s.setHist sd'.hist; simp [h₇', hsd'.wf]
      simp [State.dwn_setHist]
      use H₂
      rw [←H₃]
      have H₉ : sys.WF # sd.setHist s.hist; simp [H₃, hs.wf]
      rwa [State.dwn_setHist]
    · use sa.setHist # p :: sd.hist
      apply and_of
      · rw [←H₃']
        simp [-DState.tr_eq_some_iff]
        use sa.setHist # p :: s.hist
        simp [-DState.tr_eq_some_iff]
        rwa [State.setHist_eq_self_of # hist_eq_of_tr H₁]
      intro H₄
      have hsa := AState.of_tr H₁
      have H₇ := sys.wf_of_tr H₄
      have H₈ : sys.WF # s.setHist sd'.hist; simp [h₇', hsd'.wf]
      simp [State.dwn_setHist]
      simp at H₂'
      have G₁ : sys.WF # sa.setHist # p :: sd'.hist
      · apply sys.wf_of_tr (a := sd') (t := p)
        rw [←H₆]
        simp [-DState.tr_eq_some_iff]
        exact ⟨_, H₄, rfl⟩
      rw [State.dwn_setHist] at H₂'
      simp at H₂; use H₂
      rw [←H₃']
      have G₂ : sys.WF # s.setHist sd.hist
      · simp [H₃', hsd.wf]
      rwa [State.dwn_setHist]
  split_ifs with h₉
  · have H₁ := h₉; simp [-DState.tr_eq_some_iff, ←h₈] at H₁
    simp [-DState.tr_eq_some_iff, H₁]
    simp [-DState.tr_eq_some_iff, h₈]
  · have H₁ := h₉; simp_rw [←h₈] at H₁
    simp [-DState.tr_eq_some_iff, H₁]

@[simp]
instance : dHistBlind.HistBlind := histBlind_dHistBlind

theorem dHws_and_dwn_lt_of_dHistBlind_tr {sd sa} [hsd : DState sd]
(h₁ : sys.tr sd (dHistBlind.f sd) = some sa) (h₂ : sd.dHws) :
sa.dHws ∧ sa.dwn < sd.dwn := by
  simp [-DState.tr_eq_some_iff, dHistBlind, choose?_eq_ite] at h₁
  have h₃ : ∃ (sd' : State), sys.WF sd' ∧ sd'.setHist sd.hist = sd
  · use sd; simp [hsd.wf]
  have h₅ := Classical.epsilon_spec h₃
  generalize h₄ : Classical.epsilon (λ (sd' : State) =>
    sys.WF sd' ∧ sd'.setHist sd.hist = sd) = sd' at h₁ h₅
  rcases h₅ with ⟨hsd', h₅⟩
  have h₅' := setHist_eq_comm.mp h₅
  replace hsd' : DState sd'
  · clear h₁
    use hsd'
    rw [←h₅']
    simp
  have h₆ : ∃ p sa, sys.tr sd' p = some sa ∧ sa.dHws ∧ sa.dwn < sd'.dwn
  · clear h₁
    rw [←h₅] at hsd h₂
    simp at h₂
    exact hsd'.exi_tr_dHws_and_dwn_lt h₂
  have h₇ := Classical.epsilon_spec h₆
  generalize h₈ : Classical.epsilon (λ p => ∃ sa,
    sys.tr sd' p = some sa ∧ sa.dHws ∧ sa.dwn < sd'.dwn) = p at h₁ h₇
  rcases h₇ with ⟨sa', h₇, h₉, H⟩
  have H₁ : sys.tr sd p = sa'.setHist (p :: sd.hist)
  · clear h₁
    rw [←h₅'] at h₇
    simp [-DState.tr_eq_some_iff] at h₇
    obtain ⟨sa', h₇, rfl⟩ := h₇
    simp [-DState.tr_eq_some_iff]
    rwa [State.setHist_eq_self_of]
    exact hist_eq_of_tr h₇
  have H₁' : sys.validTr sd p := ⟨_, H₁⟩
  simp [-DState.tr_eq_some_iff, h₃, h₆, h₈, H₁'] at h₁
  have H₂ : sa.setHist sa'.hist = sa'
  · simp [H₁] at h₁; simp [←h₁]
  have H₃ := AState.of_tr h₁
  have H₄ := AState.of_tr h₇
  have H₄' : AState # sa.setHist sa'.hist; rwa [←H₂] at H₄
  have H₅ : DState # sd.setHist sd'.hist; rwa [h₅']
  constructor
  · rwa [←H₂, State.dHws_setHist_iff] at h₉
  · rw [←H₂, ←h₅'] at H
    simp at H
    exact H

theorem State.dHws_histBlind_of_dHws {s} [hs : sys.WF s] (h : s.dHws) :
∃ (d : DStrat), d.HistBlind ∧ ∀ (a : AStrat), a.WF → s.dWins ⟨a, d⟩ := by
  use dHistBlind, inferInstance
  intro a Ha
  apply dWins_of_lt_lt (p := (·.dHws)) (f := (·.dwn)) h <;> clear! s
  · intro sa sd hsa hsd h₁ h₂
    use hsa.dHws_of_tr h₂ h₁, hsa.dwn_lt_of_tr h₁ h₂
  · intro sd sa hsd hsa h₁ h₂
    exact dHws_and_dwn_lt_of_dHistBlind_tr h₂ h₁

theorem State.dHws_iff_dHws_histBlind {s} [hs : sys.WF s] : s.dHws ↔
∃ (d : DStrat), d.HistBlind ∧ ∀ (a : AStrat), a.WF → s.dWins ⟨a, d⟩ :=
  ⟨dHws_histBlind_of_dHws, λ ⟨d, Hd, h₁⟩ => by use d, Hd.wf⟩