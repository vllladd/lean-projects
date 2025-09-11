import AP.AP.HistBlind.Basic

namespace AP

open Classical in noncomputable
def aHistBlind : AStrat := .mk # λ s => do
  let s' ← choose? # λ (s' : State) => sys.WF s' ∧ s'.setHist s.hist = s
  let a ← choose? # λ (a : AStrat) => a.WF ∧ ∀ (d : DStrat), d.WF → s'.a_wins ⟨a, d⟩
  return a.f s'

instance : aHistBlind.WF := by unfold aHistBlind; infer_instance

theorem histBlind_aHistBlind : aHistBlind.HistBlind := by
  use inferInstance; intro s hist hs hs' h₁; unfold aHistBlind
  have h₃ : (λ s' => sys.WF s' ∧ s'.setHist hist = s.setHist hist) =
    (λ s' => sys.WF s' ∧ s'.setHist s.hist = s); simp [State.ext_iff]
  simp [AStrat.mk, Option.pure_def, Option.bind_eq_bind, AStrat.f_mk,
    mk_strat_fn, choose?_eq_ite, h₃]
  split_ifs with h₂ <;> first | (rw [h₃] at h₂; contradiction) | simp

@[simp]
instance : aHistBlind.HistBlind := histBlind_aHistBlind

theorem simulate_set_a_eq_of_length_hist_lt {s s₁ p₁ n} {a : AStrat} {d : DStrat} 
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : s₁.hist.length < s.hist.length) :
sys.simulate (Strat.mk (a.set s₁ p₁) d).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ : (a.set s₁ p₁).WF := a.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  exact length_hist_le_of_reachable # System.reachable_of_simulate_full h₅

theorem simulate_set_d_eq_of_length_hist_lt {s s₁ p₁ n} {a : AStrat} {d : DStrat} 
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : s₁.hist.length < s.hist.length) :
sys.simulate (Strat.mk a (d.set s₁ p₁)).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ : (d.set s₁ p₁).WF := d.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  exact length_hist_le_of_reachable # System.reachable_of_simulate_full h₅

def State.setHistAt' (s : State) (hist₁ hist₂ : List PointZ) : State :=
  s.setHist # s.hist.take (s.hist.length - hist₁.length) ++ hist₂

def State.setHistAt (s : State) (hist₁ hist₂ : List PointZ) : State :=
  let s₁ := s.setHistAt' hist₁ hist₂
  if ¬(hist₁ <:+ s.hist ∧ sys.WF s₁) then s else s₁

@[simp]
instance {s : State} {hist₁ hist₂} [hs : AState s]
[hs' : sys.WF # s.setHistAt' hist₁ hist₂] : AState # s.setHistAt' hist₁ hist₂ := by
  use inferInstance; simp [State.setHistAt']

@[simp]
instance {s : State} {hist₁ hist₂} [hs : DState s]
[hs' : sys.WF # s.setHistAt' hist₁ hist₂] : DState # s.setHistAt' hist₁ hist₂ := by
  use inferInstance; simp [State.setHistAt']

instance {a : AStrat} {hist₁ hist₂} [ha : a.WF] :
AStrat.WF # .mk' # λ s => a.f # s.setHistAt hist₁ hist₂ := by
  have ha' := ha
  rw [AStrat.wf_iff] at ha ⊢
  intro s hs h₁
  specialize ha h₁
  dsimp
  generalize hs' : s.setHistAt hist₁ hist₂ = s'
  simp [State.setHistAt] at hs'
  split_ifs at hs' with h₂; subst hs'; exact ha
  simp at h₂; rcases h₂ with ⟨H, h₂⟩
  suffices h₄ : sys.validTr s' # a.f s'
  · subst hs'
    nth_rw 1 [State.setHistAt'] at h₄
    simp at h₄
    exact h₄
  subst hs'
  apply ha'.validTr
  simpa [State.setHistAt', -AState.hasTr_iff]

instance {d : DStrat} {hist₁ hist₂} [hd : d.WF] :
DStrat.WF # .mk' # λ s => d.f # s.setHistAt hist₁ hist₂ := by
  have hd' := hd
  rw [DStrat.wf_iff] at hd ⊢
  intro s hs h₁
  specialize hd h₁
  dsimp
  generalize hs' : s.setHistAt hist₁ hist₂ = s'
  simp [State.setHistAt] at hs'
  split_ifs at hs' with h₂; subst hs'; exact hd
  simp at h₂; rcases h₂ with ⟨H, h₂⟩
  suffices h₄ : sys.validTr s' # d.f s'
  · subst hs'
    nth_rw 1 [State.setHistAt'] at h₄
    simp at h₄
    exact h₄
  subst hs'
  exact hd'.validTr _

@[simp]
instance {s hist₁ hist₂} [hs : sys.WF s] : sys.WF # s.setHistAt hist₁ hist₂ := by
  simp [State.setHistAt]; split_ifs with h; exact hs; simp at h; exact h.2

@[simp]
instance {s hist₁ hist₂} [hs : AState s] : AState # s.setHistAt hist₁ hist₂ := by
  simp [State.setHistAt]; split_ifs with h₁; exact hs; simp at h₁; simp [h₁]

@[simp]
instance {s hist₁ hist₂} [hs : DState s] : DState # s.setHistAt hist₁ hist₂ := by
  simp [State.setHistAt]; split_ifs with h₁; exact hs
  simp at h₁; rcases h₁ with ⟨h₁, h₂⟩; infer_instance

@[simp]
theorem State.setHistAt_self {s : State} {hist} [hs' : sys.WF # s.setHist hist] :
s.setHistAt s.hist hist = s.setHist hist := by
  simp [State.setHistAt, State.setHistAt', hs']

theorem State.wf_setHist_take_append_of_reachable {s₀ s : State} {hist} [hs₀ : sys.WF s₀]
[hs₀' : sys.WF # s₀.setHist hist] (h : sys.Reachable s₀ s) :
sys.WF # s.setHist # s.hist.take (s.hist.length - s₀.hist.length) ++ hist := by
  rw [System.reachable_iff_exi_trs] at h
  obtain ⟨ps, h⟩ := h
  rename' s => s₂
  generalize hs₁ : s₀ = s₁
  replace hs₀' : sys.WF # s₁.setHist # s₁.hist.take
    (s₁.hist.length - s₀.hist.length) ++ hist
  · subst hs₁; simpa
  rw [hs₁] at h
  simp only [←hs₁]
  have hx : sys.WF s₁; rwa [←hs₁]
  have hr : sys.Reachable s₀ s₁; subst hs₁; rfl
  clear hs₁
  induction ps generalizing s₁
  · simp at h
    subst h
    simpa
  nm p ps ih
  simp at h
  split at h; simp at h
  nm x s' h₁; clear x
  have h₂ := System.wf_of_tr h₁
  have h₃ : sys.tr (s₁.setHist # s₁.hist.take (s₁.hist.length - s₀.hist.length) ++ hist)
    p = some (s'.setHist # s'.hist.take (s'.hist.length - s₀.hist.length) ++ hist)
  · simp
    use s', h₁
    congr
    simp [hist_eq_of_tr h₁]
    rw [Nat.succ_sub # length_hist_le_of_reachable hr]
    simp
  exact ih s' h (System.wf_of_tr h₃) h₂ (System.reachable_right hr h₁)

theorem State.setHistAt_cancel_of_reachable {s₀ s : State} {hist}
[hs₀ : sys.WF s₀] [hs₀' : sys.WF # s₀.setHist hist] (h : sys.Reachable s₀ s) :
(s.setHistAt s₀.hist hist).setHistAt hist s₀.hist = s := by
  unfold setHistAt setHistAt'
  dsimp
  split_ifs with h₁ h₂ h₂ <;> simp_all
  · rcases h₁ with ⟨h₁, h₃⟩
    exfalso
    simp [List.take_length_sub_append_eq_of_suffix h₁] at h₂
    apply h₂
    exact System.wf_of_reachable h
  exfalso
  rcases h₂ with ⟨h₂, h₃⟩
  have h₄ := hist_suffix_of_reachable h
  specialize h₁ h₄
  apply h₁
  exact wf_setHist_take_append_of_reachable h

theorem State.aHws_setHist_of_aHws {s hist} [hs : sys.WF s]
[hs' : sys.WF # s.setHist hist] (h : s.aHws) : (s.setHist hist).aHws := by
  rename' s => s₀, hs => hs₀, hs' => hs₀'
  rcases h with ⟨a, ha, h⟩
  use .mk' # λ s => a.f # s.setHistAt hist s₀.hist, inferInstance
  intro d hd n
  specialize h ⟨λ s => d.f # s.setHistAt s₀.hist hist⟩ inferInstance n
  apply System.simulate_congr_rel' h (r := λ s₁ s₂ => s₁.setHistAt s₀.hist hist = s₂)
  · simp
  intro k hk b₁ b₂ c₁ hb₁ hb₂ h₁ h₂
  use c₁.setHistAt s₀.hist hist
  simp
  have H₁ := System.wf_of_simulate_eq hb₁
  have H₂ := System.wf_of_simulate_eq hb₂
  dsimp at H₁ H₂
  replace H₁ := b₁.aState_or_dState
  rcases H₁ with H₁ | H₁
  · replace H₂ : AState b₂; simp [←h₁]
    simp [-AState.tr_eq_some_iff] at h₂ ⊢
    nth_rw 2 [←h₁]
    rw [setHistAt_cancel_of_reachable]
    rotate_left; exact System.reachable_of_simulate_full hb₁
    rw [←h₁]
    dsimp [setHistAt, setHistAt']
    split_ifs with h₃ h₄ h₄
    · simp [-AState.tr_eq_some_iff]
      use c₁, h₂
      simp [hist_eq_of_tr h₂]
      rw [Nat.succ_sub]
      rotate_left
      · apply length_hist_le_of_reachable
        exact System.reachable_of_simulate_full hb₁
      simp
    · simp at h₄
      specialize h₄ # h₃.1.trans # hist_suffix_of_tr h₂
      exfalso
      apply h₄
      apply wf_setHist_take_append_of_reachable
      trans b₁
      · exact System.reachable_of_simulate_full hb₁
      · exact System.reachable_of_tr h₂
    · simp at h₃
      specialize h₃ _
      · apply hist_suffix_of_reachable
        exact System.reachable_of_simulate_full hb₁
      exfalso
      apply h₃
      apply wf_setHist_take_append_of_reachable
      exact System.reachable_of_simulate_full hb₁
    · exact h₂
  · replace H₂ : DState b₂; simp [←h₁]
    simp [-DState.tr_eq_some_iff] at h₂ ⊢
    rw [h₁] at h₂
    nth_rw 1 [←h₁]
    dsimp [setHistAt, setHistAt']
    split_ifs with h₃ h₄ h₄
    · simp [-DState.tr_eq_some_iff]
      use c₁, h₂
      simp [hist_eq_of_tr h₂]
      rw [Nat.succ_sub]
      rotate_left
      · apply length_hist_le_of_reachable
        exact System.reachable_of_simulate_full hb₁
      simp
    · simp at h₄
      specialize h₄ # h₃.1.trans # hist_suffix_of_tr h₂
      exfalso
      apply h₄
      apply wf_setHist_take_append_of_reachable
      trans b₁
      · exact System.reachable_of_simulate_full hb₁
      · exact System.reachable_of_tr h₂
    · simp at h₃
      specialize h₃ _
      · apply hist_suffix_of_reachable
        exact System.reachable_of_simulate_full hb₁
      exfalso
      apply h₃
      apply wf_setHist_take_append_of_reachable
      exact System.reachable_of_simulate_full hb₁
    · exact h₂

@[simp]
theorem State.aHws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).aHws ↔ s.aHws := by
  symm; use aHws_setHist_of_aHws; rintro h
  suffices h₁ : s.setHist hist |>.setHist s.hist |>.aHws; simpa
  have h₁ : sys.WF # s.setHist hist |>.setHist s.hist; simpa
  exact aHws_setHist_of_aHws h

@[simp]
theorem State.dHws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).dHws ↔ s.dHws := by simp only [←not_aHws_iff, aHws_setHist_iff]

theorem AState.aHistBlind_tr_aHws {sa} [ha : AState sa]
(h₁ : sa.aHws) : ∃ sd, sys.tr sa (aHistBlind.f sa) = some sd ∧ sd.aHws := by
  have h₂ := ha.hasTr_of_aHws h₁
  obtain ⟨sd, hd⟩ := aHistBlind.validTr h₂
  use sd, hd
  have h₃ : ∃ s', sys.WF s' ∧ s'.setHist sa.hist = sa
  · use sa; simp
  generalize h₄ : Classical.epsilon
    (λ s' => sys.WF s' ∧ s'.setHist sa.hist = sa) = s'
  have h₅ := Classical.epsilon_spec h₃; rw [h₄] at h₅
  rcases h₅ with ⟨h₅, h₆⟩
  have h₆' := setHist_eq_comm.mp h₆
  have H₆ := System.wf_of_tr hd
  have h₇' : sys.WF # sa.setHist s'.hist; rwa [h₆']
  have h₇ : s'.aHws; rw [←h₆']; simpa
  unfold State.aHws at h₇
  generalize h₈ : Classical.epsilon (λ (a : AStrat) => a.WF ∧
    ∀ (d : DStrat), d.WF → s'.a_wins ⟨a, d⟩) = a
  have h₉ := Classical.epsilon_spec h₇
  rw [h₈] at h₉
  rcases h₉ with ⟨H₁, H₂⟩
  have H₃ : AState s'; use h₅; rw [←h₆']; simp
  have H₄ : sys.validTr sa (a.f s')
  · rw [←h₆]
    simp
    apply a.validTr
    rw [←h₆']
    rwa [State.hasTr_setHist]
  simp [-AState.tr_eq_some_iff, aHistBlind, mk_strat_fn,
    choose?_eq_ite, h₃, h₄, h₇, h₈, H₄] at hd
  clear H₄
  rw [←h₆] at hd
  simp [-AState.tr_eq_some_iff] at hd
  rcases hd with ⟨sd, H₈, rfl⟩
  have h₉ := DState.of_tr H₈
  have h' : sys.WF # sd.setHist # a.f s' :: s'.hist
  · replace h₉ : sys.WF sd := inferInstance
    convert h₉
    simp
    exact hist_eq_of_tr H₈
  suffices h : (sd.setHist # a.f s' :: s'.hist).aHws
  · simp at h ⊢; exact h
  use a, inferInstance
  intro d hd n
  specialize H₂ d hd (n + 1)
  simp [H₈] at H₂
  convert H₂
  simp
  exact hist_eq_of_tr H₈

theorem State.aHws_histBlind_of_aHws {s} [hs : sys.WF s] (h : s.aHws) :
∃ (a : AStrat), a.HistBlind ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩ := by
  use aHistBlind, inferInstance
  intro d Hd
  apply a_wins_of_ind h <;> clear! s
  · exact @AState.aHistBlind_tr_aHws
  intro sd hd sa h₁ h₂
  dsimp at h₂
  rw [DState.aHws_iff_tr] at h₁
  apply h₁; exact h₂

theorem State.aHws_iff_aHws_histBlind {s} [hs : sys.WF s] : s.aHws ↔
∃ (a : AStrat), a.HistBlind ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩ :=
  ⟨aHws_histBlind_of_aHws, λ ⟨a, Ha, h₁⟩ => by use a, Ha.wf⟩

@[simp]
theorem State.setHistAt_setHist {s : State} {hist₁ hist₂} [hs : sys.WF # s.setHist hist₂] :
(s.setHist hist₁).setHistAt hist₁ hist₂ = s.setHist hist₂ := by
  simp [setHistAt, setHistAt', hs]

instance {s} [hs : sys.WF s] : sys.WF (s.setHist s.hist) := by simpa

theorem State.setHistAt_cancel_of_suffix {s : State} {hist₁ hist₂}
[hs : sys.WF s] [hs' : sys.WF # s.setHistAt' hist₁ hist₂]
(h : hist₁ <:+ s.hist) : (s.setHistAt hist₁ hist₂).setHistAt hist₂ hist₁ = s := by
  simp [setHistAt, setHistAt'] at hs' ⊢
  split_ifs at hs ⊢ with h₁ h₂ h₂ <;> simp [h] at h₁ h₂ ⊢
  · rcases h₂ with ⟨h₂, h₃⟩; contradiction
  · simp [List.take_length_sub_append_eq_of_suffix h, hs] at h₂