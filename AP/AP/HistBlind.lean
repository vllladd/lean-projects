import AP.AP.Determinacy

namespace AP

@[simp]
theorem State.aMove_setHist {s : State} {hist p} :
(s.setHist hist).aMove p = (s.aMove p).map (·.setHist hist) := by
  simp [State.aMove]; rfl

@[simp]
theorem State.dMove_setHist {s : State} {hist p} :
(s.setHist hist).dMove p = (s.dMove p).map (·.setHist hist) := by
  simp [State.dMove]; rfl

@[simp]
theorem State.move_setHist {s : State} {hist p} :
(s.setHist hist).move p = (s.move p).map (·.setHist # p :: hist) := by
  simp [State.move, Option.bind_map]
  split_ifs with ht <;> simp [State.setHist]

@[simp]
theorem State.tr_setHist {s : State} {hist p} :
sys.tr (s.setHist hist) p = (sys.tr s p).map (·.setHist # p :: hist) := by
  simp [sys]

@[simp]
theorem State.validTr_setHist {s : State} {hist} :
sys.validTr (s.setHist hist) = sys.validTr s := by
  ext p; constructor <;> rintro ⟨s₁, h₁⟩
  · simp at h₁; obtain ⟨s', h₁, h₂⟩ := h₁; use s'
  · use s₁.setHist (p :: hist); simp; use s₁

@[simp]
theorem State.hasTr_setHist {s : State} {hist} :
sys.hasTr (s.setHist hist) ↔ sys.hasTr s := by
  apply exists_iff_of; simp

def AStrat.histBlind (a : AStrat) : Prop :=
  ∀ s hist, AState s → sys.WF (s.setHist hist) →
  sys.hasTr s → a.f (s.setHist hist) = a.f s

def DStrat.histBlind (d : DStrat) : Prop :=
  ∀ s hist, DState s → sys.WF (s.setHist hist) →
  sys.hasTr s → d.f (s.setHist hist) = d.f s

@[simp]
theorem State.chooseAMove_setHist {s : State} {hist} :
(s.setHist hist).chooseAMove = s.chooseAMove := by
  simp [chooseAMove]

@[simp]
theorem State.chooseDMove_setHist {s : State} {hist} :
(s.setHist hist).chooseDMove = s.chooseDMove := by
  simp [chooseDMove]

open Classical in noncomputable
def aStratHistBlind : AStrat := .mk' # λ s => do
  let s' ← choose? # λ (s' : State) => sys.WF s' ∧ s'.setHist s.hist = s
  let a ← choose? # λ (a : AStrat) => a.WF ∧ ∀ (d : DStrat), d.WF → s'.a_wins ⟨a, d⟩
  return a.f s'

open Classical in noncomputable
def dStratHistBlind : DStrat := .mk' # λ s => do
  let s' ← choose? # λ (s' : State) => sys.WF s' ∧ s'.setHist s.hist = s
  let d ← choose? # λ (d : DStrat) => d.WF ∧ ∀ (a : AStrat), a.WF → s'.d_wins ⟨a, d⟩
  return d.f s'

instance : aStratHistBlind.WF := by unfold aStratHistBlind; infer_instance
instance : dStratHistBlind.WF := by unfold dStratHistBlind; infer_instance

@[simp] theorem histBlind_aStratHistBlind : aStratHistBlind.histBlind := by
  intro s hist hs hs' h₁; unfold aStratHistBlind
  have h₃ : (λ s' => sys.WF s' ∧ s'.setHist hist = s.setHist hist) =
    (λ s' => sys.WF s' ∧ s'.setHist s.hist = s); simp [State.ext_iff]
  simp [AStrat.mk', Option.pure_def, Option.bind_eq_bind, AStrat.f_mk,
    mk_strat_fn, choose?_eq_ite, h₃]
  split_ifs with h₂ <;> first | (rw [h₃] at h₂; contradiction) | simp

@[simp] theorem histBlind_dStratHistBlind : dStratHistBlind.histBlind := by
  intro s hist hs hs' h₁; unfold dStratHistBlind
  have h₃ : (λ s' => sys.WF s' ∧ s'.setHist hist = s.setHist hist) =
    (λ s' => sys.WF s' ∧ s'.setHist s.hist = s); simp [State.ext_iff]
  simp [DStrat.mk', Option.pure_def, Option.bind_eq_bind, DStrat.f_mk,
    mk_strat_fn, choose?_eq_ite, h₃]
  split_ifs with h₂ <;> first | (rw [h₃] at h₂; contradiction) | simp

theorem setPw_eq_comm {s₁ s₂ : State} :
s₁.setPw s₂.pw = s₂ ↔ s₂.setPw s₁.pw = s₁ := by
  simp [State.ext_iff]; tauto

theorem setHist_eq_comm {s₁ s₂ : State} :
s₁.setHist s₂.hist = s₂ ↔ s₂.setHist s₁.hist = s₁ := by
  simp [State.ext_iff]; tauto

theorem length_hist_eq_of_tr {s s₁ p} (h : sys.tr s p = some s₁) :
s₁.hist.length = s.hist.length + 1 := by simp [hist_eq_of_tr h]

-- #check 0 #exit

theorem length_hist_le_of_reachable {s s₁} [hs : sys.WF s]
(h : sys.Reachable s s₁) : s.hist.length ≤ s₁.hist.length := by
  rw [System.reachable_iff_exi_trs] at h
  obtain ⟨ps, hp⟩ := h
  induction ps generalizing s s₁
  · simp at hp; simp [hp]
  nm p ps ih
  simp at hp
  split at hp; simp at hp
  nm x s₂ h₁; clear x
  have h₂ := System.wf_of_tr h₁
  specialize ih hp; trans s₂.hist.length
  simp [length_hist_eq_of_tr h₁]; exact ih

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

theorem State.a_hws_setHist_of {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist]
(h : s.a_hws) : (s.setHist hist).a_hws := by
  sorry

-- #check 0 #exit

@[simp]
theorem State.a_hws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).a_hws ↔ s.a_hws := by
  symm; use a_hws_setHist_of; rintro h
  suffices h₁ : s.setHist hist |>.setHist s.hist |>.a_hws; simpa
  have h₁ : sys.WF # s.setHist hist |>.setHist s.hist; simpa
  exact a_hws_setHist_of h

@[simp]
theorem State.d_hws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).d_hws ↔ s.d_hws := by simp only [←not_a_hws_iff, a_hws_setHist_iff]

-- #check 0 #exit

theorem State.a_hws_histBlind_of_a_hws {s} [hs : sys.WF s] (h : s.a_hws) :
∃ (a : AStrat), a.WF ∧ a.histBlind ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩ := by
  use aStratHistBlind, inferInstance, by simp
  intro d Hd
  generalize H : Strat.mk aStratHistBlind d = st
  have Hst : st.WF; subst H; infer_instance
  apply a_wins_of_ind h <;> clear! s
  rotate_left
  · sorry
  · intro sa ha h₁
    have h₂ := ha.hasTr_of_a_hws h₁
    obtain ⟨sd, hd⟩ := st.validTr h₂
    rw [AState.start_f_eq] at hd
    use sd, hd
    subst H
    have h₃ : ∃ s', sys.WF s' ∧ s'.setHist sa.hist = sa
    · use sa; simp; infer_instance
    generalize h₄ : Classical.epsilon
      (λ s' => sys.WF s' ∧ s'.setHist sa.hist = sa) = s'
    have h₅ := Classical.epsilon_spec h₃; rw [h₄] at h₅
    rcases h₅ with ⟨h₅, h₆⟩
    have h₆' := setHist_eq_comm.mp h₆
    have H₆ := System.wf_of_tr hd
    have h₇' : sys.WF # sa.setHist s'.hist; rwa [h₆']
    have h₇ : s'.a_hws; rw [←h₆']; simpa
    unfold State.a_hws at h₇
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
      rwa [hasTr_setHist]
    simp [-AState.tr_eq_some_iff, aStratHistBlind, mk_strat_fn,
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
    suffices h : (sd.setHist # a.f s' :: s'.hist).a_hws
    · simp at h ⊢; exact h
    
    obtain ⟨a₁, ha₁, H₄⟩ : s'.a_hws := by use a
    have H₅ : (a₁.set s' # a.f s').WF := AStrat.wf_set_of_tr H₈
    use a₁, inferInstance
    intro d₁ hd₁ n
    specialize H₄ d₁ hd₁ (n + 1)
    simp at H₄
    split at H₄; simp at H₄
    nm x s₃ H₇; clear x
    convert H₄
    
    sorry
    
    -- have H₄ : sd.setHist (a.f s' :: sa.hist) = sd; simp [hist_eq_of_tr hd]
    -- have H₈ : sys.WF # sd.setHist # a.f s' :: s'.hist
    -- · clear H₄; rw [←h₆] at hd
    --   simp [-AState.tr_eq_some_iff] at hd
    --   rcases hd with ⟨s₂, H₈, rfl⟩
    --   simp
    --   have H₄ := System.wf_of_tr H₈
    --   convert H₄
    --   simp
    --   exact hist_eq_of_tr H₈
    -- suffices h : (sd.setHist # a.f s' :: s'.hist).a_hws; simp at h; exact h
    -- 
    -- -- rw [ha.a_hws_iff_tr] at h₁
    -- 
    -- replace h₁ : s'.a_hws; rw [←h₆']; simpa
    -- rcases h₁ with ⟨a₁, ha₁, h₁⟩
    -- have H₅ : (a₁.set s' # a.f s').WF
    -- · rw [←h₆] at hd
    --   simp [-AState.tr_eq_some_iff] at hd
    --   rcases hd with ⟨p₂, H₆, H₇⟩
    --   exact a₁.wf_set_of_tr H₆
    -- use a₁.set s' (a.f s'), H₅
    -- intro d₁ hd₁ n
    -- specialize h₁ d₁ hd₁ # n + 1
    -- simp at h₁
    -- split at h₁; simp at h₁
    -- nm x s₂ H₇; clear x
    -- rw [simulate_set_a_eq_of_length_hist_lt]
    -- rotate_left
    -- · rw [←h₆']
    --   simp
    --   rw [h₆']
    --   exact System.validTr_of_eq_some hd
    -- · simp
    -- clear H₄
    -- 
    -- convert h₁
    -- have H₉ := System.wf_of_tr H₇
    -- 
    -- rw [←h₆] at hd
    -- simp [-AState.tr_eq_some_iff] at hd
    -- rcases hd with ⟨p₂, A₁, rfl⟩
    -- simp at H₈
    -- 
    -- ext:1 <;> simp
    -- · rw [pw_eq_of_tr A₁, pw_eq_of_tr H₇]
    -- · 