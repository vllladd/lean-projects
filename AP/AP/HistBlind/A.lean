import AP.AP.HistBlind.Basic

namespace AP

open Classical in noncomputable
def aHistBlind : AStrat := .mk # λ s => do
  let s' ← choose? # λ (s' : State) => sys.WF s' ∧ s'.setHist s.hist = s
  let a ← choose? # λ (a : AStrat) => a.WF ∧ ∀ (d : DStrat), d.WF → s'.aWins ⟨a, d⟩
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

def State.setHistAt' (s : State) (hist₁ hist₂ : List PointZ) : State :=
  s.setHist # s.hist.take (s.hist.length - hist₁.length) ++ hist₂

def State.setHistAt (s : State) (hist₁ hist₂ : List PointZ) : State :=
  let s₁ := s.setHistAt' hist₁ hist₂
  if ¬(hist₁ <:+ s.hist ∧ sys.WF s₁) then s else s₁

@[simp]
theorem State.validTr_setHistAt' {s : State} {hist₁ hist₂ p} :
sys.validTr (s.setHistAt' hist₁ hist₂) p ↔ sys.validTr s p := by
  simp [setHistAt']

@[simp]
theorem State.hasTr_setHistAt' {s : State} {hist₁ hist₂} :
sys.hasTr (s.setHistAt' hist₁ hist₂) = sys.hasTr s := by
  simp [setHistAt']

@[simp]
theorem State.validTr_setHistAt {s : State} {hist₁ hist₂ p} :
sys.validTr (s.setHistAt hist₁ hist₂) p ↔ sys.validTr s p := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
theorem State.hasTr_setHistAt {s : State} {hist₁ hist₂} :
sys.hasTr (s.setHistAt hist₁ hist₂) = sys.hasTr s := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
instance {s : State} {hist₁ hist₂} [hs : AState s]
[hs' : sys.WF # s.setHistAt' hist₁ hist₂] : AState # s.setHistAt' hist₁ hist₂ := by
  use inferInstance; simp [State.setHistAt']

@[simp]
instance {s : State} {hist₁ hist₂} [hs : DState s]
[hs' : sys.WF # s.setHistAt' hist₁ hist₂] : DState # s.setHistAt' hist₁ hist₂ := by
  use inferInstance; simp [State.setHistAt']

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
theorem State.setHistAt'_self {s : State} {hist} :
s.setHistAt' s.hist hist = s.setHist hist := by
  simp [setHistAt']

@[simp]
theorem State.setHistAt_self {s : State} {hist} [hs' : sys.WF # s.setHist hist] :
s.setHistAt s.hist hist = s.setHist hist := by
  simp [State.setHistAt, hs']

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

theorem State.wf_setHistAt'_of_reachable {s₀ s : State} {hist} [hs₀ : sys.WF s₀]
[hs₀' : sys.WF # s₀.setHist hist] (h : sys.Reachable s₀ s) :
sys.WF # s.setHistAt' s₀.hist hist :=
  wf_setHist_take_append_of_reachable h

theorem State.wf_setHistAt_of_reachable {s₀ s : State} {hist} [hs₀ : sys.WF s₀]
[hs₀' : sys.WF # s₀.setHist hist] (h : sys.Reachable s₀ s) :
sys.WF # s.setHistAt s₀.hist hist := by
  simp [setHistAt, hist_suffix_of_reachable h, wf_setHistAt'_of_reachable h]

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

theorem State.setHistAt_eq_of_reachable' {s₀ s : State} {hist₀ hist}
[hs₀ : sys.WF s₀] [hs₀' : sys.WF # s₀.setHist hist] (h₀ : hist₀ = s₀.hist)
(h : sys.Reachable s₀ s) : s.setHistAt hist₀ hist = s.setHistAt' hist₀ hist := by
  simp [h₀, setHistAt, hist_suffix_of_reachable h, setHistAt',
    wf_setHist_take_append_of_reachable]

theorem State.setHistAt_eq_of_reachable {s₀ s : State} {hist}
[hs₀ : sys.WF s₀] [hs₀' : sys.WF # s₀.setHist hist] (h : sys.Reachable s₀ s) :
s.setHistAt s₀.hist hist = s.setHistAt' s₀.hist hist :=
  setHistAt_eq_of_reachable' rfl h

def AStrat.setHistAt (a : AStrat) (hist₁ hist₂ : List PointZ) : AStrat where
  f s := a.f # s.setHistAt hist₁ hist₂

def DStrat.setHistAt (d : DStrat) (hist₁ hist₂ : List PointZ) : DStrat where
  f s := d.f # s.setHistAt hist₁ hist₂

instance {a : AStrat} {hist₁ hist₂} [ha : a.WF] : a.setHistAt hist₁ hist₂ |>.WF := by
  unfold AStrat.setHistAt
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
  simpa [State.setHistAt']

instance {d : DStrat} {hist₁ hist₂} [hd : d.WF] : d.setHistAt hist₁ hist₂ |>.WF := by
  unfold DStrat.setHistAt
  have hd' := hd
  rw [DStrat.wf_iff] at hd ⊢
  intro s hs
  specialize @hd s _
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

theorem eq_iff_eq_left_of {α : Type*} {x y z : α} (h : x = y) : x = z ↔ y = z := by
  subst h; rfl

theorem eq_iff_eq_right_of {α : Type*} {x y z : α} (h : x = y) : z = x ↔ z = y := by
  subst h; rfl

@[simp]
theorem State.pw_setHistAt' {s : State} {hist₁ hist₂} :
(s.setHistAt' hist₁ hist₂).pw = s.pw := rfl

@[simp]
theorem State.aTurn_setHistAt' {s : State} {hist₁ hist₂} :
(s.setHistAt' hist₁ hist₂).aTurn = s.aTurn := rfl

@[simp]
theorem State.aPos_setHistAt' {s : State} {hist₁ hist₂} :
(s.setHistAt' hist₁ hist₂).aPos = s.aPos := rfl

@[simp]
theorem State.taken_setHistAt' {s : State} {hist₁ hist₂} :
(s.setHistAt' hist₁ hist₂).taken = s.taken := rfl

@[simp]
theorem State.pw_setHistAt {s : State} {hist₁ hist₂} :
(s.setHistAt hist₁ hist₂).pw = s.pw := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
theorem State.aTurn_setHistAt {s : State} {hist₁ hist₂} :
(s.setHistAt hist₁ hist₂).aTurn = s.aTurn := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
theorem State.aPos_setHistAt {s : State} {hist₁ hist₂} :
(s.setHistAt hist₁ hist₂).aPos = s.aPos := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
theorem State.taken_setHistAt {s : State} {hist₁ hist₂} :
(s.setHistAt hist₁ hist₂).taken = s.taken := by
  simp [setHistAt]; split_ifs <;> simp

@[simp]
theorem State.aMove_setHistAt' {s : State} {hist₁ hist₂ p} :
(s.setHistAt' hist₁ hist₂).aMove p = (s.aMove p).map (·.setHistAt' hist₁ hist₂) := by
  simp [State.aMove]; rfl

@[simp]
theorem State.dMove_setHistAt' {s : State} {hist₁ hist₂ p} :
(s.setHistAt' hist₁ hist₂).dMove p = (s.dMove p).map (·.setHistAt' hist₁ hist₂) := by
  simp [State.dMove]; rfl

theorem State.move_setHistAt' {s : State} {hist₁ hist₂ p}
(h : hist₁.length ≤ s.hist.length) :
(s.setHistAt' hist₁ hist₂).move p = (s.move p).map (·.setHistAt' hist₁ hist₂) := by
  simp [State.move, Option.bind_map]
  split_ifs with ht
  all_goals
    simp [setHistAt']
    congr
    ext s₁ s₂
    simp
    apply eq_iff_eq_left_of
    ext:1 <;> simp
    rw [Nat.succ_sub h]; rfl

theorem State.tr_setHistAt' {s : State} {hist₁ hist₂ p}
(h : hist₁.length ≤ s.hist.length) :
sys.tr (s.setHistAt' hist₁ hist₂) p = (sys.tr s p).map (·.setHistAt' hist₁ hist₂) := by
  simp [sys, move_setHistAt' h]

theorem State.setHistAt'_cancel_of_reachable {s s₁ : State} {hist}
(h : sys.Reachable s s₁) : (s₁.setHistAt' s.hist hist).setHistAt' hist s.hist = s₁ := by
  simp [setHistAt', hist_suffix_of_reachable h]

theorem State.wf_setHistAt'_iff_of_reachable {s s₁ : State} {hist}
[hs : sys.WF s] [hs' : sys.WF # s.setHist hist] (h : sys.Reachable s s₁) :
sys.WF (s₁.setHistAt' s.hist hist) ↔ sys.WF s₁ := by
  symm; use λ _ => wf_setHistAt'_of_reachable h; intro h₁
  suffices h₂ : (s₁.setHistAt' s.hist hist).setHistAt' hist s.hist = s₁
  · rw [←h₂] at h ⊢; exact sys.wf_of_reachable h
  exact setHistAt'_cancel_of_reachable h

theorem AState.setHistAt'_iff_of_reachable {s s₁ : State} {hist}
[hs : sys.WF s] [hs' : sys.WF # s.setHist hist] (h : sys.Reachable s s₁) :
AState (s₁.setHistAt' s.hist hist) ↔ AState s₁ := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact sys.wf_of_reachable h
  · simp at h₂; exact h₂
  · rwa [State.wf_setHistAt'_iff_of_reachable h]
  · exact h₂

theorem DState.setHistAt'_iff_of_reachable {s s₁ : State} {hist}
[hs : sys.WF s] [hs' : sys.WF # s.setHist hist] (h : sys.Reachable s s₁) :
DState (s₁.setHistAt' s.hist hist) ↔ DState s₁ := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact sys.wf_of_reachable h
  · simp at h₂; exact h₂
  · rwa [State.wf_setHistAt'_iff_of_reachable h]
  · exact h₂

theorem State.setHist_reachable_setHistAt'_of_reachable_and_tr {s s₁ s'} {hist p}
(h₁ : sys.Reachable s s') (h₂ : sys.tr s' p = some s₁) :
sys.Reachable (s'.setHistAt' s.hist hist) (s₁.setHistAt' s.hist hist) := by
  apply sys.reachable_of_tr (t := p)
  simp [tr_setHistAt' # length_hist_le_of_reachable h₁]; use s₁

theorem State.setHist_reachable_setHistAt'_of_reachable {s s₁ : State} {hist}
(h : sys.Reachable s s₁) : sys.Reachable (s.setHist hist) (s₁.setHistAt' s.hist hist) := by
  rw [sys.reachable_iff_exi_trs] at h
  obtain ⟨ps, h⟩ := h
  induction ps using List.reverseRecOn generalizing s₁
  · simp at h; simp [h]
  nm ps p ih
  simp at h
  obtain ⟨s', h₁, h₂⟩ := h
  specialize ih h₁
  apply ih.trans; clear ih
  replace h₁ := sys.reachable_of_trs h₁
  exact setHist_reachable_setHistAt'_of_reachable_and_tr h₁ h₂

theorem State.exi_aWins_cnd_setHist_of {s hist} {p : (ℕ → State) → Prop} {a : AStrat}
[hs : sys.WF s] [hs' : sys.WF # s.setHist hist] [ha : a.WF]
(hp : ∀ (st : Strat) [st.WF] hist₁,
p (sys.simulate st.f s · |>.1.setHistAt s.hist hist₁) ↔
p (sys.simulate st.f s · |>.1)) (h : ∀ (d : DStrat) [d.WF],
p (sys.simulate (Strat.f ⟨a, d⟩) s · |>.1) ∧ s.aWins ⟨a, d⟩) :
∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF →
p (sys.simulate (Strat.f ⟨a, d⟩) (s.setHist hist) · |>.1) ∧
(s.setHist hist).aWins ⟨a, d⟩ := by
  use a.setHistAt hist s.hist, inferInstance
  intro d hd
  specialize h # d.setHistAt s.hist hist
  rcases h with ⟨h₁, h₂⟩
  suffices H : ∀ n,
    sys.simulate (Strat.f ⟨a.setHistAt hist s.hist, d⟩) (s.setHist hist) n =
    (sys.simulate (Strat.f ⟨a, d.setHistAt s.hist hist⟩) s n).map
    (·.setHistAt s.hist hist) id
  · use by simpa [H, hp]
    clear h₁
    intro n
    specialize h₂ n
    simpa [H]
  clear! p
  intro n
  specialize h₂ n
  have H := sys.simulate_congr_rel (r := λ s₁ s₂ => s₁.setHistAt s.hist hist = s₂)
    (a₁ := s) (a₂ := s.setHist hist) (f := Strat.f ⟨a, d.setHistAt s.hist hist⟩)
    (g := Strat.f ⟨a.setHistAt hist s.hist, d⟩) (n := n) (by simp)
  specialize H _; rotate_left; obtain ⟨s₁, rfl, H⟩ := H; ext:1 <;> simp_all
  clear H
  dsimp
  rintro k hk s₁ s₁' h₁ h₃ rfl
  use by simp
  intro s₂ s₂' h₄ h₅
  have H₁ := sys.reachable_of_simulate_full h₁
  have H₂ := sys.reachable_of_simulate_full h₃
  have H₃ := length_hist_le_of_reachable H₁
  have H₄ := length_hist_le_of_reachable H₂
  have H₅ := sys.reachable_right H₁ h₄
  rw [setHistAt_eq_of_reachable H₁] at h₅
  simp [tr_setHistAt' H₃] at h₅
  obtain ⟨c, h₅, h₆⟩ := h₅
  rw [setHistAt_eq_of_reachable H₅]
  have hs₁ := sys.wf_of_reachable H₁
  have H₇ : sys.WF # s₁.setHistAt' s.hist hist
  · rwa [wf_setHistAt'_iff_of_reachable H₁]
  have h₇ : (s₁.setHistAt' s.hist hist).setHistAt hist s.hist =
    (s₁.setHistAt' s.hist hist).setHistAt' hist s.hist
  · apply setHistAt_eq_of_reachable' (s₀ := s.setHist hist) (by simp)
    exact setHist_reachable_setHistAt'_of_reachable H₁
  replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  · have H₆ : AState # s₁.setHistAt' s.hist hist
    · rwa [AState.setHistAt'_iff_of_reachable H₁]
    simp at h₄ h₅
    simp [AStrat.setHistAt] at h₅
    rw [h₇, setHistAt'_cancel_of_reachable H₁, h₄] at h₅; clear h₇
    simp at h₅; subst h₅; exact h₆
  · have H₆ : DState # s₁.setHistAt' s.hist hist
    · rwa [DState.setHistAt'_iff_of_reachable H₁]
    simp at h₄ h₅
    simp [DStrat.setHistAt, setHistAt_eq_of_reachable, h₅] at h₄
    subst h₄; exact h₆

theorem State.aHws_setHist_of {s hist} [hs : sys.WF s]
[hs' : sys.WF # s.setHist hist] (h : s.aHws) : (s.setHist hist).aHws := by
  obtain ⟨a, ha, h⟩ := h
  have h₁ := s.exi_aWins_cnd_setHist_of (hist := hist) (p := λ _ => True) (a := a)
  simp only [implies_true, true_and, forall_const] at h₁
  specialize h₁ h; obtain ⟨a', ha', h₁⟩ := h₁; use a'

@[simp]
theorem State.aHws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).aHws ↔ s.aHws := by
  symm; use aHws_setHist_of; rintro h
  suffices h₁ : s.setHist hist |>.setHist s.hist |>.aHws; simpa
  have h₁ : sys.WF # s.setHist hist |>.setHist s.hist; simpa
  exact aHws_setHist_of h

@[simp]
theorem State.dHws_setHist_iff {s hist} [hs : sys.WF s] [hs' : sys.WF # s.setHist hist] :
(s.setHist hist).dHws ↔ s.dHws := by simp only [←not_aHws_iff, aHws_setHist_iff]

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

theorem AState.aHistBlind_tr_aHws {sa} [ha : AState sa]
(h₁ : sa.aHws) : ∃ sd, sys.tr sa (aHistBlind.f sa) = some sd ∧ sd.aHws := by
  have h₂ := sa.hasTr_of_aHws h₁
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
    ∀ (d : DStrat), d.WF → s'.aWins ⟨a, d⟩) = a
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
  simp [aHistBlind, mk_strat_fn,
    choose?_eq_ite, h₃, h₄, h₇, h₈, H₄] at hd
  clear H₄
  rw [←h₆] at hd
  simp at hd
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
∃ (a : AStrat), a.HistBlind ∧ ∀ (d : DStrat), d.WF → s.aWins ⟨a, d⟩ := by
  use aHistBlind, inferInstance
  intro d Hd
  apply aWins_of_ind h
  · intro sa hsa H; apply AState.aHistBlind_tr_aHws
  intro sd hd sa H h₁ h₂
  dsimp at h₂
  rw [DState.aHws_iff_tr] at h₁
  apply h₁; exact h₂

theorem State.aHws_iff_aHws_histBlind {s} [hs : sys.WF s] : s.aHws ↔
∃ (a : AStrat), a.HistBlind ∧ ∀ (d : DStrat), d.WF → s.aWins ⟨a, d⟩ :=
  ⟨aHws_histBlind_of_aHws, λ ⟨a, Ha, h₁⟩ => by use a, Ha.wf⟩