import AP.AP.Basic

namespace AP

theorem State.not_a_hws_of_d_hws {s : State} (h : s.d_hws) : ¬s.a_hws := by
  obtain ⟨d, hd, h⟩ := h
  simp [a_hws]
  intro a ha
  use d, hd
  exact h a ha

theorem AState.of_simulate_mul_two {sa} [ha : AState sa]
{st : Strat} [hst : st.WF] {n} : AState (sys.simulate st.f sa # n * 2).1 := by
  induction n generalizing sa; exact ha
  nm n ih
  simp [Nat.succ_mul]
  split; exact ha
  nm x sd h₁; clear x
  have hd := DState.of_tr h₁
  split; nm x h₂; simp at h₂
  nm x sa' h₂; clear x
  have ha' := AState.of_tr h₂
  exact ih

instance {sa} [ha : AState sa] {st : Strat} [hst : st.WF] {n} :
AState (sys.simulate st.f sa # n * 2).1 := ha.of_simulate_mul_two

theorem AState.a_wins_of_ind_two {sa} [ha : AState sa]
{st : Strat} [hst : st.WF] {p : State → Prop} (hp : p sa)
(h : ∀ {sa} [AState sa], p sa → ∃ sd, sys.tr sa (st.a.f sa) = some sd ∧
∀ sa', sys.tr sd (st.d.f sd) = some sa' → p sa') :
sa.a_wins st := by
  rw [sa.a_wins_iff_mul_two]
  intro n
  suffices h₁ : ∃ b, sys.simulate st.f sa (n * 2) = (b, 0) ∧ p b
  · obtain ⟨b, h₁, h₂⟩ := h₁; simp [h₁]
  induction n
  · use sa; simpa
  nm n ih
  clear hp
  rename' sa => sa₀, ha => ha₀
  obtain ⟨sa, ih, hp⟩ := ih
  simp only [Nat.succ_mul, System.simulate_add]
  have ha : AState sa
  · replace ih := congrArg (·.1) ih; subst ih; infer_instance
  simp [ih]
  specialize h hp
  obtain ⟨sd, h₁, h₂⟩ := h
  simp [h₁]
  have hd := DState.of_tr h₁
  obtain ⟨sa', h₃⟩ := hst.wf_d.1 hd.hasTr hd.turn
  simp [h₃]
  exact h₂ _ h₃

theorem AState.ind_two {sa sa'} [ha : AState sa] [ha' : AState sa']
{p : State → Prop} (h₁ : p sa) (h₂ : ∀ sa [AState sa] pa sd pd sa',
sys.tr sa pa = some sd → sys.tr sd pd = some sa' → p sa')
(h₃ : sys.Reachable sa sa') : p sa' := by
  replace h₃ := System.exi_trs_of_reachable h₃
  obtain ⟨ts, h₃⟩ := h₃
  generalize hn : ts.length = n
  induction n using Nat.strong_induction_on generalizing ts sa
  nm n ih
  cases ts; simp at h₃; simpa [←h₃]; nm pa ts
  simp at h₃; split at h₃; simp at h₃
  nm x sd h₄; clear x
  have hd := DState.of_tr h₄
  cases ts; simp at h₃; simp [h₃] at hd; nm pd ts
  simp at h₃; split at h₃; simp at h₃
  nm x sa₁ h₅; clear x
  simp [add_assoc] at hn; subst hn
  have ha₁ := AState.of_tr h₅
  exact @ih ts.length (by simp) sa₁ _
    (h₂ sa pa sd pd sa₁ h₄ h₅) ts h₃ rfl

def aStratChooseCnd (p : State → Prop) (sa : State) (pa : PointZ) : Prop :=
  ∃ sd, sys.tr sa pa = some sd ∧ ∀ pd sa', sys.tr sd pd = some sa' → p sa'

open Classical in noncomputable
def aStratChoose (p : State → Prop) : AStrat :=
  .mk' # λ sa => choose? # aStratChooseCnd p sa

theorem wf_aStratChoose {p} : (aStratChoose p).WF := by
  unfold aStratChoose; infer_instance

instance {p} : (aStratChoose p).WF := wf_aStratChoose

theorem AState.a_hws_of_ind_two {sa : State} [ha : AState sa] {p : State → Prop}
(h₁ : p sa) (h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧
∀ pd sa', sys.tr sd pd = some sa' → p sa') : sa.a_hws := by
  classical
  use aStratChoose p, inferInstance
  intro d hd
  apply ha.a_wins_of_ind_two h₁
  clear! sa
  intro sa ha hp
  specialize h₂ sa hp
  simp only [aStratChoose, choose?_eq_ite]
  replace h₂ : ∃ pa, aStratChooseCnd p sa pa := h₂
  have h₃ := Classical.epsilon_spec h₂
  generalize h₁ : Classical.epsilon (aStratChooseCnd p sa) = pa at h₃ ⊢
  unfold aStratChooseCnd at h₃
  obtain ⟨sd, h₃, h₄⟩ := h₃; use sd
  simp [-tr_eq_some_iff, mk_strat_fn, h₂, h₁,
    System.validTr_iff_isSome, h₃]; apply h₄

instance {s} [hs : sys.WF s] : sys.Tree s := by
  rw [System.tree_iff_full_trs]
  use hs; intro ts₁ ts₂ s' h₁ h₂
  have h₃ := congrArg (·.1.hist) h₁
  have h₄ := congrArg (·.1.hist) h₂
  simp at h₃ h₄
  simp [h₂] at h₄
  simp [h₁, ←h₄] at h₃
  exact h₃

@[simp]
def getMoveFromHist (s_target s : State) : List PointZ → Option PointZ
| [] => none
| p :: ps => if s = s_target then some p else do
  let s' ← sys.tr s p
  getMoveFromHist s_target s' ps

def State.getMoveAt (s s_target : State) : Option PointZ :=
  getMoveFromHist s_target (initState s.pw) s.hist.reverse

theorem getMoveFromHist_append_eq_some_of {s acc ps ps₁ p}
(h : getMoveFromHist s acc ps = some p) :
getMoveFromHist s acc (ps ++ ps₁) = some p := by
  induction ps generalizing acc; simp at h
  nm p₁ ps ih
  simp at h ⊢
  split_ifs at h ⊢ with h₁; exact h
  simp at h ⊢
  obtain ⟨s', h₂, h₃⟩ := h
  use s', h₂
  exact ih h₃

theorem getMoveAt_eq_getMoveAt_eq_some_and_tr {s₁ s₂ p₁ s p}
(h₁ : s₁.getMoveAt s = some p) (h₂ : sys.tr s₁ p₁  = some s₂) :
s₂.getMoveAt s = some p := by
  unfold State.getMoveAt at h₁ ⊢
  simp [pw_eq_of_tr h₂, hist_eq_of_tr h₂]
  generalize initState s₁.pw = acc at h₁ ⊢
  generalize s₁.hist.reverse = ps at h₁ ⊢
  generalize [p₁] = ps₁
  exact getMoveFromHist_append_eq_some_of h₁

theorem getMoveFromHist_eq_some_iff_exi_trs {s acc p ps} [hs : sys.WF acc] :
getMoveFromHist s acc ps = some p ↔ sys.WF s ∧
∃ ps', ps' ++ [p] <+: ps ∧ sys.trs acc ps' = (s, []) := by
  induction ps generalizing acc; simp
  nm p₁ ps ih
  simp
  generalize hb : sys.tr acc p₁ = r
  split_ifs with h₁
  · subst h₁; simp [hs]; rw [eq_comm]
  rcases r with _ | b <;> simp
  · intro h₂ ps' h₃
    cases ps'; simpa
    nm p₂ ps'
    simp at h₃
    rcases h₃ with ⟨rfl, h₃⟩
    simp [hb]
  have h₂ := System.wf_of_tr hb
  rw [ih]; clear ih
  constructor
  · rintro ⟨h₃, ps', h₄, h₅⟩
    use h₃, p₁ :: ps'
    simpa [h₄, hb]
  rintro ⟨h₃, ps', h₄, h₅⟩
  use h₃
  cases ps'
  · simp at h₅; contradiction
  nm p₂ ps'
  simp at h₄
  rcases h₄ with ⟨rfl, h₄⟩
  simp [hb] at h₅
  use ps'

theorem getMoveAt_eq_some_of_tr {s s' p} [hs : sys.WF s]
(h₁ : sys.tr s p = some s') : s'.getMoveAt s = some p := by
  simp [State.getMoveAt, pw_eq_of_tr h₁, hist_eq_of_tr h₁]
  rw [getMoveFromHist_eq_some_iff_exi_trs]
  use hs, s.hist.reverse; simp

theorem getMoveAt_eq_some_of_tr_and_reachable {s s₁ s₂ p} [hs : sys.WF s]
(h₁ : sys.tr s p = some s₁) (h₂ : sys.Reachable s₁ s₂) : s₂.getMoveAt s = some p := by
  rw [System.reachable_iff_exi_trs] at h₂
  obtain ⟨ps, h₂⟩ := h₂
  induction ps using List.reverseRecOn generalizing s₂
  · simp at h₂; subst h₂
    exact getMoveAt_eq_some_of_tr h₁
  nm ps p₁ ih
  simp [System.trs_append] at h₂
  generalize hr : sys.trs s₁ ps = r at h₂
  rcases r with ⟨s₃, ps'⟩
  dsimp at h₂
  split_ifs at h₂ with h₃ <;> simp at h₂
  subst h₃
  simp at h₂
  rcases h₂ with ⟨h₂, h₃⟩
  split at h₃ <;> simp at h₃
  nm x s₄ h₄; clear x h₃
  simp [h₄] at h₂
  subst h₂
  specialize ih hr
  exact getMoveAt_eq_getMoveAt_eq_some_and_tr ih h₄

theorem getMoveAt_eq_some_iff_exi_trs {s₀ s p} [sys.WF s] :
s.getMoveAt s₀ = some p ↔ ∃ ps', ps' ++ [p] <+: s.hist.reverse ∧
sys.trs (initState s.pw) ps' = (s₀, []) := by
  rw [State.getMoveAt, getMoveFromHist_eq_some_iff_exi_trs]
  use λ h => h.2
  rintro ⟨ps', h₁, h₂⟩
  refine' ⟨_, _, h₁, h₂⟩
  apply System.wf_of_trs h₂

open Classical in noncomputable
def dStratOfDWins (sa : State) : DStrat := .mk' # λ sd => do
  let pa ← sd.getMoveAt sa
  let sd' ← sys.tr sa pa
  let pd ← choose? # λ pd => ∃ sa', sys.tr sd' pd = some sa' ∧
    ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF → sa'.d_wins ⟨a, d⟩
  if sd' = sd then some pd else do
    let sa' ← sys.tr sd' pd
    let d ← choose? # λ (d : DStrat) => d.WF ∧
      ∀ (a : AStrat), a.WF → sa'.d_wins ⟨a, d⟩
    return d.f sd

instance {sa} : (dStratOfDWins sa).WF := by unfold dStratOfDWins; infer_instance

def AStrat.set (a : AStrat) (s : State) (p : PointZ) : AStrat := ⟨fn_set s p a.f⟩
def DStrat.set (d : DStrat) (s : State) (p : PointZ) : DStrat := ⟨fn_set s p d.f⟩

@[simp]
theorem AStrat.f_set {a : AStrat} {s p} : (a.set s p).f = fn_set s p a.f := rfl

@[simp]
theorem DStrat.f_set {d : DStrat} {s p} : (d.set s p).f = fn_set s p d.f := rfl

theorem AStrat.wf_set_of_validTr {a : AStrat} {s p} [ha : a.WF]
(h : sys.validTr s p) : (a.set s p).WF := by
  simp [set, wf_iff]; intro s₁ hs₁ h₁; unfold fn_set; split_ifs with h₂
  subst h₂; exact h; exact ha.validTr h₁

theorem DStrat.wf_set_of_validTr {d : DStrat} {s p} [hd : d.WF]
(h : sys.validTr s p) : (d.set s p).WF := by
  simp [set, wf_iff]; intro s₁ hs₁ h₁; unfold fn_set; split_ifs with h₂
  subst h₂; exact h; simp

theorem AStrat.wf_set_of_tr {a : AStrat} {s s' p} [ha : a.WF]
(h : sys.tr s p = some s') : (a.set s p).WF :=
  wf_set_of_validTr ⟨_, h⟩

theorem DStrat.wf_set_of_tr {d : DStrat} {s s' p} [hd : d.WF]
(h : sys.tr s p = some s') : (d.set s p).WF :=
  wf_set_of_validTr ⟨_, h⟩

theorem simulate_congr {s} [hs : sys.WF s]
{st₁ st₂ : Strat} [hst₁ : st₁.WF] [hst₂ : st₂.WF] {n}
(h₁ : ∀ k < n, ∀ sa [AState sa], sys.simulate st₁.f s k = (sa, 0) →
sys.simulate st₂.f s k = (sa, 0) → sys.hasTr sa → st₁.a.f sa = st₂.a.f sa)
(h₂ : ∀ k < n, ∀ sd [DState sd], sys.simulate st₁.f s k = (sd, 0) →
sys.simulate st₂.f s k = (sd, 0) → sys.hasTr sd → st₁.d.f sd = st₂.d.f sd) :
sys.simulate st₁.f s n = sys.simulate st₂.f s n := by
  apply System.simulate_congr
  intro k hk s₁ h₄ h₅ h₆
  have h₇ := System.wf_of_reachable # System.reachable_of_simulate_full h₄
  replace h₇ := s₁.aState_or_dState
  rcases h₇ with ha | hd <;> simp
  · apply h₁ <;> assumption
  · apply h₂ <;> assumption

theorem AState.a_hws_of_not_d_hws {sa} [ha : AState sa] (h : ¬sa.d_hws) : sa.a_hws := by
  apply ha.a_hws_of_ind_two (p := (¬·.d_hws)) h; clear! sa
  intro sa ha h
  unfold State.d_hws at h ⊢
  contrapose h
  push_neg at h ⊢
  use dStratOfDWins sa, inferInstance
  intro a hsa
  by_cases h₁ : ¬sys.hasTr sa
  · simp [System.hasTr] at h₁; use 1; simp [h₁]
  push_neg at h₁
  replace h₁ := hsa.validTr h₁
  generalize hpa : a.f sa = pa at h₁
  obtain ⟨sd, h₁⟩ := h₁
  have hd := DState.of_tr h₁
  specialize h pa sd h₁
  generalize Hpd : Classical.epsilon (λ pd => ∃ sa', sys.tr sd pd = some sa' ∧
    ∃ d, d.WF ∧ ∀ (a : AStrat), a.WF → sa'.d_wins ⟨a, d⟩) = pd
  have h₂ := Classical.epsilon_spec h; rw [Hpd] at h₂
  obtain ⟨sa', h₂, h₃⟩ := h₂
  generalize Hd : Classical.epsilon (λ (d : DStrat) => d.WF ∧
    ∀ (a : AStrat), a.WF → sa'.d_wins ⟨a, d⟩) = d
  have h₄ := Classical.epsilon_spec h₃; rw [Hd] at h₄
  obtain ⟨h₄, h₅⟩ := h₄
  specialize h₅ a hsa
  obtain ⟨n, h₅⟩ := h₅
  use n + 2
  simp [hpa, h₁]
  have h₆ : sys.tr sd ((dStratOfDWins sa).f sd) = some sa'
  · have h₆ : sd.getMoveAt sa = some pa
    · apply getMoveAt_eq_some_of_tr_and_reachable h₁; rfl
    simp [-DState.tr_eq_some_iff, dStratOfDWins, mk_strat_fn, h₆, h₁]
    rw [choose?_eq_of_exi, Hpd]; rotate_left; exact h
    simpa [-DState.tr_eq_some_iff, System.validTr_of_eq_some h₂]
  have ha' := AState.of_tr h₆
  dsimp at h₅
  simp [h₆]
  convert h₅ using 3
  generalize hd₁ : d.set sd pd = d₁
  have hd₂ := d.wf_set_of_tr h₂; rw [hd₁] at hd₂
  trans sys.simulate (Strat.mk a d₁).f sa' n
  rotate_left
  · subst hd₁
    apply simulate_congr <;> simp only [implies_true]
    intro k hk b hb H₁ H₂ H₃
    apply fn_set_eq_of_ne; symm
    have H₄ : sys.Acyclic sd := inferInstance
    replace H₄ := H₄.2 (by rfl) h₂
    rintro rfl
    apply H₄
    exact System.reachable_of_simulate_full H₂
  apply simulate_congr <;> simp only [implies_true]
  intro k hk b hb H₁ H₂ H₃
  replace H₃ : b.getMoveAt sa = some pa
  · apply getMoveAt_eq_some_of_tr_and_reachable h₁
    trans sa'
    · exact System.reachable_of_tr h₂
    · exact System.reachable_of_simulate_full H₁
  simp [dStratOfDWins, mk_strat_fn, H₃, h₁]; clear H₃
  rw [choose?_eq_of_exi, Hpd]; rotate_left; exact h
  simp
  split_ifs with H₃
  · subst H₃ hd₁; simp [System.validTr_of_eq_some h₂]
  rw [h₂]; dsimp
  rw [choose?_eq_of_exi, Hd]
  rotate_left; exact h₃
  subst hd₁; simp; symm
  exact fn_set_eq_of_ne # ne_symm' H₃

open Classical in noncomputable
def aStratOfAHws (sd : State) : AStrat := .mk' # λ sa => do
  let pd ← sa.getMoveAt sd
  let sa' ← sys.tr sd pd
  let a ← choose? # λ (a : AStrat) => a.WF ∧
    ∀ (d : DStrat), d.WF → sa'.a_wins ⟨a, d⟩
  return a.f sa

instance {s} : (aStratOfAHws s).WF := by unfold aStratOfAHws; infer_instance

theorem AState.d_hws_of_tr' {sd sa pd} [hd : DState sd]
(h₁ : sys.tr sd pd = some sa) (h₂ : sa.d_hws) : sd.d_hws := by
  have ha := AState.of_tr h₁
  obtain ⟨d, h₂, h₃⟩ := h₂
  generalize hd₁ : d.set sd pd = d₁
  have H₁ : d₁.WF; subst hd₁; exact DStrat.wf_set_of_tr h₁
  use d₁, H₁
  subst hd₁
  intro a h₄
  specialize h₃ a h₄
  contrapose h₃
  simp at h₃ ⊢
  intro n
  specialize h₃ # n + 1
  simp [h₁] at h₃
  rw [←h₃]
  congr 1
  apply simulate_congr <;> simp
  intro k hk b H₅ H₂ H₃ H₄
  symm; unfold fn_set
  split_ifs with H₆; rotate_left; rfl
  subst H₆
  have H₆ : sys.Acyclic b := inferInstance
  replace H₆ := H₆.2 (by rfl) h₁
  exfalso; apply H₆
  exact System.reachable_of_simulate_full H₂

theorem DState.a_hws_of_tr' {sa sd pa} [ha : AState sa]
(h₁ : sys.tr sa pa = some sd) (h₂ : sd.a_hws) : sa.a_hws := by
  have hd := DState.of_tr h₁
  obtain ⟨a, h₂, h₃⟩ := h₂
  generalize ha₁ : a.set sa pa = a₁
  have H₁ : a₁.WF; subst ha₁; apply AStrat.wf_set_of_tr h₁
  use a₁, H₁
  subst ha₁
  intro d h₄
  specialize h₃ d h₄
  intro n
  cases n; simp; nm n
  specialize h₃ n
  simp [h₁]
  rw [←h₃]
  congr 1
  apply simulate_congr <;> simp
  intro k hk b H₅ H₂ H₃ H₄
  symm; unfold fn_set
  split_ifs with H₆; rotate_left; rfl
  subst H₆
  have H₆ : sys.Acyclic b := inferInstance
  replace H₆ := H₆.2 (by rfl) h₁
  exfalso; apply H₆
  exact System.reachable_of_simulate_full H₂

theorem State.a_hws_of_not_d_hws {s : State} [hs : sys.WF s]
(h : ¬s.d_hws) : s.a_hws := by
  classical
  replace hs := s.aState_or_dState
  rcases hs with  hs | hs; exact hs.a_hws_of_not_d_hws h
  rename' s => sd
  use aStratOfAHws sd, inferInstance
  intro d hd n
  cases n; rfl; nm n
  obtain ⟨sa, h₁⟩ := hd.validTr sd
  simp [h₁]
  have ha := AState.of_tr h₁
  replace h : ¬sa.d_hws
  · contrapose! h; exact AState.d_hws_of_tr' h₁ h
  replace h := ha.a_hws_of_not_d_hws h
  unfold State.a_hws at h
  generalize h₂ : Classical.epsilon (λ (a : AStrat) => a.WF ∧
    ∀ (d : DStrat), d.WF → sa.a_wins { a := a, d := d }) = a
  have h₃ := Classical.epsilon_spec h; rw [h₂] at h₃
  rcases h₃ with ⟨h₃, h₄⟩
  specialize h₄ d hd n
  rw [←h₄]
  congr 1
  apply simulate_congr <;> simp
  intro k hk b H₅ H₂ H₃ H₄
  have H₆ : b.getMoveAt sd = some (d.f sd)
  · apply getMoveAt_eq_some_of_tr_and_reachable h₁
    exact System.reachable_of_simulate_full H₂
  simp [aStratOfAHws, mk_strat_fn, H₆, h₁]
  rw [choose?_eq_of_exi, h₂]; rotate_left; exact h
  simp [h₃.validTr H₄]

@[simp]
theorem State.not_a_hws_iff {s : State} [hs : s.WF] : ¬s.a_hws ↔ s.d_hws := by
  refine' ⟨λ h => _, s.not_a_hws_of_d_hws⟩
  contrapose! h; exact s.a_hws_of_not_d_hws h

@[simp]
theorem State.not_d_hws_iff {s : State} [hs : s.WF] : ¬s.d_hws ↔ s.a_hws := by
  simp [not_iff_comm']

theorem AState.hasTr_of_a_hws {sa} [hs : AState sa]
(h : sa.a_hws) : sys.hasTr sa := by
  obtain ⟨a, h₁, h₂⟩ := h
  specialize h₂ (.mk' # λ _ => none) inferInstance 1
  simp at h₂
  split at h₂; simp at h₂
  nm x sd h₃; clear x h₂
  exact System.hasTr_of_eq_some h₃

theorem AState.a_hws_iff_tr {sa} [hs : AState sa] :
sa.a_hws ↔ ∃ p sd, sys.tr sa p = some sd ∧ sd.a_hws := by
  constructor
  · intro h
    obtain h₁ := hs.hasTr_of_a_hws h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨sd, h₂⟩ := ha.validTr h₁
    use a.f sa, sd, h₂, a, ha
    intro d hd n
    specialize h d hd (n + 1)
    simp [h₂] at h
    exact h
  · rintro ⟨p, sd, h₁, h₂⟩
    have h₃ := DState.of_tr h₁
    exact DState.a_hws_of_tr' h₁ h₂

theorem AState.d_hws_iff_tr {sa} [hs : AState sa] :
sa.d_hws ↔ ∀ p sd, sys.tr sa p = some sd → sd.d_hws := by
  rw [←State.not_a_hws_iff, not_iff_comm']; push_neg
  convert hs.a_hws_iff_tr using 5; nm p sd
  rw [and_congr_right_iff]; intro h
  have h₁ := DState.of_tr h; simp

theorem DState.d_hws_iff_tr {sd} [hs : DState sd] :
sd.d_hws ↔ ∃ p sa, sys.tr sd p = some sa ∧ sa.d_hws := by
  constructor
  · intro h
    obtain ⟨d, hd, h⟩ := h
    obtain ⟨sa, h₂⟩ := hd.validTr sd
    use d.f sd, sa, h₂, d, hd
    intro a ha
    specialize h a ha
    obtain ⟨n, h⟩ := h
    cases n; simp at h; nm n
    use n; simp [h₂] at h; exact h
  · rintro ⟨p, sa, h₁, h₂⟩
    have h₃ := AState.of_tr h₁
    exact AState.d_hws_of_tr' h₁ h₂

theorem DState.a_hws_iff_tr {sd} [hs : DState sd] :
sd.a_hws ↔ ∀ p sa, sys.tr sd p = some sa → sa.a_hws := by
  rw [←State.not_d_hws_iff, not_iff_comm']; push_neg
  convert hs.d_hws_iff_tr using 5; nm p sa
  rw [and_congr_right_iff]; intro h
  have h₁ := AState.of_tr h; simp

theorem AState.a_hws_of_ind {s} [ha : AState s]
{p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, p sd → sys.tr sd pd = some sa → p sa) : s.a_hws := by
  apply ha.a_hws_of_ind_two h₁
  intro sa h₄ h₅
  specialize h₂ sa h₅
  obtain ⟨pa, sd, h₂, h₆⟩ := h₂
  use pa, sd, h₂
  intro pd sa' h₇
  have h₈ := DState.of_tr h₂
  exact h₃ sd pd sa' h₆ h₇

theorem AState.a_wins_of_ind {s} [ha : AState s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, p sd → sys.tr sd (st.d.f sd) = some sa → p sa) :
s.a_wins st := by
  apply ha.a_wins_of_ind_two h₁
  intro sa h₄ h₅
  specialize h₂ sa h₅
  obtain ⟨sd, h₂, h₆⟩ := h₂
  use sd, h₂
  intro sa' h₇
  have h₈ := DState.of_tr h₂
  exact h₃ sd sa' h₆ h₇

theorem State.a_wins_of_ind {s} [hs : sys.WF s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, p sd → sys.tr sd (st.d.f sd) = some sa → p sa) :
s.a_wins st := by
  replace hs := s.aState_or_dState
  rcases hs with ha | hd
  · exact ha.a_wins_of_ind h₁ h₂ h₃
  intro n
  cases n; rfl; nm n
  simp
  obtain ⟨sa, h₄⟩ := hst.wf_d.validTr s
  simp [h₄]
  have h₅ := AState.of_tr h₄
  have h₆ := h₃ s sa h₁ h₄
  apply h₅.a_wins_of_ind h₆ h₂ h₃

theorem State.a_hws_of_ind {s} [hs : sys.WF s]
{p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, p sd → sys.tr sd pd = some sa → p sa) : s.a_hws := by
  replace hs := s.aState_or_dState
  rcases hs with ha | hd
  · exact ha.a_hws_of_ind h₁ h₂ h₃
  rw [hd.a_hws_iff_tr]
  intro pd sa h₅
  have h₆ := AState.of_tr h₅
  have h₇ := h₃ s pd sa h₁ h₅
  exact h₆.a_hws_of_ind h₇ h₂ h₃

open Classical in noncomputable
def aSeek (p : State → Prop) : AStrat := .mk' # λ sa =>
  choose? # λ pa => ∃ sd, sys.tr sa pa = some sd ∧ p sd

instance {p} : (aSeek p).WF := by unfold aSeek; infer_instance

theorem State.exi_a_wins_of_ind {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, p sd → sys.tr sd (d.f sd) = some sa → p sa) :
∃ (a : AStrat), a.WF ∧ s.a_wins ⟨a, d⟩ := by
  use aSeek p, inferInstance
  apply a_wins_of_ind h₁; clear! s
  · intro sa ha ih; dsimp
    specialize h₂ sa ih
    simp [-AState.tr_eq_some_iff, aSeek, mk_strat_fn, choose?_eq_ite, h₂]
    generalize hp : Classical.epsilon
      (λ pa => ∃ sd, sys.tr sa pa = some sd ∧ p sd) = pa
    have h₄ := Classical.epsilon_spec h₂
    rw [hp] at h₄
    rcases h₄ with ⟨sd, h₄, h₅⟩
    simp [-AState.tr_eq_some_iff, sys.validTr_of_eq_some h₄]
    use sd
  · intro sd hd sa ih h₄; dsimp at h₄
    have ha := AState.of_tr h₄
    exact h₃ sd sa ih h₄

theorem State.a_wins_iff_add {s st} (k : ℕ) :
s.a_wins st ↔ ∀ n, (sys.simulate st.f s # k + n).2 = 0 := by
  constructor <;> intro h₁ n
  · exact h₁ # k + n
  · apply System.simulate_snd_eq_zero_of_le_and_eq_zero # h₁ n
    linarith

theorem State.d_wins_iff_add {s st} (k : ℕ) :
s.d_wins st ↔ ∃ n, (sys.simulate st.f s # k + n).2 ≠ 0 := by
  constructor <;> rintro ⟨n, h₁⟩
  · use n
    contrapose! h₁
    apply System.simulate_snd_eq_zero_of_le_and_eq_zero h₁
    linarith
  · use k + n

theorem State.length_hist_lt_of_tr {s s' p}
(h : sys.tr s p = some s') : s.hist.length < s'.hist.length := by
  simp [hist_eq_of_tr h]

theorem length_hist_sub_eq_of_simulate {st : Strat} {s₀ s n} [hs : sys.WF s₀]
(h : sys.simulate st.f s₀ n = (s, 0)) : s.hist.length - s₀.hist.length = n := by
  induction n generalizing s₀
  · simp at h; simp [h]
  nm n ih
  simp at h
  split at h; simp at h; nm x s' h₁; clear x
  have hs' := sys.wf_of_tr h₁
  specialize ih h
  rw [hist_eq_of_tr h₁] at ih
  simp at ih
  rw [←ih]; clear ih
  rw [Nat.sub_succ]
  simp
  rw [Nat.sub_add_cancel]
  have h₂ : s'.hist.length ≤ s.hist.length
  · apply length_hist_le_of_reachable
    exact System.reachable_of_simulate_full h
  have h₃ : s₀.hist.length < s'.hist.length
  · exact State.length_hist_lt_of_tr h₁
  omega

theorem AState.d_hws_of_tr {sa sd p} [ha : AState sa]
(h₁ : sys.tr sa p = some sd) (h₂ : sa.d_hws) : sd.d_hws :=
  d_hws_iff_tr.mp h₂ _ _ h₁

theorem DState.a_hws_of_tr {sd sa p} [hd : DState sd]
(h₁ : sys.tr sd p = some sa) (h₂ : sd.a_hws) : sa.a_hws :=
  a_hws_iff_tr.mp h₂ _ _ h₁

theorem State.d_wins_of_lt_lt {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd < f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa < f sd) : s.d_wins ⟨a, d⟩ := by
  generalize hn : f s = n
  induction n using Nat.strong_induction_on generalizing s
  nm n ih
  subst hn
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · by_cases h₄ : sys.hasTr s
    rotate_left
    · use 1
      rw [sys.simulate_eq_of_not_hasTr h₄]
      simp
    replace h₄ := a.validTr h₄
    obtain ⟨s', h₄⟩ := h₄
    have := DState.of_tr h₄
    obtain ⟨h₅, h₆⟩ := h₂ s s' h₁ h₄
    specialize ih (f s') h₆ h₅ rfl
    obtain ⟨n, ih⟩ := ih
    use n + 1
    simpa [h₄]
  · have h₄ := d.validTr s
    obtain ⟨s', h₄⟩ := h₄
    have := AState.of_tr h₄
    obtain ⟨h₅, h₆⟩ := h₃ s s' h₁ h₄
    specialize ih (f s') h₆ h₅ rfl
    obtain ⟨n, ih⟩ := ih
    use n + 1
    simpa [h₄]

theorem State.d_wins_of_le_lt {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd ≤ f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa < f sd) : s.d_wins ⟨a, d⟩ := by
  apply s.d_wins_of_lt_lt (a := a) (d := d) (p := p)
    (f := λ s => f s * 2 + if s.aTurn then 1 else 0) h₁
  · intro sa sd hsa hsd h₄ h₅
    simp
    specialize h₂ sa sd h₄ h₅
    use h₂.1; replace h₂ := h₂.2
    linarith
  · intro sd sa hsd hsa h₄ h₅
    simp
    specialize h₃ sd sa h₄ h₅
    use h₃.1; replace h₃ := h₃.2
    linarith

theorem State.d_wins_of_lt_le {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd < f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa ≤ f sd) : s.d_wins ⟨a, d⟩ := by
  apply s.d_wins_of_lt_lt (a := a) (d := d) (p := p)
    (f := λ s => f s * 2 + if s.aTurn then 0 else 1) h₁
  · intro sa sd hsa hsd h₄ h₅
    simp
    specialize h₂ sa sd h₄ h₅
    use h₂.1; replace h₂ := h₂.2
    linarith
  · intro sd sa hsd hsa h₄ h₅
    simp
    specialize h₃ sd sa h₄ h₅
    use h₃.1; replace h₃ := h₃.2
    linarith

theorem State.d_wins_of_lt_lt_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd < f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa < f sd) :
s.d_wins ⟨a, d⟩ := by
  have h₃ := s.d_wins_of_lt_lt (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

theorem State.d_wins_of_le_lt_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd ≤ f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa < f sd) :
s.d_wins ⟨a, d⟩ := by
  have h₃ := s.d_wins_of_le_lt (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

theorem State.d_wins_of_lt_le_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd < f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa ≤ f sd) :
s.d_wins ⟨a, d⟩ := by
  have h₃ := s.d_wins_of_lt_le (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

@[simp]
theorem not_a_hws_pw_iff {pw} : ¬a_hws_pw pw ↔ d_hws_pw pw :=
  State.not_a_hws_iff

@[simp]
theorem not_d_hws_pw_iff {pw} : ¬d_hws_pw pw ↔ a_hws_pw pw :=
  State.not_d_hws_iff