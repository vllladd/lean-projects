import Projects.AP.Basic

namespace AP

open Classical in noncomputable
def aSeek (p : State → Prop) : AStrat := .mk # λ sa =>
  choose? # λ pa => ∃ sd, sys.tr sa pa = some sd ∧ p sd

def aStratChooseCnd (p : State → Prop) (sa : State) (pa : PointZ) : Prop :=
  ∃ sd, sys.tr sa pa = some sd ∧ ∀ pd sa', sys.tr sd pd = some sa' → p sa'

open Classical in noncomputable
def aStratChoose (p : State → Prop) : AStrat :=
  .mk # λ sa => choose? # aStratChooseCnd p sa

@[simp]
def getMoveFromHist (s_target s : State) : List PointZ → Option PointZ
| [] => none
| p :: ps => if s = s_target then some p else do
  let s' ← sys.tr s p
  getMoveFromHist s_target s' ps

def State.getMoveAt (s s_target : State) : Option PointZ :=
  getMoveFromHist s_target (initState s.pw s.aPos₀) s.hist.reverse.tail

open Classical in noncomputable
def dStratOfDWins (sa : State) : DStrat := .mk # λ sd => do
  let pa ← sd.getMoveAt sa
  let sd' ← sys.tr sa pa
  let pd ← choose? # λ pd => ∃ sa', sys.tr sd' pd = some sa' ∧
    ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF → sa'.dWins ⟨a, d⟩
  if sd' = sd then some pd else do
    let sa' ← sys.tr sd' pd
    let d ← choose? # λ (d : DStrat) => d.WF ∧
      ∀ (a : AStrat), a.WF → sa'.dWins ⟨a, d⟩
    return d.f sd

def AStrat.set (a : AStrat) (s : State) (p : PointZ) : AStrat := ⟨fn_set s p a.f⟩
def DStrat.set (d : DStrat) (s : State) (p : PointZ) : DStrat := ⟨fn_set s p d.f⟩

open Classical in noncomputable
def aStratOfAHws (sd : State) : AStrat := .mk # λ sa => do
  let pd ← sa.getMoveAt sd
  let sa' ← sys.tr sd pd
  let a ← choose? # λ (a : AStrat) => a.WF ∧
    ∀ (d : DStrat), d.WF → sa'.aWins ⟨a, d⟩
  return a.f sa

-----

theorem State.not_aHws_of_dHws {s : State} (h : s.dHws) : ¬s.aHws := by
  obtain ⟨d, hd, h⟩ := h
  simp [aHws]
  intro a ha
  use d, hd
  exact h a ha

theorem AState.of_simulate_mul_two {sa} [ha : AState sa]
{st : Strat} [hst : st.WF] {n} : AState (sys.simulate st.f sa # n * 2).1 := by
  induction n generalizing sa; exact ha
  nm n ih
  simp [Nat.succ_mul, System.simulate]
  split; exact ha
  nm x sd h₁; clear x
  have hd := DState.of_tr h₁
  split; nm x h₂; simp at h₂
  nm x sa' h₂; clear x
  have ha' := AState.of_tr h₂
  exact ih

@[simp]
instance {sa} [ha : AState sa] {st : Strat} [hst : st.WF] {n} :
AState (sys.simulate st.f sa # n * 2).1 :=
  ha.of_simulate_mul_two

theorem AState.of_simulate_mul_two_eq' {sa s₁ r} [ha : AState sa]
{st : Strat} [hst : st.WF] {n} (h : sys.simulate st.f sa (n * 2) = (s₁, r)) : AState s₁ := by
  rw [Prod.fst_eq_of_eq_mk h]; infer_instance

theorem AState.of_simulate_mul_two_eq_full {sa s₁ f} [ha : AState sa]
{n} (h : sys.simulate f sa (n * 2) = (s₁, 0)) : AState s₁ := by
  induction n generalizing sa
  · simp at h
    rwa [←h]
  nm n ih
  simp_rw [Nat.add_mul, sys.simulate_succ_full'] at h
  obtain ⟨sd, h₁, sa', h₂, h₃⟩ := h
  have hsd := DState.of_tr h₁
  have hsa' := AState.of_tr h₂
  exact ih h₃

theorem DState.of_simulate_mul_two_eq_full {sd s₁ f} [hd : DState sd]
{n} (h : sys.simulate f sd (n * 2) = (s₁, 0)) : DState s₁ := by
  induction n generalizing sd
  · simp at h
    rwa [←h]
  nm n ih
  simp_rw [Nat.add_mul, sys.simulate_succ_full'] at h
  obtain ⟨sd, h₁, sa', h₂, h₃⟩ := h
  have hsd := AState.of_tr h₁
  have hsa' := DState.of_tr h₂
  exact ih h₃

theorem AState.aWins_of_ind_two' {sa₀} [ha₀ : AState sa₀]
{st : Strat} [hst : st.WF] {p : State → Prop} (hp : p sa₀)
(h : ∀ {sa} [AState sa], sys.Reachable sa₀ sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ ∀ sa',
sys.tr sd (st.d.f sd) = some sa' → p sa') : sa₀.aWins st ∧ p sa₀ := by
  rw [sa₀.aWins_iff_mul_two]
  suffices h₁ : ∀ n, ∃ b, sys.simulate st.f sa₀ (n * 2) = (b, 0) ∧ p b
  · constructor
    · intro n; specialize h₁ n; obtain ⟨b, h₁, h₂⟩ := h₁; simp [h₁]
    · specialize h₁ 0; simp at h₁; exact h₁
  intro n
  induction n
  · use sa₀; simpa
  nm n ih
  clear hp
  obtain ⟨sa, ih, hp⟩ := ih
  simp only [Nat.succ_mul, System.simulate_add]
  have ha : AState sa
  · replace ih := congrArg (·.1) ih; subst ih; infer_instance
  simp [ih]
  specialize h (sys.reachable_of_simulate ih) hp
  obtain ⟨sd, h₁, h₂⟩ := h
  simp [h₁]
  have hd := DState.of_tr h₁
  obtain ⟨sa', h₃⟩ := hst.wf_d.1 hd.hasTr hd.turn
  simp [h₃]
  exact h₂ _ h₃

theorem AState.aWins_of_ind_two {sa₀} [ha₀ : AState sa₀]
{st : Strat} [hst : st.WF] {p : State → Prop} (hp : p sa₀)
(h : ∀ {sa} [AState sa], sys.Reachable sa₀ sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ ∀ sa',
sys.tr sd (st.d.f sd) = some sa' → p sa') : sa₀.aWins st :=
  ha₀.aWins_of_ind_two' hp h |>.1

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
  simp at h₃; choose sd h₄ h₃ using h₃
  have hd := DState.of_tr h₄
  cases ts; simp at h₃; simp [h₃] at hd; nm pd ts
  simp at h₃; choose sa₁ h₅ h₃ using h₃
  simp [add_assoc] at hn; subst hn
  have ha₁ := AState.of_tr h₅
  exact @ih ts.length (by simp) sa₁ _
    (h₂ sa pa sd pd sa₁ h₄ h₅) ts h₃ rfl

theorem wf_aStratChoose {p} : (aStratChoose p).WF := by
  unfold aStratChoose; infer_instance

@[simp, grind ·]
instance {p} : (aStratChoose p).WF := wf_aStratChoose

theorem AState.aHws_of_ind_two' {sa₀ : State} [ha₀ : AState sa₀] {p : State → Prop}
(h₁ : p sa₀) (h₂ : ∀ sa [AState sa], sys.Reachable sa₀ sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ ∀ pd sa',
sys.tr sd pd = some sa' → p sa') : sa₀.aHws ∧ p sa₀ := by
  classical
  convert_to ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → sa₀.aWins ⟨a, d⟩ ∧ p sa₀
  · simp_all only [State.aHws, and_true]
  use aStratChoose p, inferInstance
  intro d hd
  apply ha₀.aWins_of_ind_two' h₁
  intro sa ha hp H
  specialize h₂ sa hp H
  simp only [aStratChoose, choose?_eq_ite]
  replace h₂ : ∃ pa, aStratChooseCnd p sa pa := h₂
  have h₃ := Classical.epsilon_spec h₂
  generalize h₁ : Classical.epsilon (aStratChooseCnd p sa) = pa at h₃ ⊢
  unfold aStratChooseCnd at h₃
  obtain ⟨sd, h₃, h₄⟩ := h₃; use sd
  simp [h₂, h₁, sys.validTr_iff_isSome, h₃]; apply h₄

theorem AState.aHws_of_ind_two {sa₀ : State} [ha₀ : AState sa₀] {p : State → Prop}
(h₁ : p sa₀) (h₂ : ∀ sa [AState sa], sys.Reachable sa₀ sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ ∀ pd sa',
sys.tr sd pd = some sa' → p sa') : sa₀.aHws :=
  ha₀.aHws_of_ind_two' h₁ h₂ |>.1

@[simp, grind ·]
instance {s} [hs : sys.WF s] : sys.Tree s := by
  rw [System.tree_iff_full_trs]
  use hs; intro ts₁ ts₂ s' h₁ h₂
  have h₃ := congrArg (·.1.hist) h₁
  have h₄ := congrArg (·.1.hist) h₂
  simp at h₃ h₄
  simp [h₂] at h₄
  simp [h₁, ←h₄] at h₃
  exact h₃

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

theorem getMoveAt_eq_getMoveAt_eq_some_and_tr {s₁ s₂ p₁ s p} [hs : sys.WF s₁]
(h₁ : s₁.getMoveAt s = some p) (h₂ : sys.tr s₁ p₁  = some s₂) :
s₂.getMoveAt s = some p := by
  unfold State.getMoveAt at h₁ ⊢
  simp [-List.tail_reverse, pw_eq_of_tr h₂, hist_eq_of_tr h₂]
  generalize initState s₁.pw = acc at h₁ ⊢
  generalize hp : s₁.hist.reverse = ps at h₁ ⊢
  replace hp : ps ≠ []; simp [←hp]
  generalize [p₁] = ps₁
  apply getMoveFromHist_append_eq_some_of
  convert h₁ using 3
  exact State.aPos₀_eq_of_tr h₂

theorem getMoveFromHist_eq_some_iff_exi_trs {s acc p ps} [hs : sys.WF acc] :
getMoveFromHist s acc ps = some p ↔ sys.WF s ∧
∃ ps', ps' ++ [p] <+: ps ∧ sys.trs acc ps' = (s, []) := by
  induction ps generalizing acc; simp
  nm p₁ ps ih
  simp
  generalize hb : sys.tr acc p₁ = r
  split_ifs with h₁
  · subst h₁; simp [hs]
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
  simp [-List.tail_reverse, State.getMoveAt, pw_eq_of_tr h₁, hist_eq_of_tr h₁]
  rw [getMoveFromHist_eq_some_iff_exi_trs]; use hs, s.hist.reverse.tail
  simp [-List.tail_reverse, State.aPos₀_eq_of_tr h₁]

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
  rcases h₂ with ⟨h₂, s₄, h₄⟩
  simp [System.trs, h₄] at h₂
  subst h₂
  specialize ih hr
  have hs₁ := sys.wf_of_tr h₁
  have hs₃ := sys.wf_of_trs hr
  exact getMoveAt_eq_getMoveAt_eq_some_and_tr ih h₄

theorem getMoveAt_eq_some_iff_exi_trs {s₀ s p} [sys.WF s] :
s.getMoveAt s₀ = some p ↔ ∃ ps', ps' ++ [p] <+: s.hist.reverse.tail ∧
sys.trs (initState s.pw s.aPos₀) ps' = (s₀, []) := by
  rw [State.getMoveAt, getMoveFromHist_eq_some_iff_exi_trs]
  use λ h => h.2
  rintro ⟨ps', h₁, h₂⟩
  refine' ⟨_, _, h₁, h₂⟩
  apply System.wf_of_trs h₂

instance {sa} : (dStratOfDWins sa).WF := by
  unfold dStratOfDWins; infer_instance

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
  simp [set, wf_iff]; intro s₁ hs₁; unfold fn_set; split_ifs with h₂
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
  have h₇ := System.wf_of_reachable # System.reachable_of_simulate h₄
  replace h₇ := s₁.aState_or_dState
  rcases h₇ with ha | hd <;> simp
  · apply h₁ <;> assumption
  · apply h₂ <;> assumption

theorem AState.aHws_of_not_dHws {sa} [ha : AState sa] (h : ¬sa.dHws) : sa.aHws := by
  apply ha.aHws_of_ind_two (p := (¬·.dHws)) h; clear! sa
  intro sa ha H h
  unfold State.dHws at h ⊢
  contrapose h
  push_neg at h
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
    ∃ d, d.WF ∧ ∀ (a : AStrat), a.WF → sa'.dWins ⟨a, d⟩) = pd
  have h₂ := Classical.epsilon_spec h; rw [Hpd] at h₂
  obtain ⟨sa', h₂, h₃⟩ := h₂
  generalize Hd : Classical.epsilon (λ (d : DStrat) => d.WF ∧
    ∀ (a : AStrat), a.WF → sa'.dWins ⟨a, d⟩) = d
  have h₄ := Classical.epsilon_spec h₃; rw [Hd] at h₄
  obtain ⟨h₄, h₅⟩ := h₄
  specialize h₅ a hsa
  obtain ⟨n, h₅⟩ := h₅
  use n + 2
  simp only [show 2 = 1 + 1 by rfl, ←add_assoc, ne_def,
    sys.snd_simulate_add_one_eq_zero_iff']
  simp [hpa, h₁]
  have h₆ : sys.tr sd (dStratOfDWins sa |>.f sd) = some sa'
  · have h₆ : sd.getMoveAt sa = some pa
    · apply getMoveAt_eq_some_of_tr_and_reachable h₁; rfl
    simp [dStratOfDWins, mkStratFn, h₆, h₁]
    rw [choose?_eq_of_exi, Hpd]; rotate_left; exact h
    simpa [System.validTr_of_eq_some h₂]
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
    exact System.reachable_of_simulate H₂
  apply simulate_congr <;> simp only [implies_true]
  intro k hk b hb H₁ H₂ H₃
  replace H₃ : b.getMoveAt sa = some pa
  · apply getMoveAt_eq_some_of_tr_and_reachable h₁
    trans sa'
    · exact System.reachable_of_tr h₂
    · exact System.reachable_of_simulate H₁
  simp [dStratOfDWins, mkStratFn, H₃, h₁]; clear H₃
  rw [choose?_eq_of_exi, Hpd]; rotate_left; exact h
  simp
  split_ifs with H₃
  · subst H₃ hd₁; simp [System.validTr_of_eq_some h₂]
  rw [h₂]; dsimp
  rw [choose?_eq_of_exi, Hd]
  rotate_left; exact h₃
  subst hd₁; simp; symm
  exact fn_set_eq_of_ne # ne_symm' H₃

instance {s} : (aStratOfAHws s).WF := by
  unfold aStratOfAHws; infer_instance

theorem AState.dHws_of_tr' {sd sa pd} [hd : DState sd]
(h₁ : sys.tr sd pd = some sa) (h₂ : sa.dHws) : sd.dHws := by
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
  rw [sys.snd_simulate_add_one_eq_zero_iff'] at h₃
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
  exact System.reachable_of_simulate H₂

theorem DState.aHws_of_tr' {sa sd pa} [ha : AState sa]
(h₁ : sys.tr sa pa = some sd) (h₂ : sd.aHws) : sa.aHws := by
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
  rw [sys.snd_simulate_add_one_eq_zero_iff']
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
  exact System.reachable_of_simulate H₂

theorem State.aHws_of_not_dHws {s : State} [hs : sys.WF s]
(h : ¬s.dHws) : s.aHws := by
  classical
  replace hs := s.aState_or_dState
  rcases hs with  hs | hs; exact hs.aHws_of_not_dHws h
  rename' s => sd
  use aStratOfAHws sd, inferInstance
  intro d hd n
  cases n; rfl; nm n
  obtain ⟨sa, h₁⟩ := hd.validTr sd
  rw [sys.snd_simulate_add_one_eq_zero_iff']
  simp [h₁]
  have ha := AState.of_tr h₁
  replace h : ¬sa.dHws
  · contrapose! h; exact AState.dHws_of_tr' h₁ h
  replace h := ha.aHws_of_not_dHws h
  unfold State.aHws at h
  generalize h₂ : Classical.epsilon (λ (a : AStrat) => a.WF ∧
    ∀ (d : DStrat), d.WF → sa.aWins { a := a, d := d }) = a
  have h₃ := Classical.epsilon_spec h; rw [h₂] at h₃
  rcases h₃ with ⟨h₃, h₄⟩
  specialize h₄ d hd n
  rw [←h₄]
  congr 1
  apply simulate_congr <;> simp
  intro k hk b H₅ H₂ H₃ H₄
  have H₆ : b.getMoveAt sd = some (d.f sd)
  · apply getMoveAt_eq_some_of_tr_and_reachable h₁
    exact System.reachable_of_simulate H₂
  simp [aStratOfAHws, mkStratFn, H₆, h₁]
  rw [choose?_eq_of_exi, h₂]; rotate_left; exact h
  simp [h₃.validTr H₄]

@[simp]
theorem State.not_aHws_iff {s : State} [hs : sys.WF s] : ¬s.aHws ↔ s.dHws := by
  refine' ⟨λ h => _, s.not_aHws_of_dHws⟩
  contrapose! h; exact s.aHws_of_not_dHws h

@[simp]
theorem State.not_dHws_iff {s : State} [hs : sys.WF s] : ¬s.dHws ↔ s.aHws := by
  simp [not_iff_comm']

theorem State.hasTr_of_aHws {s} (h : s.aHws) : sys.hasTr s := by
  obtain ⟨a, h₁, h₂⟩ := h
  specialize h₂ (.mk # λ _ => none) inferInstance 1
  simp at h₂
  choose s₁ h₂ using h₂
  exact sys.hasTr_of_eq_some h₂

theorem AState.aHws_iff_tr {sa} [hs : AState sa] :
sa.aHws ↔ ∃ p sd, sys.tr sa p = some sd ∧ sd.aHws := by
  constructor
  · intro h
    obtain h₁ := State.hasTr_of_aHws h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨sd, h₂⟩ := ha.validTr h₁
    use a.f sa, sd, h₂, a, ha
    intro d hd n
    specialize h d hd (n + 1)
    rw [sys.snd_simulate_add_one_eq_zero_iff'] at h
    simp [h₂] at h
    exact h
  · rintro ⟨p, sd, h₁, h₂⟩
    have h₃ := DState.of_tr h₁
    exact DState.aHws_of_tr' h₁ h₂

theorem AState.dHws_iff_tr {sa} [hs : AState sa] :
sa.dHws ↔ ∀ p sd, sys.tr sa p = some sd → sd.dHws := by
  rw [←State.not_aHws_iff, not_iff_comm']; push_neg
  convert hs.aHws_iff_tr using 5; nm p sd
  rw [and_congr_right_iff]; intro h
  have h₁ := DState.of_tr h; simp

theorem DState.dHws_iff_tr {sd} [hs : DState sd] :
sd.dHws ↔ ∃ p sa, sys.tr sd p = some sa ∧ sa.dHws := by
  constructor
  · intro h
    obtain ⟨d, hd, h⟩ := h
    obtain ⟨sa, h₂⟩ := hd.validTr sd
    use d.f sd, sa, h₂, d, hd
    intro a ha
    specialize h a ha
    obtain ⟨n, h⟩ := h
    cases n; simp at h; nm n
    use n; rw [ne_def, sys.snd_simulate_add_one_eq_zero_iff'] at h
    simp [h₂] at h; exact h
  · rintro ⟨p, sa, h₁, h₂⟩
    have h₃ := AState.of_tr h₁
    exact AState.dHws_of_tr' h₁ h₂

theorem DState.aHws_iff_tr {sd} [hs : DState sd] :
sd.aHws ↔ ∀ p sa, sys.tr sd p = some sa → sa.aHws := by
  rw [←State.not_dHws_iff, not_iff_comm']; push_neg
  convert hs.dHws_iff_tr using 5; nm p sa
  rw [and_congr_right_iff]; intro h
  have h₁ := AState.of_tr h; simp

theorem AState.aHws_of_ind' {s} [ha : AState s] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, sys.Reachable s sd → p sd →
sys.tr sd pd = some sa → p sa) : s.aHws ∧ p s := by
  apply ha.aHws_of_ind_two' h₁
  intro sa h₄ H h₅
  specialize h₂ sa H h₅
  obtain ⟨pa, sd, h₂, h₆⟩ := h₂
  use pa, sd, h₂
  intro pd sa' h₇
  have h₈ := DState.of_tr h₂
  exact h₃ sd pd sa' (sys.reachable_right H h₂) h₆ h₇

theorem AState.aHws_of_ind {s} [ha : AState s] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, sys.Reachable s sd → p sd →
sys.tr sd pd = some sa → p sa) : s.aHws :=
  ha.aHws_of_ind' h₁ h₂ h₃ |>.1

theorem AState.aWins_of_ind' {s} [ha : AState s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, sys.Reachable s sd → p sd →
sys.tr sd (st.d.f sd) = some sa → p sa) : s.aWins st ∧ p s := by
  apply ha.aWins_of_ind_two' h₁
  intro sa h₄ H h₅
  specialize h₂ sa H h₅
  obtain ⟨sd, h₂, h₆⟩ := h₂
  use sd, h₂
  intro sa' h₇
  have h₈ := DState.of_tr h₂
  exact h₃ sd sa' (sys.reachable_right H h₂) h₆ h₇

theorem AState.aWins_of_ind {s} [ha : AState s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, sys.Reachable s sd → p sd →
sys.tr sd (st.d.f sd) = some sa → p sa) : s.aWins st :=
  ha.aWins_of_ind' h₁ h₂ h₃ |>.1

theorem State.aWins_of_ind' {s} [hs : sys.WF s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, sys.Reachable s sd → p sd →
sys.tr sd (st.d.f sd) = some sa → p sa) : s.aWins st ∧ p s := by
  replace hs := s.aState_or_dState
  rcases hs with ha | hd
  · exact ha.aWins_of_ind' h₁ h₂ h₃
  convert_to ∀ n, (sys.simulate st.f s n).2 = 0 ∧ p s
  · unfold State.aWins
    clear h₂ h₃
    use by tauto
    intro h
    use λ n => h n |>.1
  intro n
  cases n; simpa; nm n
  rw [sys.snd_simulate_add_one_eq_zero_iff']
  simp
  obtain ⟨sa, h₄⟩ := hst.wf_d.validTr s
  simp [h₄]
  have h₅ := AState.of_tr h₄
  have h₆ := h₃ s sa (by rfl) h₁ h₄
  refine ⟨?_, h₁⟩
  apply h₅.aWins_of_ind h₆
  · intro sa₁ hsa₁ H₁ H₂; exact h₂ _ (H₁.step h₄) H₂
  · intro sd₁ hsd₁ H₁ H₂; apply h₃; exact H₂.step h₄

theorem State.aWins_of_ind {s} [hs : sys.WF s]
{st : Strat} [hst : st.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ sd, sys.tr sa (st.a.f sa) = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, sys.Reachable s sd → p sd →
sys.tr sd (st.d.f sd) = some sa → p sa) : s.aWins st :=
  s.aWins_of_ind' h₁ h₂ h₃ |>.1

theorem State.aHws_of_ind' {s} [hs : sys.WF s] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, sys.Reachable s sd → p sd →
sys.tr sd pd = some sa → p sa) : s.aHws ∧ p s := by
  replace hs := s.aState_or_dState
  rcases hs with ha | hd
  · exact ha.aHws_of_ind' h₁ h₂ h₃
  rw [hd.aHws_iff_tr]
  convert_to ∀ p₁ sa, sys.tr s p₁ = some sa → sa.aHws ∧ p s
  · simp_all only [and_true]
  intro pd sa h₅
  have h₆ := AState.of_tr h₅
  have h₇ := h₃ s pd sa (by rfl) h₁ h₅
  refine ⟨?_, h₁⟩
  apply h₆.aHws_of_ind h₇
  · intro sa₁ hsa₁ H₁ H₂; exact h₂ _ (H₁.step h₅) H₂
  · intro sd₁ hsd₁ H₁ H₂ H₃; apply h₃; exact H₃.step h₅

theorem State.aHws_of_ind {s} [hs : sys.WF s] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], sys.Reachable s sa → p sa →
∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] pd sa, sys.Reachable s sd → p sd →
sys.tr sd pd = some sa → p sa) : s.aHws :=
  s.aHws_of_ind' h₁ h₂ h₃ |>.1

instance {p} : (aSeek p).WF := by unfold aSeek; infer_instance

theorem State.exi_aWins_of_ind' {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, p sd → sys.tr sd (d.f sd) = some sa → p sa) :
(∃ (a : AStrat), a.WF ∧ s.aWins ⟨a, d⟩) ∧ p s := by
  suffices h₄ : ∃ (a : AStrat), a.WF ∧ s.aWins ⟨a, d⟩ ∧ p s; tauto
  use aSeek p, inferInstance
  apply aWins_of_ind' h₁; clear! s
  · intro sa ha H ih; dsimp
    specialize h₂ sa ih
    simp [aSeek, mkStratFn, choose?_eq_ite, h₂]
    generalize hp : Classical.epsilon
      (λ pa => ∃ sd, sys.tr sa pa = some sd ∧ p sd) = pa
    have h₄ := Classical.epsilon_spec h₂
    rw [hp] at h₄
    rcases h₄ with ⟨sd, h₄, h₅⟩
    simp [sys.validTr_of_eq_some h₄]
    use sd
  · intro sd hd sa H ih h₄; dsimp at h₄
    have ha := AState.of_tr h₄
    exact h₃ sd sa ih h₄

theorem State.exi_aWins_of_ind {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] {p : State → Prop} (h₁ : p s)
(h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧ p sd)
(h₃ : ∀ sd [DState sd] sa, p sd → sys.tr sd (d.f sd) = some sa → p sa) :
∃ (a : AStrat), a.WF ∧ s.aWins ⟨a, d⟩ :=
  s.exi_aWins_of_ind' h₁ h₂ h₃ |>.1

theorem State.aWins_iff_add {s st} (k : ℕ) :
s.aWins st ↔ ∀ n, (sys.simulate st.f s # k + n).2 = 0 := by
  constructor <;> intro h₁ n
  · exact h₁ # k + n
  · apply System.simulate_snd_eq_zero_of_le_and_eq_zero # h₁ n
    linarith

theorem State.dWins_iff_add {s st} (k : ℕ) :
s.dWins st ↔ ∃ n, (sys.simulate st.f s # k + n).2 ≠ 0 := by
  constructor <;> rintro ⟨n, h₁⟩
  · use n
    contrapose! h₁
    apply System.simulate_snd_eq_zero_of_le_and_eq_zero h₁
    linarith
  · use k + n

theorem State.length_hist_lt_of_tr {s s' p}
(h : sys.tr s p = some s') : s.hist.length < s'.hist.length := by
  simp [hist_eq_of_tr h]

theorem length_hist_sub_eq_of_simulate {s₀ s n f} [hs : sys.WF s₀]
(h : sys.simulate f s₀ n = (s, 0)) : s.hist.length - s₀.hist.length = n := by
  induction n generalizing s₀
  · simp at h; simp [h]
  nm n ih
  simp only [System.simulate_succ_full'] at h
  choose s' h₁ h using h
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
    exact System.reachable_of_simulate h
  have h₃ : s₀.hist.length < s'.hist.length
  · exact State.length_hist_lt_of_tr h₁
  omega

theorem AState.dHws_of_tr {sa sd p} [ha : AState sa]
(h₁ : sys.tr sa p = some sd) (h₂ : sa.dHws) : sd.dHws :=
  dHws_iff_tr.mp h₂ _ _ h₁

theorem DState.aHws_of_tr {sd sa p} [hd : DState sd]
(h₁ : sys.tr sd p = some sa) (h₂ : sd.aHws) : sa.aHws :=
  aHws_iff_tr.mp h₂ _ _ h₁

theorem State.dWins_of_lt_lt {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd < f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa < f sd) : s.dWins ⟨a, d⟩ := by
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
    rw [ne_def, sys.snd_simulate_add_one_eq_zero_iff']
    simpa [h₄]
  · have h₄ := d.validTr s
    obtain ⟨s', h₄⟩ := h₄
    have := AState.of_tr h₄
    obtain ⟨h₅, h₆⟩ := h₃ s s' h₁ h₄
    specialize ih (f s') h₆ h₅ rfl
    obtain ⟨n, ih⟩ := ih
    use n + 1
    rw [ne_def, sys.snd_simulate_add_one_eq_zero_iff']
    simpa [h₄]

theorem State.dWins_of_le_lt {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd ≤ f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa < f sd) : s.dWins ⟨a, d⟩ := by
  apply s.dWins_of_lt_lt (a := a) (d := d) (p := p)
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

theorem State.dWins_of_lt_le {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {p : State → Prop} {f : State → ℕ}
(h₁ : p s) (h₂ : ∀ sa sd [AState sa] [DState sd], p sa →
sys.tr sa (a.f sa) = some sd → p sd ∧ f sd < f sa)
(h₃ : ∀ sd sa [DState sd] [AState sa], p sd →
sys.tr sd (d.f sd) = some sa → p sa ∧ f sa ≤ f sd) : s.dWins ⟨a, d⟩ := by
  apply s.dWins_of_lt_lt (a := a) (d := d) (p := p)
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

theorem State.dWins_of_lt_lt_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd < f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa < f sd) :
s.dWins ⟨a, d⟩ := by
  have h₃ := s.dWins_of_lt_lt (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

theorem State.dWins_of_le_lt_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd ≤ f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa < f sd) :
s.dWins ⟨a, d⟩ := by
  have h₃ := s.dWins_of_le_lt (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

theorem State.dWins_of_lt_le_uncond {s} [hs : sys.WF s]
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF] {f : State → ℕ}
(h₁ : ∀ sa sd [AState sa] [DState sd], sys.tr sa (a.f sa) = some sd → f sd < f sa)
(h₂ : ∀ sd sa [DState sd] [AState sa], sys.tr sd (d.f sd) = some sa → f sa ≤ f sd) :
s.dWins ⟨a, d⟩ := by
  have h₃ := s.dWins_of_lt_le (a := a) (d := d) (p := λ _ => True) (f := f)
  simp only [true_and, forall_const] at h₃; exact h₃ h₁ h₂

theorem State.simulate_set_a_eq_of_length_hist_lt {s s₁ p₁ n} {a : AStrat} {d : DStrat}
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : s₁.hist.length < s.hist.length) :
sys.simulate (Strat.mk (a.set s₁ p₁) d).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ := a.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  exact length_hist_le_of_reachable # System.reachable_of_simulate h₅

theorem State.simulate_set_d_eq_of_length_hist_lt {s s₁ p₁ n} {a : AStrat} {d : DStrat}
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : s₁.hist.length < s.hist.length) :
sys.simulate (Strat.mk a (d.set s₁ p₁)).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ := d.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  exact length_hist_le_of_reachable # System.reachable_of_simulate h₅

theorem State.simulate_set_a_eq_of_le_length_hist_sub {s s₁ p₁ n} {a : AStrat} {d : DStrat}
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : n ≤ s₁.hist.length - s.hist.length) :
sys.simulate (Strat.mk (a.set s₁ p₁) d).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ := a.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  simpa [length_hist_eq_of_simulate_eq h₄]

theorem State.simulate_set_d_eq_of_le_length_hist_sub {s s₁ p₁ n} {a : AStrat} {d : DStrat}
[hs : sys.WF s] [hs₁ : sys.WF s₁] [ha : a.WF] [hd : d.WF]
(h₁ : sys.validTr s₁ p₁) (h₂ : n ≤ s₁.hist.length - s.hist.length) :
sys.simulate (Strat.mk a (d.set s₁ p₁)).f s n = sys.simulate (Strat.mk a d).f s n := by
  have h₃ := d.wf_set_of_validTr h₁; apply simulate_congr <;> simp
  intro k hk sa hsa h₄ h₅ h₆; rw [fn_set_eq_of_ne]; rintro rfl; contrapose! h₂
  simpa [length_hist_eq_of_simulate_eq h₄]