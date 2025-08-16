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

theorem AState.a_wins_of_ind {sa} [ha : AState sa]
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

theorem AState.ind {sa sa'} [ha : AState sa] [ha' : AState sa'] {p : State → Prop}
(h₁ : p sa) (h₂ : ∀ sa [AState sa] pa sd pd sa',
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

noncomputable
def mk_strat_fn (f : State → Option PointZ) : State → PointZ :=
  λ s => (Option.getD · (Classical.epsilon # sys.validTr s)) # do
    let p ← f s
    guard # sys.validTr s p
    return p

instance {f} : sys.SimFn # mk_strat_fn f := by
  constructor; intro s hs h; unfold mk_strat_fn
  have h₁ := Classical.epsilon_spec h; dsimp; cases h₂ : f s; simpa
  nm s'; simp [guard]; split_ifs with h₃; simpa; simpa

@[simp] noncomputable
def AStrat.mk' (f : State → Option PointZ) : AStrat := ⟨mk_strat_fn f⟩

@[simp] noncomputable
def DStrat.mk' (f : State → Option PointZ) : DStrat := ⟨mk_strat_fn f⟩

instance {f} : (AStrat.mk' f).WF := by simp; infer_instance
instance {f} : (DStrat.mk' f).WF := by simp; infer_instance

@[simp] theorem AStrat.f_mk {f} : (AStrat.mk f).f = f := rfl
@[simp] theorem DStrat.f_mk {f} : (DStrat.mk f).f = f := rfl

def aOptimalCnd (p : State → Prop) (sa : State) (pa : PointZ) : Prop :=
  ∃ sd, sys.tr sa pa = some sd ∧ ∀ pd sa', sys.tr sd pd = some sa' → p sa'

open Classical in noncomputable
def aOptimal (p : State → Prop) : AStrat :=
  .mk' # λ sa => choose? # aOptimalCnd p sa

theorem wf_aOptimal {p} : (aOptimal p).WF := by
  unfold aOptimal; infer_instance

instance {p} : (aOptimal p).WF := wf_aOptimal

theorem AState.a_hws_of_ind {sa : State} [ha : AState sa] {p : State → Prop}
(h₁ : p sa) (h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧
∀ pd sa', sys.tr sd pd = some sa' → p sa') : sa.a_hws := by
  classical
  use aOptimal p, inferInstance
  intro d hd
  apply ha.a_wins_of_ind h₁
  clear! sa
  intro sa ha hp
  specialize h₂ sa hp
  simp only [aOptimal, choose?_eq_ite]
  replace h₂ : ∃ pa, aOptimalCnd p sa pa := h₂
  have h₃ := Classical.epsilon_spec h₂
  generalize h₁ : Classical.epsilon (aOptimalCnd p sa) = pa at h₃ ⊢
  unfold aOptimalCnd at h₃
  obtain ⟨sd, h₃, h₄⟩ := h₃; use sd
  simp [-sys_tr_eq_some_iff, -validTr_iff, mk_strat_fn, h₂, h₁,
    System.validTr_iff_isSome, h₃]; apply h₄

theorem hist_eq_of_tr_eq_some {s s' p}
(h : sys.tr s p = some s') : s'.hist = p :: s.hist := by
  simp [sys, State.move] at h
  split_ifs at h with h₁ <;> simp at h <;> obtain ⟨s', h, rfl⟩ := h <;> rfl

@[simp]
theorem hist_trs {s ps} [hs : sys.WF s] : (sys.trs s ps).1.hist =
(ps.take # ps.length - (sys.trs s ps).2.length).reverse ++ s.hist := by
  induction ps generalizing s; rfl
  nm p ps ih
  simp
  split; simp
  nm x s' h₁; clear x
  have hs' := System.wf_of_tr h₁
  rw [ih]; clear ih
  replace h₁ := hist_eq_of_tr_eq_some h₁
  rw [h₁, List.append_cons, ←List.reverse_cons]; clear h₁
  generalize hn : (sys.trs s' ps).2.length = n
  have h₁ : n ≤ ps.length; subst hn; exact System.trs_snd_length_le
  rw [Nat.sub_add_comm h₁]; simp

instance {s} [hs : sys.WF s] : sys.Tree s := by
  rw [System.tree_iff_full_trs]
  use hs; intro ts₁ ts₂ s' h₁ h₂
  have h₃ := congrArg (·.1.hist) h₁
  have h₄ := congrArg (·.1.hist) h₂
  simp at h₃ h₄
  simp [h₂] at h₄
  simp [h₁, ←h₄] at h₃
  exact h₃

def getMoveFromHist (s_target s : State) : List PointZ → Option PointZ
| [] => none
| p :: ps => if s = s_target then some p else do
  let s' ← sys.tr s p
  getMoveFromHist s_target s' ps

def State.getMoveAt (s s_target : State) : Option PointZ :=
  getMoveFromHist s_target (initState s.pw) s.hist

noncomputable
def dOptimal (sa : State) : DStrat := .mk' # λ sd => do
  let pa ← sd.getMoveAt sa
  let sd' ← sys.tr sa pa
  none

#check 0 #exit

theorem AState.a_hws_of_not_d_hws {sa} [ha : AState sa] (h : ¬sa.d_hws) : sa.a_hws := by
  apply ha.a_hws_of_ind (p := (¬·.d_hws)) h; clear! sa
  intro sa ha h
  unfold State.d_hws at h ⊢
  contrapose h
  push_neg at h ⊢

#check 0 #exit

theorem State.a_hws_of_not_d_hws {s : State} [hs : s.WF] (h : ¬s.d_hws) : s.a_hws := by
  unfold d_hws at h; push_neg at h

#check 0 #exit

@[simp]
theorem State.not_a_hws_iff {s : State} [hs : s.WF] : ¬s.a_hws ↔ s.d_hws := by
  refine' ⟨λ h => _, s.not_a_hws_of_d_hws⟩
  contrapose! h; exact s.a_hws_of_not_d_hws h

@[simp]
theorem State.not_d_hws_iff_a_hws {s : State} [hs : s.WF] : ¬s.d_hws ↔ s.a_hws := by
  simp [not_iff_comm']