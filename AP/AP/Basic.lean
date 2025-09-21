import AP.AP.Defs

namespace AP

theorem AStrat.wf_def {a : AStrat} : a.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → s.aTurn → sys.validTr s (a.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem DStrat.wf_def {d : DStrat} : d.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → s.aTurn = false → sys.validTr s (d.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem Strat.wf_def {st : Strat} : st.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → sys.validTr s (st.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem Strat.wf_iff {st : Strat} : st.WF ↔ st.a.WF ∧ st.d.WF := by
  rw [Strat.wf_def, AStrat.wf_def, DStrat.wf_def]
  simp [System.hasTr, System.validTr, Strat.f]
  constructor
  · intro h
    constructor
    all_goals
      intro s hs p s' h₁ h₂
      specialize h _ _ h₁
      simp [h₂] at h
      exact h
  · rintro ⟨h₁, h₂⟩
    intro s hs p s' h₃
    split_ifs with h₄
    · exact h₁ _ _ h₃ h₄
    · simp at h₄; exact h₂ _ _ h₃ h₄

theorem Strat.WF.wf_a {st : Strat} [hst : st.WF] : st.a.WF := by
  rw [Strat.wf_iff] at hst; exact hst.1

theorem Strat.WF.wf_d {st : Strat} [hst : st.WF] : st.d.WF := by
  rw [Strat.wf_iff] at hst; exact hst.2

@[simp] instance {st : Strat} [hst : st.WF] : st.a.WF := hst.wf_a
@[simp] instance {st : Strat} [hst : st.WF] : st.d.WF := hst.wf_d

instance : Inhabited State := ⟨initState 0 0⟩

@[simp] theorem State.default_def : (default : State) = initState 0 0 := rfl

@[simp] instance : sys.WF default := by
  simp [System.wf_def, System.initial_def]; use default; simp [sys]

class AState (s : State) : Prop where
  wf : sys.WF s
  turn : s.aTurn

class DState (s : State) : Prop where
  wf : sys.WF s
  turn : s.aTurn = false

theorem AState.iff {s : State} : AState s ↔ sys.WF s ∧ s.aTurn :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem DState.iff {s : State} : DState s ↔ sys.WF s ∧ s.aTurn = false :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp] instance {sa} [ha : AState sa] : sys.WF sa := ha.wf
@[simp] instance {sd} [hd : DState sd] : sys.WF sd := hd.wf

@[simp] theorem AState.turn' {s : State} [hs : AState s] : s.aTurn := hs.turn
@[simp] theorem DState.turn' {s : State} [hs : DState s] : s.aTurn = false := hs.turn

def State.chooseDMove (s : State) : PointZ :=
  (insert s.aPos s.taken).max! + ⟨1, 0⟩

theorem State.validTr_iff_of_aTurn {s : State} {p} (ht : s.aTurn) :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.aMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.aMove, ht, h]

theorem State.validTr_iff_of_not_aTurn {s : State} {p} (ht : s.aTurn = false) :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken := by
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.dMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.dMove, ht, h]

theorem AState.validTr_iff {s : State} [hs : AState s] {p} :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  apply s.validTr_iff_of_aTurn; simp

theorem DState.validTr_iff {s : State} [hs : DState s] {p} :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken := by
  apply s.validTr_iff_of_not_aTurn; simp

theorem State.validTr_chooseDMove {s : State} (ht : s.aTurn = false) :
sys.validTr s s.chooseDMove := by
  rw [s.validTr_iff_of_not_aTurn ht]
  suffices h₁ : s.chooseDMove ∉ insert s.aPos s.taken
  · simp at h₁; rw [ne_comm]; exact h₁
  apply Set'.not_mem_of_max!_lt
  simp [State.chooseDMove, Point.zero_def]

@[simp]
theorem DState.validTr_chooseDMove {s : State} [hs : DState s] :
sys.validTr s s.chooseDMove :=  s.validTr_chooseDMove hs.turn

theorem State.hasTr_of_not_aTurn {s : State} (ht : s.aTurn = false) : sys.hasTr s := by
  use s.chooseDMove; exact s.validTr_chooseDMove ht

@[simp]
theorem DState.hasTr {s : State} [hs : DState s] : sys.hasTr s := by
  apply s.hasTr_of_not_aTurn; simp

def State.aMoves (s : State) : List PointZ :=
  s.aPos.nbhd s.pw |>.filter (sys.validTr s)

def State.aHasMove (s : State) : Bool :=
  s.aMoves ≠ []

theorem State.hasTr_iff_of_aTurn {s : State} (ht : s.aTurn) :
sys.hasTr s ↔ ∃ p, s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  simp [sys, System.hasTr_iff, move, aMove, ht]

@[simp]
theorem AState.hasTr_iff {s : State} [hs : AState s] :
sys.hasTr s ↔ ∃ p, s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  simp [s.hasTr_iff_of_aTurn]

theorem State.aHasMove_of_hasTr {s : State}
(ht : s.aTurn) (h : sys.hasTr s) : s.aHasMove := by
  simp [aHasMove, aMoves]; simp [sys.hasTr_iff] at h
  obtain ⟨p, s', h⟩ := h; use p; simp [h, Point.dist_comm]
  simp [sys, move, aMove, ht] at h; exact h.1.2.2

theorem State.hasTr_of_aHasMove {s : State} (ht : s.aTurn)
(h : s.aHasMove) : sys.hasTr s := by
  simp [aHasMove, aMoves, s.hasTr_iff_of_aTurn ht] at h ⊢
  simp [sys, move, aMove, ht] at h
  rcases h with ⟨p, h⟩; use p; tauto

theorem State.hasTr_iff_aHasMove {s : State} (ht : s.aTurn) :
sys.hasTr s ↔ s.aHasMove := ⟨s.aHasMove_of_hasTr ht, s.hasTr_of_aHasMove ht⟩

theorem State.WF.ind_turn {P : State → Prop}
(h₁ : ∀ (s : State), AState s → P s) (h₂ : ∀ (s : State), DState s → P s)
{s : State} (hs : sys.WF s) : P s := by
  cases ht : s.aTurn
  · apply h₂; constructor <;> assumption
  · apply h₁; constructor <;> assumption

@[simp]
def State.hasMove (s : State) : Bool :=
  if s.aTurn then s.aHasMove else true

theorem State.hasTr_iff_hasMove {s : State} : sys.hasTr s ↔ s.hasMove := by
  simp; cases ht : s.aTurn <;> simp
  · exact hasTr_of_not_aTurn ht
  · exact hasTr_iff_aHasMove ht

instance {s : State} : Decidable (sys.hasTr s) :=
  match h : s.hasMove with
  | true => .isTrue # by rwa [s.hasTr_iff_hasMove]
  | false => .isFalse # by rw [s.hasTr_iff_hasMove, h]; simp

def State.setHist (s : State) (hist : List PointZ) : State :=
  {s with hist := hist}

@[simp] theorem State.pw_setHist {s : State} {hist} :
(s.setHist hist).pw = s.pw := rfl

@[simp] theorem State.aPos_setHist {s : State} {hist} :
(s.setHist hist).aPos = s.aPos := rfl

@[simp] theorem State.aTurn_setHist {s : State} {hist} :
(s.setHist hist).aTurn = s.aTurn := rfl

@[simp] theorem State.taken_setHist {s : State} {hist} :
(s.setHist hist).taken = s.taken := rfl

@[simp] theorem State.hist_setHist {s : State} {hist} :
(s.setHist hist).hist = hist := rfl

@[simp]
theorem State.setHist_setHist {s : State} {hist₁ hist₂} :
(s.setHist hist₁).setHist hist₂ = s.setHist hist₂ := rfl

@[simp]
theorem State.setHist_eq_self_iff {s : State} {hist} :
s.setHist hist = s ↔ s.hist = hist := by
  simp [State.ext_iff, eq_comm]

@[simp]
theorem State.setHist_hist_self_eq_self {s : State} : s.setHist s.hist = s := rfl

@[simp]
instance {s hist} [hs : AState s] [hs' : sys.WF # s.setHist hist] :
AState # s.setHist hist := ⟨hs', by simp⟩

@[simp]
instance {s hist} [hs : DState s] [hs' : sys.WF # s.setHist hist] :
DState # s.setHist hist := ⟨hs', by simp⟩

def State.setPw (s : State) (pw : ℕ) : State :=
  {s with pw := pw}

@[simp] theorem State.pw_setPw {s : State} {pw} : (s.setPw pw).pw = pw := rfl
@[simp] theorem State.aPos_setPw {s : State} {pw} : (s.setPw pw).aPos = s.aPos := rfl
@[simp] theorem State.aTurn_setPw {s : State} {pw} : (s.setPw pw).aTurn = s.aTurn := rfl
@[simp] theorem State.taken_setPw {s : State} {pw} : (s.setPw pw).taken = s.taken := rfl
@[simp] theorem State.hist_setPw {s : State} {pw} : (s.setPw pw).hist = s.hist := rfl

@[simp]
theorem State.setPw_setPw {s : State} {pw₁ pw₂} :
(s.setPw pw₁).setPw pw₂ = s.setPw pw₂ := rfl

@[simp]
theorem State.setPw_eq_self_iff {s : State} {pw} : s.setPw pw = s ↔ s.pw = pw := by
  simp [State.ext_iff, eq_comm]

@[simp]
theorem State.setPw_pw_self_eq_self {s : State} : s.setPw s.pw = s := rfl

theorem AState.validTr_of_le {s : State} [hs : AState s] {pw p}
(h₁ : s.pw ≤ pw) (h₂ : sys.validTr s p) : sys.validTr (s.setPw pw) p := by
  simp [hs.validTr_iff] at h₂; rcases h₂ with ⟨h₂, h₃, h₄⟩
  simp [System.validTr, sys, State.move, State.aMove]
  use h₂, h₃; linarith

theorem AState.hasTr_of_le {s : State} [hs : AState s] {pw}
(h₁ : s.pw ≤ pw) (h₂ : sys.hasTr s) : sys.hasTr (s.setPw pw) := by
  obtain ⟨p, h₃⟩ := h₂; use p; exact hs.validTr_of_le h₁ h₃

@[simp]
theorem State.not_aWins_iff {s : State} {st : Strat} : ¬s.aWins st ↔ s.dWins st := by
  simp [aWins, dWins]

@[simp]
theorem State.not_dWins_iff {s : State} {st : Strat} : ¬s.dWins st ↔ s.aWins st := by
  simp [aWins, dWins]

theorem AStrat.wf_iff {a : AStrat} : a.WF ↔ ∀ {s} [AState s],
sys.hasTr s → sys.validTr s (a.f s) := by
  simp [AState.iff, AStrat.wf_def]; tauto

theorem DStrat.wf_iff {d : DStrat} : d.WF ↔ ∀ s [DState s], sys.validTr s (d.f s) := by
  simp [DState.iff, DStrat.wf_def]
  apply forall_iff_of; intro s
  apply forall_iff_of; intro hs
  simp; rw [or_iff_not_imp_left]
  intro h₁ h₂
  replace hs : DState s; use hs
  simp at h₁

theorem State.tr_eq_some_iff_of_aTurn {s : State} {s' p} (ht : s.aTurn) :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw) ∧
{s with aPos := p, aTurn := false, hist := p :: s.hist} = s' := by
  simp [sys, State.move, State.aMove, ht]

theorem State.tr_eq_some_iff_of_not_aTurn {s : State} {s' p} (ht : s.aTurn = false) :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken) ∧
{s with taken := s.taken.insert p, aTurn := true, hist := p :: s.hist} = s' := by
  simp [sys, State.move, State.dMove, ht]

@[simp]
theorem AState.tr_eq_some_iff {s s' p} [hs : AState s] :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw) ∧
{s with aPos := p, aTurn := false, hist := p :: s.hist} = s' :=
  s.tr_eq_some_iff_of_aTurn turn

@[simp]
theorem DState.tr_eq_some_iff {s s' p} [hs : DState s] :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken) ∧
{s with taken := s.taken.insert p, aTurn := true, hist := p :: s.hist} = s' :=
  s.tr_eq_some_iff_of_not_aTurn turn

@[simp]
theorem AState.strat_f_eq {sa} {st : Strat} [ha : AState sa] :
st.f sa = st.a.f sa := by simp [Strat.f]

@[simp]
theorem DState.strat_f_eq {sd} {st : Strat} [hd : DState sd] :
st.f sd = st.d.f sd := by simp [Strat.f]

theorem State.aWins_iff_mul_two {s : State} {st : Strat} :
s.aWins st ↔ ∀ n, (sys.simulate st.f s # n * 2).2 = 0 := by
  constructor <;> intro h n; apply h
  apply System.simulate_snd_eq_zero_of_le_and_eq_zero # h n; simp

@[simp]
theorem DState.tr_ne_none {sd} [hd : DState sd] {st : DStrat} [hst : st.WF] :
sys.tr sd (st.f sd) ≠ none := by
  have h₁ := hd.hasTr
  rw [DStrat.wf_iff] at hst
  obtain ⟨sa, h₂⟩ := @hst sd _
  simp [h₂]

@[simp]
instance {st : Strat} [hst : st.WF] : sys.SimFn st.f := by
  rw [Strat.wf_def] at hst; exact ⟨hst⟩

theorem AState.of_tr {sa sd p} [hd : DState sd]
(h : sys.tr sd p = some sa) : AState sa := by
  use System.wf_of_tr h; simp at h; simp [←h.2]

theorem DState.of_tr {sa sd p} [ha : AState sa]
(h : sys.tr sa p = some sd) : DState sd := by
  use System.wf_of_tr h; simp at h; simp [←h.2]

theorem AState.of_tr' {sa sd p} [ha : sys.WF sa] [hd : DState sd]
(h : sys.tr sa p = some sd) : AState sa := by
  by_cases ht : sa.aTurn; exact ⟨ha, ht⟩
  simp at ht; simp [sys, State.move, ht] at h
  obtain ⟨s, h₁, rfl⟩ := h
  have h₂ := hd.turn
  simp at h₂

theorem DState.of_tr' {sa sd p} [hd : sys.WF sd] [ha : AState sa]
(h : sys.tr sd p = some sa) : DState sd := by
  by_cases ht : sd.aTurn = false; exact ⟨hd, ht⟩
  simp at ht; simp [sys, State.move, ht] at h
  obtain ⟨s, h₁, rfl⟩ := h
  have h₂ := ha.turn
  simp at h₂

@[simp]
theorem AState.not_dState {sa} [ha : AState sa] : ¬DState sa := by
  intro hd; have h := ha.turn; rw [hd.turn] at h; simp at h

@[simp]
theorem DState.not_aState {sd} [hd : DState sd] : ¬AState sd := by
  intro ha; simp at hd

instance {a : AStrat} {d : DStrat} [ha : a.WF] [hd : d.WF] : Strat.WF ⟨a, d⟩ := by
  rw [Strat.wf_iff]; exact ⟨ha, hd⟩

instance {f} [hf : sys.SimFn f] : AStrat.WF ⟨f⟩ := by
  rw [AStrat.wf_iff]; rw [System.simFn_def] at hf
  rintro s ⟨hs, ht⟩; apply hf

instance {f} [hf : sys.SimFn f] : DStrat.WF ⟨f⟩ := by
  rw [DStrat.wf_iff]; rw [System.simFn_def] at hf
  rintro s ⟨hs, ht⟩; apply hf
  replace hs : DState s; use hs
  simp

theorem State.aState_or_dState {s} [hs : sys.WF s] : AState s ∨ DState s := by
  simp [AState.iff, DState.iff, hs]

theorem AStrat.WF.validTr {s} [hs : AState s] {st : AStrat} [hst : st.WF]
(h : sys.hasTr s) : sys.validTr s (st.f s) := by
  rw [AStrat.wf_iff] at hst; exact hst h

@[simp]
theorem DStrat.WF.validTr (s : State) [hs : DState s] {st : DStrat} [hst : st.WF] :
sys.validTr s (st.f s) := by
  rw [DStrat.wf_iff] at hst; apply hst

theorem AStrat.validTr {s} [hs : AState s] {st : AStrat} [hst : st.WF]
(h : sys.hasTr s) : sys.validTr s (st.f s) := hst.validTr h

@[simp]
theorem DStrat.validTr (s : State) [hs : DState s] {st : DStrat} [hst : st.WF] :
sys.validTr s (st.f s) := hst.validTr s

theorem Strat.WF.validTr {s} [hs : sys.WF s] {st : Strat} [hst : st.WF]
(h : sys.hasTr s) : sys.validTr s (st.f s) := by
  rw [Strat.wf_def] at hst; exact hst h

def State.chooseAMove (s : State) : PointZ :=
  s.aPos.nbhd s.pw |>.filter (sys.validTr s) |>.head?.getD 0

theorem State.validTr_chooseAMove {s : State} (ht : s.aTurn)
(h : sys.hasTr s) : sys.validTr s s.chooseAMove := by
  generalize hp : s.chooseAMove = p
  unfold chooseAMove Option.getD at hp
  split at hp; rotate_left
  · nm x h₁; clear x
    subst hp
    simp at h₁
    obtain ⟨p, s', h₂⟩ := h
    specialize h₁ p
    have H := h₂
    simp [sys, move, aMove, ht] at h₂
    replace h₂ := h₂.1
    rcases h₂ with ⟨h₂, h₃, h₄⟩
    rw [Point.dist_comm] at h₄
    specialize h₁ h₄
    simp [h₁] at H
  nm x p h₁; clear x; subst hp
  simp at h₁
  replace h₁ := List.find?_some h₁
  simp at h₁
  exact h₁

@[simp]
theorem AState.validTr_chooseAMove {s : State} [hs : AState s]
(h : sys.hasTr s) : sys.validTr s s.chooseAMove :=
  s.validTr_chooseAMove hs.turn h

def State.chooseMove (s : State) : PointZ :=
  if s.aTurn then s.chooseAMove else s.chooseDMove

@[simp]
theorem State.validTr_chooseMove {s : State}
(h : sys.hasTr s) : sys.validTr s s.chooseMove := by
  cases ht : s.aTurn <;> simp [chooseMove, ht]
  · exact validTr_chooseDMove ht
  · exact validTr_chooseAMove ht h

@[simp]
theorem AState.chooseMove_eq {s} [hs : AState s] :
s.chooseMove = s.chooseAMove := by simp [State.chooseMove]

@[simp]
theorem DState.chooseMove_eq {s} [hs : DState s] :
s.chooseMove = s.chooseDMove := by simp [State.chooseMove]

instance : Inhabited AStrat := ⟨⟨State.chooseAMove⟩⟩
instance : Inhabited DStrat := ⟨⟨State.chooseDMove⟩⟩
instance : Inhabited Strat := ⟨default, default⟩

@[simp] theorem AStrat.default_def : (default : AStrat) = ⟨State.chooseAMove⟩ := rfl
@[simp] theorem DStrat.default_def : (default : DStrat) = ⟨State.chooseDMove⟩ := rfl

@[simp] theorem Strat.default_def : (default : Strat) =
⟨⟨State.chooseAMove⟩, ⟨State.chooseDMove⟩⟩ := rfl

instance : AStrat.WF ⟨State.chooseAMove⟩ := by
  constructor; intro s hs h₁ ht; simp; exact s.validTr_chooseAMove ht h₁

instance : DStrat.WF ⟨State.chooseDMove⟩ := by
  constructor; intro s hs h₁ ht; simp; exact s.validTr_chooseDMove ht

instance : (default : AStrat).WF := by simp; infer_instance
instance : (default : DStrat).WF := by simp; infer_instance
instance : (default : Strat).WF := by simp; infer_instance

theorem pw_eq_of_tr {s s' p} (h : sys.tr s p = some s') : s'.pw = s.pw := by
  simp [sys, State.move, State.aMove, State.dMove] at h
  split_ifs at h with h₁ <;> simp at h <;> rcases h with ⟨s', h, rfl⟩ <;> rfl

@[simp]
theorem pw_initState {pw p} : (initState pw p).pw = pw := rfl

def State.aPos₀ (s : State) : PointZ :=
  s.hist.getLast?.iget

theorem hist_eq_of_tr {s s' p}
(h : sys.tr s p = some s') : s'.hist = p :: s.hist := by
  simp [sys, State.move] at h
  split_ifs at h with h₁ <;> simp at h <;> obtain ⟨s', h, rfl⟩ := h <;> rfl

theorem length_hist_eq_of_tr {s s₁ p} (h : sys.tr s p = some s₁) :
s₁.hist.length = s.hist.length + 1 := by simp [hist_eq_of_tr h]

theorem hist_suffix_of_reachable {s₁ s₂ : State}
(h : sys.Reachable s₁ s₂) : s₁.hist <:+ s₂.hist := by
  induction h; rfl
  clear s₂
  nm a b c p h₁ h₂ ih
  trans b.hist
  rotate_left; exact ih
  clear ih
  rw [hist_eq_of_tr h₁]
  simp

theorem length_hist_le_of_reachable {s₁ s₂ : State}
(h : sys.Reachable s₁ s₂) : s₁.hist.length ≤ s₂.hist.length :=
  hist_suffix_of_reachable h |>.length_le

theorem hist_suffix_of_tr {s₁ s₂ : State} {p}
(h : sys.tr s₁ p = some s₂) : s₁.hist <:+ s₂.hist :=
  hist_suffix_of_reachable # System.reachable_of_tr h

theorem length_hist_le_of_tr {s₁ s₂ : State} {p}
(h : sys.tr s₁ p = some s₂) : s₁.hist.length ≤ s₂.hist.length :=
  hist_suffix_of_tr h |>.length_le

@[simp]
theorem hist_initState {pw p} : (initState pw p).hist = [p] := rfl

@[simp]
theorem State.hist_ne_nil {s} [hs : sys.WF s] : s.hist ≠ [] := by
  obtain ⟨s₀, h₁, h₂⟩ := hs
  replace h₁ := h₁.1
  simp [sys] at h₁
  obtain ⟨pw, p, rfl⟩ := h₁
  have h₁ := hist_suffix_of_reachable h₂
  intro h₃
  rw [h₃] at h₁
  simp at h₁

@[simp]
theorem Option.getD_eq_iget_iff {α : Type*} [ha : Inhabited α] {m : Option α} {x} :
m.getD x = m.iget ↔ m.isSome ∨ x = default := by
  cases m <;> simp

theorem State.aPos₀_eq_of_tr {s s' t} [hs : sys.WF s]
(h : sys.tr s t = some s') : s'.aPos₀ = s.aPos₀ := by
  replace hs := s.aState_or_dState; rcases hs with hs | hs <;> simp at h
  · rcases h with ⟨⟨h₁, h₂, h₃⟩, rfl⟩; simp [aPos₀, List.getLast?_cons]
  · rcases h with ⟨⟨h₁, h₂⟩, rfl⟩; simp [aPos₀, List.getLast?_cons]

theorem State.aPos₀_eq_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : s'.aPos₀ = s.aPos₀ := by
  apply sys.invariant_val (f := aPos₀) h
  intro s s' p hs hs'; exact aPos₀_eq_of_tr

@[simp]
theorem initial_iff {s} : sys.Initial s ↔ initState s.pw s.aPos₀ = s := by
  simp [System.initial_def, sys]; constructor
  · rintro ⟨pw, p, h⟩; subst h; rfl
  · intro h; use s.pw, s.aPos₀

@[simp]
theorem pw_trs {s ps} [hs : sys.WF s] : (sys.trs s ps).1.pw = s.pw := by
  induction ps generalizing s; rfl
  nm p ps ih
  simp; split; rfl
  nm x s' h₁; clear x
  have h₂ := System.wf_of_tr h₁
  rw [ih, pw_eq_of_tr h₁]

theorem pw_eq_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : s'.pw = s.pw := by
  rw [System.reachable_iff_exi_trs] at h; obtain ⟨ts, h⟩ := h
  replace h := congrArg (·.1.pw) h; simp at h; rw [h]

@[simp]
theorem aPos₀_initState {pw p} : (initState pw p).aPos₀ = p := rfl

@[simp]
theorem aPos_initState {pw p} : (initState pw p).aPos = p := rfl

@[simp]
theorem taken_initState {pw p} : (initState pw p).taken = ∅ := rfl

theorem State.wf_iff {s} : sys.WF s ↔ ∃ ps,
sys.trs (initState s.pw s.aPos₀) ps = (s, []) := by
  simp [System.wf_def, System.reachable_iff_exi_trs]
  constructor
  · rintro ⟨s₁, h₁, ps, h₂⟩
    have hs₁ : sys.WF s₁
    · have hs₁ : sys.Initial s₁; simpa; infer_instance
    use ps
    have h₃ := congrArg (·.1.pw) h₂
    simp at h₃
    have hs := System.wf_of_trs h₂
    have h₄ : s.aPos₀ = s₁.aPos₀ :=
      aPos₀_eq_of_reachable # sys.reachable_of_trs' h₂
    simpa [h₄, ←h₃, h₁]
  · rintro ⟨ps, h₁⟩
    use initState s.pw s.aPos₀
    simp; use ps

@[simp] instance {pw p} : sys.Initial # initState pw p := by simp

@[simp]
theorem setPw_initState {p pw₁ pw₂} :
(initState pw₁ p).setPw pw₂ = initState pw₂ p := rfl

theorem State.tr_setPw_eq_some_of {s s' pw p} [hs : sys.WF s]
(h₁ : s.pw ≤ pw) (h₂ : sys.tr s p = some s') :
sys.tr (s.setPw pw) p = some (s'.setPw pw) := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs <;> simp at h₂
  · rcases h₂ with ⟨⟨h₂, h₃, h₄⟩, rfl⟩
    have h₅ : (s.setPw pw).aTurn; simp
    simp [tr_eq_some_iff_of_aTurn h₅, State.ext_iff, h₂, h₃]
    linarith
  · rcases h₂ with ⟨⟨h₂, h₃⟩, rfl⟩
    have h₅ : (s.setPw pw).aTurn = false; simp
    simp [tr_eq_some_iff_of_not_aTurn h₅, State.ext_iff, h₂, h₃]

theorem State.trs_setPw_eq_of {s s' pw ps} [hs : sys.WF s]
(h₁ : s.pw ≤ pw) (h₂ : sys.trs s ps = (s', [])) :
sys.trs (s.setPw pw) ps = (s'.setPw pw, []) := by
  induction ps generalizing s
  · simp at h₂; simp [h₂]
  nm p ps ih
  simp at h₂
  split at h₂; simp at h₂
  nm x s₁ h₃; clear x
  simp [tr_setPw_eq_some_of h₁ h₃]
  have h₄ := System.wf_of_tr h₃
  refine' ih _ h₂
  rwa [pw_eq_of_tr h₃]

theorem State.wf_setPw_of_le {s pw} [hs : sys.WF s]
(h : s.pw ≤ pw) : sys.WF (s.setPw pw) := by
  have H := hs
  rw [wf_iff] at hs ⊢; dsimp
  obtain ⟨ps, h₁⟩ := hs; use ps
  have h₂ : (initState s.pw s.aPos₀).pw ≤ pw; simpa
  have h₃ := trs_setPw_eq_of h₂ h₁
  simp at h₃
  exact h₃

theorem DState.tr_setPw_eq {s p pw} [hs : DState s] :
sys.tr (s.setPw pw) p = (sys.tr s p).map (·.setPw pw) := by
  ext s' :1; simp [State.tr_eq_some_iff_of_not_aTurn]; intros; rfl

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
  replace h₁ := hist_eq_of_tr h₁
  rw [h₁, List.append_cons, ←List.reverse_cons]; clear h₁
  generalize hn : (sys.trs s' ps).2.length = n
  have h₁ : n ≤ ps.length; subst hn; exact System.trs_snd_length_le
  rw [Nat.sub_add_comm h₁]; simp

@[simp]
theorem length_hist_eq_one_iff {s} [hs : sys.WF s] :
s.hist.length = 1 ↔ initState s.pw s.aPos₀ = s := by
  refine' ⟨λ h => _, λ h => by rw [←h]; rfl⟩
  obtain ⟨ps, h₁⟩ := s.wf_iff.mp hs
  have h₂ := congrArg (·.1.hist) h₁
  simp at h₂
  simp [h₁] at h₂
  replace h : s.hist = [s.aPos₀]
  · cases h₁ : s.hist; simp at h₁; nm p ps
    simp [h₁] at h
    subst h
    simp at h₁ ⊢
    simp [State.aPos₀, h₁]
  simp [h] at h₂
  subst h₂
  simp at h₁
  exact h₁

theorem exi_prev_of_hist_eq_cons {s p ps} [hs : sys.WF s]
(h₁ : ps ≠ []) (h₂ : s.hist = p :: ps) : ∃ s₀, sys.WF s₀ ∧ sys.tr s₀ p = s := by
  rename' h₁ => H, h₂ => h
  obtain ⟨ps', h₁⟩ := State.wf_iff.mp hs
  induction ps' using List.reverseRecOn
  · simp at h₁
    rw [←h₁] at h
    simp [H] at h
  nm ps' p' ih; clear ih
  simp [System.trs_append] at h₁
  split_ifs at h₁ with h₂ <;> simp at h₁
  split at h₁ <;> simp at h₁
  nm x s₁ h₃; clear x
  rcases h₁ with ⟨rfl, h₁⟩
  clear h₂
  generalize hr : sys.trs (initState s₁.pw s₁.aPos₀) ps' = r at h₁ h₃
  rcases r with ⟨b, ps₁⟩
  subst h₁
  dsimp at h₃
  use b, System.wf_of_trs hr
  have h₄ := hist_eq_of_tr h₃
  simp [h] at h₄
  simpa [h₄.1]

@[simp]
theorem aTurn_initState {pw p} : (initState pw p).aTurn = false := rfl

@[simp]
theorem initState_eq_initState_iff {pw₁ p₁ pw₂ p₂} :
initState pw₁ p₁ = initState pw₂ p₂ ↔ pw₁ = pw₂ ∧ p₁ = p₂ := by
  simp [State.ext_iff]

@[simp]
theorem hist_eq_singleton_iff {s} [hs : sys.WF s] {p} :
s.hist = [p] ↔ initState s.pw p = s ∧ s.aPos₀ = p := by
  constructor
  · intro h
    have h₁ : s.hist.length = 1; simp [h]
    rw [length_hist_eq_one_iff] at h₁
    nth_rw 2 [←h₁]
    rw [←h₁] at h
    simp at h
    simp [h]
  · rintro ⟨h, rfl⟩
    nth_rw 1 [←h]
    rfl

-- #check 0 #exit

@[simp]
theorem State.trs_reverse_hist_eq {s} [hs : sys.WF s] :
sys.trs (initState s.pw s.aPos₀) s.hist.reverse.tail = (s, []) := by
  generalize hp : s.hist = ps
  induction ps generalizing s
  · simp at hp
  nm p ps ih
  simp
  by_cases H : ps = []
  · subst H
    simp at hp
    simp [hp]
  obtain ⟨s₀, hs₁, h₂⟩ := exi_prev_of_hist_eq_cons H hp
  have h₃ := hist_eq_of_tr h₂
  simp [hp] at h₃
  symm at h₃
  specialize ih h₃
  rw [List.tail_append_of_ne_nil # by simp [H]]
  rw [pw_eq_of_tr h₂, aPos₀_eq_of_tr h₂]
  simp [-List.tail_reverse, sys.trs_append, ih, h₂]

theorem State.eq_trs_reverse_hist {s} [hs : sys.WF s] :
s = (sys.trs (initState s.pw s.aPos₀) s.hist.reverse.tail).1 := by
  rw [trs_reverse_hist_eq]

def State.decideWF (s : State) : Bool :=
  sys.trs (initState s.pw s.aPos₀) s.hist.reverse.tail = (s, [])

def State.decideAState (s : State) : Bool :=
  s.decideWF && s.aTurn

def State.decideDState (s : State) : Bool :=
  s.decideWF && !s.aTurn

theorem State.wf_iff_decideWF {s} : sys.WF s ↔ s.decideWF := by
  unfold decideWF; constructor <;> intro h <;> simp [-List.tail_reverse] at h ⊢
  rw [State.wf_iff]; use s.hist.reverse.tail

instance {s} : Decidable # sys.WF s :=
  match h : s.decideWF with
  | true => .isTrue # by simp [State.wf_iff_decideWF, h]
  | false => .isFalse # by simp [State.wf_iff_decideWF, h]

@[simp]
theorem State.decideWF_eq {s} : s.decideWF = decide (sys.WF s) := by
  simp [wf_iff_decideWF]

theorem State.aState_iff_decideAState {s} : AState s ↔ s.decideAState := by
  simp [decideAState, AState.iff]

theorem State.dState_iff_decideDState {s} : DState s ↔ s.decideDState := by
  simp [decideDState, DState.iff]

instance {s} : Decidable # AState s :=
  match h : s.decideAState with
  | true => .isTrue # by simp [State.aState_iff_decideAState, h]
  | false => .isFalse # by simp [State.aState_iff_decideAState, h]

instance {s} : Decidable # DState s :=
  match h : s.decideDState with
  | true => .isTrue # by simp [State.dState_iff_decideDState, h]
  | false => .isFalse # by simp [State.dState_iff_decideDState, h]

@[simp]
theorem State.decideAState_eq {s} : s.decideAState = decide (AState s) := by
  simp [aState_iff_decideAState]

@[simp]
theorem State.decideDState_eq {s} : s.decideDState = decide (DState s) := by
  simp [dState_iff_decideDState]

@[simp]
theorem State.not_aState {s} [hs : sys.WF s] : ¬AState s ↔ DState s := by
  simp [AState.iff, DState.iff]; aesop

@[simp]
theorem State.not_dState {s} [hs : sys.WF s] : ¬DState s ↔ AState s := by
  simp [AState.iff, DState.iff]; aesop

theorem AState.validTr_of_aWins {s} {st : Strat} [hs : AState s]
(h : s.aWins st) : sys.validTr s (st.a.f s) := by
  specialize h 1
  simp at h
  split at h; simp at h
  nm x s' h₁; clear x
  exact System.validTr_of_eq_some h₁

theorem AState.hasTr_of_aWins {s} {st : Strat} [hs : AState s]
(h : s.aWins st) : sys.hasTr s :=
  System.hasTr_of_validTr # validTr_of_aWins h

theorem setPw_eq_comm {s₁ s₂ : State} :
s₁.setPw s₂.pw = s₂ ↔ s₂.setPw s₁.pw = s₁ := by
  simp [State.ext_iff]; tauto

theorem setHist_eq_comm {s₁ s₂ : State} :
s₁.setHist s₂.hist = s₂ ↔ s₂.setHist s₁.hist = s₁ := by
  simp [State.ext_iff]; tauto

@[simp]
theorem setHist_eq_setHist_iff {s : State} {hist₁ hist₂} :
s.setHist hist₁ = s.setHist hist₂ ↔ hist₁ = hist₂ := by
  simp [State.ext_iff]

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

@[simp]
theorem State.chooseAMove_setHist {s : State} {hist} :
(s.setHist hist).chooseAMove = s.chooseAMove := by
  simp [chooseAMove]

@[simp]
theorem State.chooseDMove_setHist {s : State} {hist} :
(s.setHist hist).chooseDMove = s.chooseDMove := by
  simp [chooseDMove]

theorem State.setHist_eq_self_of {s : State} {hist}
(h : s.hist = hist) : s.setHist hist = s := by
  simp [←h]

theorem AState.exi_prev {sa} [ha : AState sa] :
∃ sd p, sys.tr sd p = sa := by
  rcases ha with ⟨h₁, h₂⟩
  rw [State.wf_iff] at h₁
  obtain ⟨ps, h₁⟩ := h₁
  induction ps using List.reverseRecOn generalizing sa
  · simp at h₁
    rw [←h₁] at h₂
    simp at h₂
  nm ps p ih
  clear ih
  generalize hr : sys.trs (initState sa.pw sa.aPos₀) ps = r
  simp [sys.trs_append, hr] at h₁
  split at h₁ <;> simp at h₁
  nm h₃
  rcases h₁ with ⟨h₁, h₄⟩
  split at h₄ <;> simp at h₄
  nm x sa' h₅; clear x
  clear h₄
  simp [h₅] at h₁
  subst h₁
  rcases r with ⟨s, r⟩
  simp at h₃ h₅
  subst h₃
  use s, p

theorem State.aTurn_eq_of_tr {s s' p} (h : sys.tr s p = some s') : s'.aTurn = !s.aTurn := by
  simp [sys, move] at h; split_ifs at h with h₁
  all_goals simp [h₁]; simp at h; obtain ⟨s₁, h₂, rfl⟩ := h; simp [h₁]

theorem State.aTurn_eq_of_simulate_eq {st : Strat} {s s₁ n r}
[hs : sys.WF s] (h : sys.simulate st.f s n = (s₁, r)) :
s₁.aTurn = (s.aTurn == decide (Even # n - r)) := by
  induction n generalizing s
  · simp at h ⊢; simp [h]
  nm n ih
  simp at h
  split at h
  · nm x h₁; clear x; simp at h; simp [h]
  nm x s' h₁; clear x
  have h₂ := sys.wf_of_tr h₁
  rw [ih h, aTurn_eq_of_tr h₁]; clear ih
  simp only [beq_eq_beq, Bool.not_eq_eq_eq_not]
  rw [Nat.succ_sub # sys.snd_le_of_simulate_eq h]
  simp only [Nat.succ_eq_add_one, Nat.even_succ_iff]
  simp_rw [←Nat.not_even_iff_odd]
  simp [-Nat.not_even_iff_odd]

theorem State.aTurn_eq_of_simulate_full_eq {st : Strat} {s s₁ n}
[hs : sys.WF s] (h : sys.simulate st.f s n = (s₁, 0)) :
s₁.aTurn = (s.aTurn == decide (Even n)) :=
  aTurn_eq_of_simulate_eq h

theorem State.simulate_congr_rel_full'
{st st' : Strat} {r : State → State → Prop} {s s' s₁ n}
[hst : st.WF] [hst' : st'.WF] [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : sys.simulate st.f s n = (s₁, 0)) (ht : s.aTurn = s'.aTurn) (h₂ : r s s')
(h₃ : ∀ sa sa' sd [AState sa] [AState sa'] [DState sd],
sys.tr sa (st.a.f sa) = some sd → r sa sa' →
∃ sd', sys.tr sa' (st'.a.f sa') = some sd' ∧ r sd sd')
(h₄ : ∀ sd sd' sa [DState sd] [DState sd'] [AState sa],
sys.tr sd (st.d.f sd) = some sa → r sd sd' →
∃ sa', sys.tr sd' (st'.d.f sd') = some sa' ∧ r sa sa') :
∃ s₁', sys.simulate st'.f s' n = (s₁', 0) ∧ r s₁ s₁' := by
  apply sys.simulate_congr_rel_full (r := r) h₁ h₂
  intro k hk b b' b₁ h₅ h₆ h₇ h₈
  have hb : sys.WF b := sys.wf_of_simulate_eq h₅
  have hb' : sys.WF b' := sys.wf_of_simulate_eq h₆
  have H₁ : b.aTurn = b'.aTurn
  · rw [aTurn_eq_of_simulate_full_eq h₅, aTurn_eq_of_simulate_full_eq h₆, ht]
  replace hb := b.aState_or_dState
  rcases hb with hb | hb <;> simp [-AState.tr_eq_some_iff, -DState.tr_eq_some_iff] at h₈
  · replace hb' : AState b' := ⟨hb', by simp [←H₁]⟩
    have H₂ := DState.of_tr h₈; specialize h₃ b b' b₁ h₈ h₇
    simpa [-AState.tr_eq_some_iff]
  · replace hb' : DState b' := ⟨hb', by simp [←H₁]⟩
    have H₂ := AState.of_tr h₈; specialize h₄ b b' b₁ h₈ h₇
    simpa [-DState.tr_eq_some_iff]

theorem State.simulate_congr_rel_full
{st st' : Strat} {r : State → State → Prop} {s s' n}
[hst : st.WF] [hst' : st'.WF] [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : (sys.simulate st.f s n).2 = 0) (ht : s.aTurn = s'.aTurn) (h₂ : r s s')
(h₃ : ∀ sa sa' sd [AState sa] [AState sa'] [DState sd],
sys.tr sa (st.a.f sa) = some sd → r sa sa' →
∃ sd', sys.tr sa' (st'.a.f sa') = some sd' ∧ r sd sd')
(h₄ : ∀ sd sd' sa [DState sd] [DState sd'] [AState sa],
sys.tr sd (st.d.f sd) = some sa → r sd sd' →
∃ sa', sys.tr sd' (st'.d.f sd') = some sa' ∧ r sa sa') :
(sys.simulate st'.f s' n).2 = 0 := by
  obtain ⟨s₁, h₁⟩ : ∃ s₁, sys.simulate st.f s n = (s₁, 0); simpa [Prod.ext_iff]
  obtain ⟨s₁', h₅⟩ := s.simulate_congr_rel_full' h₁ ht h₂ h₃ h₄; simp [h₅]

theorem AState.validTr_setPw_of_le {s pw p} [hs : sys.WF s]
(h₁ : s.pw ≤ pw) (h₂ : sys.validTr s p) : sys.validTr (s.setPw pw) p := by
  obtain ⟨s', h₂⟩ := h₂; exact ⟨_, State.tr_setPw_eq_some_of h₁ h₂⟩

theorem State.setPw_eq_self_of {s : State} {pw}
(h : s.pw = pw) : s.setPw pw = s := by
  simp [←h]

theorem AState.setPw_of_le {s pw} [hs : AState s]
(h : s.pw ≤ pw) : AState (s.setPw pw) := by
  constructor <;> simp [State.wf_setPw_of_le h]

theorem DState.setPw_of_le {s pw} [hs : DState s]
(h : s.pw ≤ pw) : DState (s.setPw pw) := by
  constructor <;> simp [State.wf_setPw_of_le h]

instance {pw p} : DState (initState pw p) := by
  use inferInstance; rfl

instance {pw pw' p} : DState # (initState pw p).setPw pw' := by
  simp; infer_instance

@[simp]
def mk_strat_fn (f : State → Option PointZ) (s : State) : PointZ :=
  (·.getD s.chooseMove) # do
    let p ← f s
    guard # sys.validTr s p
    return p

instance {f} : sys.SimFn # mk_strat_fn f := by
  constructor; intro s hs h; unfold mk_strat_fn
  have h₁ := Classical.epsilon_spec h; dsimp
  cases h₂ : f s; simp; exact State.validTr_chooseMove h
  nm s'; simp [guard]; split_ifs with h₃; simpa
  simp; exact State.validTr_chooseMove h

@[simp] def AStrat.mk (f : State → Option PointZ) : AStrat := ⟨mk_strat_fn f⟩
@[simp] def DStrat.mk (f : State → Option PointZ) : DStrat := ⟨mk_strat_fn f⟩

instance {f} : (AStrat.mk f).WF := by simp; infer_instance
instance {f} : (DStrat.mk f).WF := by simp; infer_instance

@[simp] theorem AStrat.f_mk {f} : (AStrat.mk' f).f = f := rfl
@[simp] theorem DStrat.f_mk {f} : (DStrat.mk' f).f = f := rfl

theorem State.exi_tr_reachable_of_mem_dropLast_hist {s p} [hs : sys.WF s]
(h : p ∈ s.hist.dropLast) : ∃ s₀, sys.WF s₀ ∧ sys.validTr s₀ p ∧ sys.Reachable s₀ s := by
  have h₁ := s.trs_reverse_hist_eq
  rw [←List.mem_reverse, List.mem_iff_append] at h
  obtain ⟨xs, ys, h⟩ := h
  simp at h h₁
  rw [h] at h₁
  clear h
  simp [sys.trs_append] at h₁
  generalize hr : sys.trs (initState s.pw s.aPos₀) xs = r at h₁
  rcases r with ⟨s₁, r⟩
  dsimp at h₁
  split_ifs at h₁ with h₂ <;> simp at h₁
  subst h₂
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  split at h₂; simp at h₂
  nm x s₂ h₃; clear x
  simp [h₃] at h₁
  refine ⟨s₁, ?_, ⟨_, h₃⟩, ?_⟩
  · rw [wf_iff]
    use xs
    convert hr using 3
    · change _ = (initState s.pw s.aPos₀).pw
      apply pw_eq_of_reachable
      exact sys.reachable_of_trs hr
    · have hs₁ : sys.WF s₁
      · use initState s.pw s.aPos₀
        simp; exact System.reachable_of_trs' hr
      symm
      apply aPos₀_eq_of_reachable
      apply sys.reachable_of_tr h₃ |>.trans
      exact System.reachable_of_fst_trs h₁
  · rw [←h₁]
    apply sys.reachable_of_trs (ts := p :: ys)
    simp [h₃]

@[simp] instance {s} [hs : sys.Initial s] : DState s := by
  use inferInstance; simp at hs; rw [←hs]; rfl

theorem wfTrans {p} : sys.WFTrans p := by
  use initState 0 # p + 1; simp [DState.validTr_iff, Point.one_def]

@[simp] instance {p} : sys.WFTrans p := wfTrans

theorem State.hist_eq_snoc {s} [hs : sys.WF s] :
s.hist = s.hist.dropLast ++ [s.aPos₀] := by
  generalize h : s.hist = ps
  induction ps using List.reverseRecOn; simp at h
  nm ps p ih; clear ih; simp [aPos₀, h]

theorem State.exi_hist_eq_snoc {s} [hs : sys.WF s] :
∃ (ps : List PointZ), s.hist = ps ++ [s.aPos₀] :=
  ⟨_, s.hist_eq_snoc⟩

instance {s : State} {hist₁ hist₂} [hs : sys.WF # s.setHist hist₂] :
sys.WF # s.setHist hist₁ |>.setHist hist₂ := by simpa

instance {s : State} [hs : sys.WF s] : sys.WF # s.setHist s.hist := by simpa

theorem AState.aPos_eq_of_tr {s s' p} [hs : AState s]
(h : sys.tr s p = some s') : s'.aPos = p := by
  simp at h; rw [←h.2]

theorem DState.aPos_eq_of_tr {s s' p} [hs : DState s]
(h : sys.tr s p = some s') : s'.aPos = s.aPos := by
  simp at h; rw [←h.2]

theorem AState.taken_eq_of_tr {s s' p} [hs : AState s]
(h : sys.tr s p = some s') : s'.taken = s.taken := by
  simp at h; rw [←h.2]

theorem DState.taken_eq_of_tr {s s' p} [hs : DState s]
(h : sys.tr s p = some s') : s'.taken = s.taken.insert p := by
  simp at h; rw [←h.2]

@[simp]
theorem State.aPos_ne_chooseDMove {s} [hs : DState s] : s.aPos ≠ s.chooseDMove := by
  have h := hs.validTr_chooseDMove; rw [DState.validTr_iff] at h; exact h.1

@[simp]
theorem State.chooseDMove_not_mem_taken {s} [hs : DState s] : s.chooseDMove ∉ s.taken := by
  have h := hs.validTr_chooseDMove; rw [DState.validTr_iff] at h; exact h.2