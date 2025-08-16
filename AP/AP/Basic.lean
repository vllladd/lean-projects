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

instance {st : Strat} [hst : st.WF] : st.a.WF := hst.wf_a
instance {st : Strat} [hst : st.WF] : st.d.WF := hst.wf_d

abbrev State.WF (s : State) : Prop := sys.WF s

class AState (s : State) : Prop where
  wf_s : s.WF
  turn : s.aTurn

class DState (s : State) : Prop where
  wf_s : s.WF
  turn : s.aTurn = false

theorem AState.iff {s : State} : AState s ↔ s.WF ∧ s.aTurn :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem DState.iff {s : State} : DState s ↔ s.WF ∧ s.aTurn = false :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

instance {sa} [ha : AState sa] : sa.WF := ha.wf_s
instance {sd} [hd : DState sd] : sd.WF := hd.wf_s

@[simp] theorem AState.turn' {s : State} [hs : AState s] : s.aTurn := hs.turn
@[simp] theorem DState.turn' {s : State} [hs : DState s] : s.aTurn = false := hs.turn

def State.dChooseMove (s : State) : PointZ :=
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

theorem State.validTr_dChooseMove {s : State} (ht : s.aTurn = false) :
sys.validTr s s.dChooseMove := by
  rw [s.validTr_iff_of_not_aTurn ht]
  suffices h₁ : s.dChooseMove ∉ insert s.aPos s.taken
  · simp at h₁; rw [ne_comm]; exact h₁
  apply Set'.not_mem_of_max!_lt
  simp [State.dChooseMove, Point.zero_def]

theorem State.hasTr_of_not_aTurn {s : State} (ht : s.aTurn = false) : sys.hasTr s := by
  use s.dChooseMove; exact s.validTr_dChooseMove ht

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
{s : State} (hs : s.WF) : P s := by
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

theorem AState.validTr_of_le {s : State} [hs : AState s] {pw' p}
(h₁ : s.pw ≤ pw') (h₂ : sys.validTr s p) : sys.validTr {s with pw := pw'} p := by
  simp [hs.validTr_iff] at h₂; rcases h₂ with ⟨h₂, h₃, h₄⟩
  simp [System.validTr, sys, State.move, State.aMove]
  use h₂, h₃; linarith

theorem AState.hasTr_of_le {s : State} [hs : AState s] {pw'}
(h₁ : s.pw ≤ pw') (h₂ : sys.hasTr s) : sys.hasTr {s with pw := pw'} := by
  obtain ⟨p, h₃⟩ := h₂; use p; exact hs.validTr_of_le h₁ h₃

@[simp]
theorem State.not_a_wins_iff {s : State} {st : Strat} : ¬s.a_wins st ↔ s.d_wins st := by
  simp [a_wins, d_wins]

@[simp]
theorem State.not_d_wins_iff {s : State} {st : Strat} : ¬s.d_wins st ↔ s.a_wins st := by
  simp [a_wins, d_wins]

theorem AStrat.wf_iff {a : AStrat} : a.WF ↔ ∀ {s} [AState s],
sys.hasTr s → sys.validTr s (a.f s) := by
  simp [AState.iff, AStrat.wf_def]; tauto

theorem DStrat.wf_iff {d : DStrat} : d.WF ↔ ∀ {s} [DState s],
sys.hasTr s → sys.validTr s (d.f s) := by
  simp [DState.iff, DStrat.wf_def]; tauto

@[simp]
theorem AState.sys_tr_eq_some_iff {s s' p} [hs : AState s] :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw) ∧
{s with aPos := p, aTurn := false, hist := p :: s.hist} = s' := by
  simp [sys, State.move, State.aMove]

@[simp]
theorem DState.sys_tr_eq_some_iff {s s' p} [hs : DState s] :
sys.tr s p = some s' ↔ (s.aPos ≠ p ∧ p ∉ s.taken) ∧
{s with taken := insert p s.taken, aTurn := true, hist := p :: s.hist} = s' := by
  simp [sys, State.move, State.dMove]

@[simp]
theorem AState.start_f_eq {sa} {st : Strat} [ha : AState sa] :
st.f sa = st.a.f sa := by simp [Strat.f]

@[simp]
theorem DState.start_f_eq {sd} {st : Strat} [hd : DState sd] :
st.f sd = st.d.f sd := by simp [Strat.f]

theorem State.a_wins_iff_mul_two {s : State} {st : Strat} :
s.a_wins st ↔ ∀ n, (sys.simulate st.f s # n * 2).2 = 0 := by
  constructor <;> intro h n; apply h
  apply System.simulate_snd_eq_zero_of_le_and_eq_zero # h n; simp

@[simp]
theorem DState.tr_ne_none {sd} [hd : DState sd] {st : DStrat} [hst : st.WF] :
sys.tr sd (st.f sd) ≠ none := by
  have h₁ := hd.hasTr
  rw [DStrat.wf_iff] at hst
  obtain ⟨sa, h₂⟩ := hst h₁
  simp [h₂]

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

theorem State.aState_or_dState {s} [hs : sys.WF s] : AState s ∨ DState s := by
  simp [AState.iff, DState.iff, hs]

theorem AStrat.validTr {sa} [hs : AState sa] {st : AStrat} [hst : st.WF]
(h : sys.hasTr sa) : sys.validTr sa (st.f sa) := by
  rw [AStrat.wf_iff] at hst; exact hst h

@[simp]
theorem DStrat.validTr {sd} [hs : DState sd] {st : DStrat} [hst : st.WF] :
sys.validTr sd (st.f sd) := by
  rw [DStrat.wf_iff] at hst; apply hst; simp

theorem Strat.validTr {s} [hs : sys.WF s] {st : Strat} [hst : st.WF]
(h : sys.hasTr s) : sys.validTr s (st.f s) := by
  rw [Strat.wf_def] at hst; exact hst h