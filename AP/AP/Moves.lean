import AP.AP.Reachability
import AP.Temp

namespace AP

def State.moveSim (s : State) (st : Strat) (s₁ : State) :
Option # (PointZ × State) ⊕ (PointZ × State) := do
  guard # (sys.simulate st.f s # s₁.diff s).1 = s₁
  let p := st.f s₁
  let s₂ ← sys.tr s₁ p
  pure # ite s₁.aTurn Sum.inr Sum.inl (p, s₂)

def State.aMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inr r => some r
  | _ => none

def State.dMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inl r => some r
  | _ => none

def State.aSimPairs (s : State) (st : Strat) : Set (State × PointZ) :=
  {(s₁, p) | ∃ s₂, s.aMoveSim st s₁ = some (p, s₂)}

def State.aSimPts (s : State) (st : Strat) : Set PointZ :=
  Prod.snd '' s.aSimPairs st

def State.simStates (s : State) (st : Strat) : Set State :=
  {s₁ | ∃ n, sys.simulate st.f s n = (s₁, 0)}

def State.simStatesRangeAux (r : ℕ → ℕ → Prop) [hs : DecidableRel r]
(s s₁ : State) (st : Strat) : Finset State :=
  if ∃ n, sys.simulate st.f s n = (s₁, 0) then
    Finset.Icc 0 (s₁.diff s) |>.image (λ n => sys.simulate st.f s n |>.1)
      |>.filter λ s₂ => r s₂.hist.length s₁.hist.length
  else ∅

def State.simStatesIcc (s s₁ : State) (st : Strat) : Finset State :=
  s.simStatesRangeAux (· ≤ ·) s₁ st

def State.simStatesIco (s s₁ : State) (st : Strat) : Finset State :=
  s.simStatesRangeAux (· < ·) s₁ st

def State.aSimStates (s : State) (st : Strat) : Set State :=
  s.simStates st |>.filter (·.aTurn)

def State.aSimStatesIcc (s s₁ : State) (st : Strat) : Finset State :=
  s.simStatesIcc s₁ st |>.filter (·.aTurn)

def State.aSimStatesIco (s s₁ : State) (st : Strat) : Finset State :=
  s.simStatesIco s₁ st |>.filter (·.aTurn)

def State.init (s : State) : State :=
  initState s.pw s.aPos₀

def State.prev (s : State) : State :=
  sys.trs s.init (s.diffTrs s.init |>.init) |>.1

def State.lastMove (s : State) : PointZ :=
  s.diffTrs s.prev |>.getLast!

def State.IsInit (s : State) : Prop :=
  sys.Initial s

noncomputable
def State.aSimPtsNcard (s : State) (st : Strat) (set : Set PointZ) : Option ℕ :=
  s.aSimPairs st |>.filter (·.2 ∈ set) |>.ncard?

def State.aVisitedIcc' (s : State) (ps : List PointZ) : Set' PointZ :=
  match ps with
  | [] => ∅
  | p :: ps =>
    let set := sys.tr s p |>.getd.aVisitedIcc' ps
    if s.aTurn then set.insert p else set

def State.aVisitedIcc (s s₁ : State) : Set' PointZ :=
  if sys.Reachable s s₁ then State.aVisitedIcc' s (s₁.diffTrs s) |>.insert s.aPos else ∅

def State.aVisitedIco (s s₁ : State) : Set' PointZ :=
  if s = s₁ then ∅ else s.aVisitedIcc s₁.prev

def State.aNbhdsIco (s : State) (st : Strat) (s₁ : State) : Set' PointZ :=
  Set'.ofFinset (s.aSimStatesIco s₁ st |>.image (·.aPos)) |>.bind (·.nbhd s.pw)

-- #check 0 #exit

-----

@[simp]
theorem State.aVisitedIcc'_nil {s : State} : s.aVisitedIcc' [] = ∅ := rfl

@[simp]
theorem State.aVisitedIcc_self {s : State} : s.aVisitedIcc s = Set'.singleton s.aPos := by
  simp [aVisitedIcc]

theorem State.aTurn_iff_aState {s} [hs : sys.WF s] : s.aTurn ↔ AState s := by
  constructor
  · intro h; use hs
  · intro h; simp

@[simp]
theorem State.aVisitedIcc'_singleton {s : State} {p} :
s.aVisitedIcc' [p] = if s.aTurn then Set'.singleton p else ∅ := by
  simp [aVisitedIcc']

theorem AState.aVisitedIcc'_cons {s s' : State} {p ps} [hs : AState s]
(h : sys.tr s p = some s') : s.aVisitedIcc' (p :: ps) =
(s'.aVisitedIcc' ps).insert p := by
  simp [State.aVisitedIcc', h]

theorem DState.aVisitedIcc'_cons {s s' : State} {p ps} [hs : DState s]
(h : sys.tr s p = some s') : s.aVisitedIcc' (p :: ps) = s'.aVisitedIcc' ps := by
  simp [State.aVisitedIcc', h]

theorem AState.aVisitedIcc'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : AState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisitedIcc' (ps ++ [p]) = (s.aVisitedIcc' ps).insert p := by
  induction ps generalizing s
  · simp at h₁; simp [h₁]
  nm p₁ ps ih
  simp at h₁
  choose s' h₁ h₃ using h₁
  have hs' := sys.wf_of_tr h₁
  specialize ih h₃
  replace hs := s.aState_or_dState
  rw [List.cons_append]
  rcases hs with hs | hs
  · simp_rw [AState.aVisitedIcc'_cons h₁, ih, Set'.insert_comm]
  · simp_rw [DState.aVisitedIcc'_cons h₁, ih]

theorem DState.aVisitedIcc'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : DState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisitedIcc' (ps ++ [p]) = s.aVisitedIcc' ps := by
  induction ps generalizing s
  · simp at h₁; simp [h₁]
  nm p₁ ps ih
  simp at h₁
  choose s' h₁ h₃ using h₁
  have hs' := sys.wf_of_tr h₁
  specialize ih h₃
  replace hs := s.aState_or_dState
  rw [List.cons_append]
  rcases hs with hs | hs
  · simp_rw [AState.aVisitedIcc'_cons h₁, ih]
  · simp_rw [DState.aVisitedIcc'_cons h₁, ih]

theorem AState.aVisitedIcc_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : AState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisitedIcc s₂ = (s.aVisitedIcc s₁).insert p := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisitedIcc]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [if_pos # sys.reachable_of_trs h₁]
  rw [if_pos # sys.reachable_of_trs h₂]
  rw [State.diffTrs_eq_of_trs_full h₂, Set'.insert_comm]
  rw [aVisitedIcc'_snoc h₁]

theorem DState.aVisitedIcc_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : DState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisitedIcc s₂ = s.aVisitedIcc s₁ := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisitedIcc]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [if_pos # sys.reachable_of_trs h₁]
  rw [if_pos # sys.reachable_of_trs h₂]
  rw [State.diffTrs_eq_of_trs_full h₂]
  rw [aVisitedIcc'_snoc h₁]

theorem State.mem_aVisitedIcc_iff_of {s f n s₁ p} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, 0)) : p ∈ s.aVisitedIcc s₁ ↔ p = s.aPos ∨
∃ k < n, ∃ s', AState s' ∧ sys.simulate f s k = (s', 0) ∧ f s' = p := by
  induction n generalizing s₁
  · simp at h; simp [h]
  nm n ih
  simp at h
  choose s' h₁ h₂ using h
  specialize ih h₁
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h₁
  have hs₁ := sys.wf_of_tr h₂
  have h₃ := sys.reachable_of_simulate_eq h₁
  replace hs' := s'.aState_or_dState
  rcases hs' with hs' | hs'
  all_goals simp [hs'.aVisitedIcc_eq_of_tr h₂ h₃, ih]; clear ih
  · grind
  apply iff_of_eq; congr 1; apply propext
  apply exists_congr; intro k
  by_cases h : k ≠ n
  · simp [le_iff_eq_or_lt, h]
  push_neg at h; subst h
  simp
  rintro s₂ hs₂ h₄ rfl
  simp [h₁] at h₄
  contrapose! h₄
  apply ne_of_congr (·.aTurn); simp

theorem State.trs_diffTrs {s s₁ ps ps'} [hs : sys.WF s]
(h : sys.trs s ps = (s₁, ps')) : sys.trs s (s₁.diffTrs s) = (s₁, []) := by
  induction ps using List.reverseRecOn generalizing s s₁ ps'
  · simp at h; simp [h]
  nm ps p ih
  simp [sys.trs_append] at h
  generalize hr : sys.trs s ps = r at h
  rcases r with ⟨s', r⟩
  dsimp at h
  split_ifs at h with h₁
  · subst h₁
    simp at h
    specialize ih hr
    simp [System.trs] at h
    split at h
    · grind
    nm x s₂ h₁; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rw [diffTrs_eq_of_tr h₁ # sys.reachable_of_trs hr]
    simpa [ih]
  simp at h
  rcases h with ⟨rfl, rfl⟩
  exact ih hr

theorem State.simulate_diff {s s₁ f n r} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, r)) : sys.simulate f s (s₁.diff s) = (s₁, 0) := by
  induction n generalizing s s₁ r
  · simp at h; simp [h]
  nm n ih
  rw [sys.simulate_add] at h
  simp at h
  generalize hr : sys.simulate f s n = r at h
  rcases r with ⟨s', r⟩
  dsimp at h
  split_ifs at h with h₁
  · subst h₁
    simp at h
    specialize ih hr
    simp [System.simulate] at h
    split at h
    · grind
    nm x s₂ h₁; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rw [diff_eq_of_tr h₁ # sys.reachable_of_simulate_eq hr]
    rw [sys.simulate_add]
    simpa [ih]
  simp at h
  rcases h with ⟨rfl, rfl⟩
  exact ih hr

theorem State.aSimPts_eq_setOf {s : State} {st} : s.aSimPts st =
{p | ∃ s₁ s₂, s.aMoveSim st s₁ = some (p, s₂)} := by
  ext; simp [aSimPts, aSimPairs]

theorem State.mem_aSimPts_iff_aSimPairs {s : State} {st p} :
p ∈ s.aSimPts st ↔ ∃ s₁, (s₁, p) ∈ s.aSimPairs st := by
  simp [aSimPts]

@[simp]
theorem State.mem_simStates_iff {s : State} {st s₁} :
s₁ ∈ s.simStates st ↔ ∃ n, sys.simulate st.f s n = (s₁, 0) := by rfl

theorem State.false_of_aState_and_dState s [hs₁ : AState s] [hs₂ : DState s] : False := by
  simp at hs₁

theorem AState.even_of_simulate {s s₁ f n} [hs : AState s] [hs₁ : AState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Even n := by
  by_contra h₁; simp at h₁
  obtain ⟨n, rfl⟩ := h₁
  rw [mul_comm] at h
  have h₁ := DState.of_simulate_mul_two_add_one_eq_full h
  exact s₁.false_of_aState_and_dState

theorem AState.odd_of_simulate {s s₁ f n} [hs : AState s] [hs₁ : DState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Odd n := by
  by_contra h₁; simp at h₁; obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp h₁
  have h₂ := AState.of_simulate_mul_two_eq_full h; simp at h₂

theorem DState.even_of_simulate {s s₁ f n} [hs : DState s] [hs₁ : DState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Even n := by
  by_contra h₁; simp at h₁
  obtain ⟨n, rfl⟩ := Nat.odd_iff_exi.mp h₁; clear h₁
  simp at h
  choose s' h₁ h₂ using h
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h₁
  replace hs' := AState.of_tr' h₂
  have h₃ := DState.of_simulate_mul_two_eq_full h₁
  simp at h₃

theorem DState.odd_of_simulate {s s₁ f n} [hs : DState s] [hs₁ : AState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Odd n := by
  by_contra h₁; simp at h₁
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp h₁; clear h₁
  have h₁ := DState.of_simulate_mul_two_eq_full h
  simp at h₁

@[simp]
theorem State.mem_aSimStates_iff {s : State} {st s₁} [hs : sys.WF s] :
s₁ ∈ s.aSimStates st ↔ AState s₁ ∧ ∃ n, sys.simulate st.f s n = (s₁, 0) := by
  simp [aSimStates]
  constructor
  · rintro ⟨⟨n, h⟩, hs₁'⟩
    have hs₁ := sys.wf_of_simulate_eq h
    dsimp at hs₁
    replace hs₁ : AState s₁
    · use hs₁
    use hs₁, n
  · rintro ⟨hs₁1, n, h⟩; simp; use n

theorem State.mem_aSimPairs_iff_simulate_tr {s s₁ p} {st : Strat} [hs : sys.WF s] :
(s₁, p) ∈ s.aSimPairs st ↔ AState s₁ ∧ ∃ n, sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp only [aSimPairs, aMoveSim, moveSim, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq, exists_const, Sum.exists,
    reduceCtorEq, and_false, exists_eq_right, false_or, exists_and_left, Set.mem_setOf_eq,
    exists_and_right]
  constructor
  · rintro ⟨h₁, s₂, s₃, h₂, h₃⟩
    split_ifs at h₃ with ht
    simp at h₃
    rcases h₃ with ⟨rfl, rfl⟩
    apply and_of
    · constructor
      · rw [←h₁]; infer_instance
      exact ht
    intro hs₁
    clear ht
    simp
    generalize hr : sys.simulate st.f s (s₁.diff s) = r at h₁ ⊢
    rcases r with ⟨s₁, r⟩
    dsimp at *
    subst h₁
    simp at h₂ ⊢
    simp [h₂]
    use s₁.diff s - r, sys.simulate_sub_eq_of hr
  · rintro ⟨hs₁, ⟨n, h₁⟩, ⟨s₂, h₂⟩, rfl⟩
    simp [simulate_diff h₁]
    use s₂

theorem State.mem_aSimPts_iff_simulate_tr {s p} {st : Strat} [hs : sys.WF s] :
p ∈ s.aSimPts st ↔ ∃ n s₁, AState s₁ ∧ sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp_rw [mem_aSimPts_iff_aSimPairs, mem_aSimPairs_iff_simulate_tr]; grind

theorem State.mem_aSimPts_iff_simulate_ge_two {s p} {st : Strat} [hst : st.WF] [hs : sys.WF s] :
p ∈ s.aSimPts st ↔ ∃ n s₁, 2 ≤ n ∧ sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos = p := by
  rw [mem_aSimPts_iff_simulate_tr]
  constructor
  · rintro ⟨n, s₁, hs₁, h₁, s₂, h₂, rfl⟩
    have hs₂ := DState.of_tr h₂
    obtain ⟨s₃, h₃⟩ : sys.validTr s₂ (st.d.f s₂)
    · simp
    use n + 2, by omega
    rw [sys.simulate_add]
    simp [System.simulate, h₁, h₂, h₃]
    rw [DState.aPos_eq_of_tr h₃, AState.aPos_eq_of_tr h₂]
  · rintro ⟨n, s₃, hn, h₁, rfl⟩
    simp only [exists_and_right]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
    rw [add_comm] at h₁
    simp at h₁
    obtain ⟨s₂, ⟨s₁, h₁, h₂⟩, h₃⟩ := h₁
    have hs₁ : sys.WF s₁ := sys.wf_of_simulate_eq h₁
    replace hs₁ := s₁.aState_or_dState
    rcases hs₁ with hs₁ | hs₁
    · simp at h₂
      have hs₂ := DState.of_tr h₂
      use n, s₁, hs₁, h₁
      refine ⟨⟨s₂, h₂⟩, ?_⟩
      rw [DState.aPos_eq_of_tr h₃, AState.aPos_eq_of_tr h₂]
    · have hs₂ := AState.of_tr h₂
      simp at h₂ h₃
      use n + 1, s₂, hs₂
      rw [sys.simulate_add]
      simp [h₁]
      use h₂
      refine ⟨⟨s₃, h₃⟩, ?_⟩
      rw [AState.aPos_eq_of_tr h₃]

theorem State.aVisitedIcc_subset_of_simulate_le  (st : Strat) k n {s s₁ s₂} [hs : sys.WF s]
(hn : k ≤ n) (h₁ : sys.simulate st.f s k = (s₁, 0)) (h₂ : sys.simulate st.f s n = (s₂, 0)) :
s.aVisitedIcc s₁ ⊆ s.aVisitedIcc s₂ := by
  intro p; rw [mem_aVisitedIcc_iff_of h₁, mem_aVisitedIcc_iff_of h₂]; grind

@[simp]
instance {s : State} : sys.Initial s.init := by
  unfold State.init; infer_instance

@[simp]
theorem State.one_le_hist_length {s} [hs : sys.WF s] : 1 ≤ s.hist.length := by
  simp [Nat.one_le_iff_ne_zero]

theorem State.diff_init_succ {s} [hs : sys.WF s] : s.diff s.init + 1 = s.hist.length := by
  simp [init, diff]

@[simp]
theorem State.diff_init {s} [hs : sys.WF s] : s.diff s.init = s.hist.length - 1 := by
  have := s.diff_init_succ; omega

@[simp]
theorem State.isInit_initial {s} [hs : sys.Initial s] : s.IsInit := hs

theorem State.isInit_of_length_hist_eq_one {s}
[hs : sys.WF s] (h : s.hist.length = 1) : s.IsInit := by
  rw [IsInit, initial_iff]; ext <;> simp_all

theorem State.length_hist_eq_one_of_isInit {s : State}
(h : s.IsInit) : s.hist.length = 1 := by
  rw [IsInit, initial_iff] at h; rw [←h]; rfl

theorem State.isInit_iff_length_hist_eq_one {s}
[hs : sys.WF s] : s.IsInit ↔ s.hist.length = 1 :=
  ⟨length_hist_eq_one_of_isInit, isInit_of_length_hist_eq_one⟩

@[simp]
theorem State.length_hist_init {s : State} : s.init.hist.length = 1 := by
  simp [init]

@[simp]
theorem State.diffTrs_init {s} [hs : sys.WF s] : s.diffTrs s.init = s.hist.init.reverse := by
  simp [diffTrs]

@[simp]
theorem AState.initState_ne {s pw p₀} [ha : AState s] : initState pw p₀ ≠ s := by
  rintro rfl; simp at ha

@[simp]
theorem AState.not_isInit {s} [ha : AState s] : ¬s.IsInit := by
  simp [State.IsInit]

theorem State.wf_prev_and_tr {s} [hs : sys.WF s]
(h : ¬s.IsInit) : sys.WF s.prev ∧ sys.tr s.prev s.lastMove = some s := by
  choose ps h₁ using wf_iff.mp hs
  induction ps using List.reverseRecOn
  · simp at h₁
    rw [←h₁] at h
    simp at h
  nm ps p ih; clear ih
  simp at h₁
  choose s' h₁ h₂ using h₁
  rw [lastMove, prev]
  simp [hist_eq_of_tr h₂, hist_eq_of_trs h₁]
  simp [init, h₁, diffTrs_eq_of_tr h₂, h₂]
  exact sys.wf_of_trs h₁

theorem State.wf_prev {s} [hs : sys.WF s] (h : ¬s.IsInit) : sys.WF s.prev :=
  wf_prev_and_tr h |>.1

theorem State.prev_tr_lastMove {s} [hs : sys.WF s]
(h : ¬s.IsInit) : sys.tr s.prev s.lastMove = some s :=
  wf_prev_and_tr h |>.2

theorem State.length_hist_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.prev.hist.length = s.hist.length - 1 := by
  simp [length_hist_eq_of_tr # prev_tr_lastMove h]

theorem State.not_isInit_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : ¬s'.IsInit := by
  have hs' := sys.wf_of_tr h; simp [isInit_iff_length_hist_eq_one, length_hist_eq_of_tr h]

theorem State.eq_iff_pw_and_hist {s₁ s₂} [hs₁ : sys.WF s₁] [hs₂ : sys.WF s₂] :
s₁ = s₂ ↔ s₁.pw = s₂.pw ∧ s₁.hist = s₂.hist := by
  use by rintro rfl; simp;
  rintro ⟨h₁, h₂⟩
  choose ps₁ h₃ using wf_iff.mp hs₁
  choose ps₂ h₄ using wf_iff.mp hs₂
  rw [←h₁, aPos₀, ←h₂, ←aPos₀] at h₄
  simp [hist_eq_of_trs h₃, hist_eq_of_trs h₄] at h₂
  grind

theorem State.tr_inj {s₁ s₂ s₃ p₁ p₂} [hs₁ : sys.WF s₁] [hs₂ : sys.WF s₂]
(h₁ : sys.tr s₁ p₁ = some s₃) (h₂ : sys.tr s₂ p₂ = some s₃) : s₁ = s₂ ∧ p₁ = p₂ := by
  replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  · have hs₃ := DState.of_tr h₁
    replace hs₂ := AState.of_tr' h₂
    rw [AState.tr_eq_some_iff] at h₁ h₂
    rcases h₂ with ⟨⟨h₄, h₅, h₆⟩, rfl⟩
    rcases h₁ with ⟨⟨h₁, h₂, h₃⟩, h₇⟩
    rw [eq_iff_pw_and_hist]; grind
  · have hs₃ := AState.of_tr h₁
    replace hs₂ := DState.of_tr' h₂
    rw [DState.tr_eq_some_iff] at h₁ h₂
    rcases h₂ with ⟨⟨h₄, h₅⟩, rfl⟩
    rcases h₁ with ⟨⟨h₁, h₂⟩, h₇⟩
    rw [eq_iff_pw_and_hist]; grind

theorem State.lastMove_eq_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : s'.lastMove = p := by
  have hs' := sys.wf_of_tr h
  have h₁ := not_isInit_of_tr h
  have h₂ := prev_tr_lastMove h₁
  have H := wf_prev h₁
  obtain ⟨rfl, rfl⟩ := tr_inj h h₂; rfl

theorem State.diffTrs_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.diffTrs s.prev = [s.lastMove] := by
  simp [diffTrs_eq_of_tr # prev_tr_lastMove h]

theorem State.diff_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.diff s.prev = 1 := by
  simp [diff_eq_of_tr # prev_tr_lastMove h]

theorem State.prev_eq_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : s'.prev = s := by
  have hs' := sys.wf_of_tr h
  have H₁ := not_isInit_of_tr h
  have h₁ := s'.prev_tr_lastMove H₁
  have H₂ := wf_prev H₁
  obtain ⟨rfl, rfl⟩ := tr_inj h h₁; rfl

theorem State.aSimPairs_point_eq_of_state_eq {s : State} {s₁ p₁ p₂ st} [hs : sys.WF s]
(h₁ : (s₁, p₁) ∈ s.aSimPairs st) (h₂ : (s₁, p₂) ∈ s.aSimPairs st) : p₁ = p₂ := by
  rw [mem_aSimPairs_iff_simulate_tr] at h₁ h₂; grind

@[simp]
theorem State.aSimPtsNcard_empty {s : State} {st} : s.aSimPtsNcard st ∅ = some 0 := by
  simp [aSimPtsNcard]

@[simp]
theorem State.aSimPtsNcard_eq_zero_iff {s : State} {st set} [hs : sys.WF s] :
s.aSimPtsNcard st set = some 0 ↔ ∀ n s₁ s₂ [AState s₁],
sys.simulate st.f s n = (s₁, 0) → sys.tr s₁ (st.a.f s₁) = some s₂ → s₂.aPos ∉ set := by
  rw [aSimPtsNcard, Set.ncard?]
  split_ifs with h₁; rotate_left
  · simp at h₁ ⊢
    replace h₁ := Set.exi_mem_of_infinite h₁
    rcases h₁ with ⟨⟨s₁, p⟩, h₁⟩
    simp at h₁
    rw [mem_aSimPairs_iff_simulate_tr] at h₁
    obtain ⟨⟨hs₁, n, h₁, s₂, h₂, h₃⟩, h₄⟩ := h₁
    use n, s₁, hs₁, h₁, s₂, h₂
    rwa [AState.aPos_eq_of_tr h₂, h₃]
  simp
  rw [Set.ncard_eq_zero # by grind]
  rw [Set.eq_empty_iff]
  simp
  constructor
  · intro h n s₁ s₂ hs₁ h₂ h₃
    specialize h s₁ (st.a.f s₁)
    rw [mem_aSimPairs_iff_simulate_tr] at h
    rw [AState.aPos_eq_of_tr h₃]
    apply h; clear h
    use hs₁, n, h₂, s₂
  · intro h s₁ p h₂
    rw [mem_aSimPairs_iff_simulate_tr] at h₂
    choose hs₁ n h₂ s₂ h₃ h₄ using h₂
    specialize h n s₁ s₂ h₂ h₃
    rwa [←h₄, ←AState.aPos_eq_of_tr h₃]

theorem State.aSimPairs_eq_of_length_hist_eq {s s₁ s₂ p₁ p₂ st} [hs : sys.WF s]
(h₁ : (s₁, p₁) ∈ s.aSimPairs st) (h₂ : (s₂, p₂) ∈ s.aSimPairs st)
(h₃ : s₁.hist.length = s₂.hist.length) : s₁ = s₂ := by
  rw [mem_aSimPairs_iff_simulate_tr] at h₁ h₂
  choose hs₁ n h₁ h₄ h₅ h₆ using h₁
  choose hs₂ k h₂ h₇ h₈ h₉ using h₂
  simp [length_hist_eq_of_simulate_eq h₁, length_hist_eq_of_simulate_eq h₂] at h₃
  subst h₃
  simp [h₁] at h₂
  exact h₂

theorem State.finite_filter_aSimPairs_iff_image_length_hist {s : State} {st p}
[hs : sys.WF s] : (s.aSimPairs st |>.filter p |>.Finite) ↔
(s.aSimPairs st |>.filter p |>.image (·.1.hist.length) |>.Finite) := by
  rw [Set.finite_image_iff]
  rintro ⟨s₂, p₂⟩ h₄ ⟨s₃, p₃⟩ h₅ h₆
  simp at h₄ h₅ h₆ ⊢
  rcases h₄ with ⟨h₄, hp₂⟩
  rcases h₅ with ⟨h₅, hp₃⟩
  apply and_of # aSimPairs_eq_of_length_hist_eq h₄ h₅ h₆
  rintro rfl; exact aSimPairs_point_eq_of_state_eq h₄ h₅

theorem State.infinite_filter_aSimPairs_iff_image_length_hist {s : State} {st p}
[hs : sys.WF s] : (s.aSimPairs st |>.filter p |>.Infinite) ↔
(s.aSimPairs st |>.filter p |>.image (·.1.hist.length) |>.Infinite) := by
  rw [iff_iff_not']; simp [finite_filter_aSimPairs_iff_image_length_hist]

theorem State.nonempty_filter_aSimPairs_iff_image_length_hist {s : State} {st p} :
(s.aSimPairs st |>.filter p |>.Nonempty) ↔
(s.aSimPairs st |>.filter p |>.image (·.1.hist.length) |>.Nonempty) := by
  simp

theorem State.eq_simulate_eq_and_length_hist_eq {s s₁ s₂ n₁ n₂} {st : Strat}
(h₁ : sys.simulate st.f s n₁ = (s₁, 0)) (h₂ : sys.simulate st.f s n₂ = (s₂, 0))
(h₃ : s₁.hist.length = s₂.hist.length) : s₁ = s₂ := by
  simp [length_hist_eq_of_simulate_eq h₁, length_hist_eq_of_simulate_eq h₂] at h₃
  subst h₃; simp [h₁] at h₂; exact h₂

theorem State.eq_of_mem_aSimPairs' {s st s₁ s₂ p₁ p₂} [hs : sys.WF s]
(h₁ : (s₁, p₁) ∈ s.aSimPairs st) (h₂ : (s₂, p₂) ∈ s.aSimPairs st)
(h₃ : s₁.hist.length = s₂.hist.length) : s₁ = s₂ ∧ p₁ = p₂ := by
  rw [mem_aSimPairs_iff_simulate_tr] at h₁ h₂
  choose hs₁ n₁ h₁ s₃ h₄ h₅ using h₁
  choose hs₂ n₂ h₂ s₄ h₆ h₇ using h₂
  apply and_of
  · exact eq_simulate_eq_and_length_hist_eq h₁ h₂ h₃
  rintro rfl
  rw [←h₅, ←h₇]

theorem State.eq_of_mem_aSimPairs {s st r₁ r₂} [hs : sys.WF s]
(h₁ : r₁ ∈ s.aSimPairs st) (h₂ : r₂ ∈ s.aSimPairs st)
(h₃ : r₁.1.hist.length = r₂.1.hist.length) : r₁ = r₂ := by
  cases r₁; cases r₂; simp; exact eq_of_mem_aSimPairs' h₁ h₂ h₃

theorem State.ncard_filter_aSimPairs_eq_image_length_hist {s : State} {st p} [hs : sys.WF s] :
(s.aSimPairs st |>.filter p |>.ncard) =
(s.aSimPairs st |>.filter p |>.image (·.1.hist.length) |>.ncard) := by
  rw [Set.ncard_eq_ite]
  nth_rw 2 [Set.ncard_eq_ite]
  rw [finite_filter_aSimPairs_iff_image_length_hist]
  split_ifs with h
  on_goal 2 => rfl
  symm; rw [Set.ncard_image_eq_iff_injOn]
  rotate_left; rwa [finite_filter_aSimPairs_iff_image_length_hist]
  rintro ⟨s₁, p₁⟩ h₁ ⟨s₂, p₂⟩ h₂ h₃
  simp at h₁ h₂ h₃
  exact eq_of_mem_aSimPairs h₁.1 h₂.1 h₃

theorem AState.aSeek_exi_tr_of {s P} [hs : AState s]
(h : ∃ p s₁, sys.tr s p = some s₁ ∧ P s₁) :
∃ s₁, sys.tr s (aSeek P |>.f s) = some s₁ ∧ P s₁ := by
  simp [aSeek]
  rw [choose?_eq_of_exi]
  rotate_left; exact h
  simp
  have h₁ := Classical.epsilon_spec h
  generalize hp : Classical.epsilon (λ p => ∃ s₁, sys.tr s p = some s₁ ∧ P s₁) = p at h₁ ⊢
  choose s₁ h₁ h₂ using h₁
  simpa [sys.validTr_of_eq_some h₁, h₁]

theorem AState.ne_of_tr {s s₁ p} [hs : AState s]
(h : sys.tr s p = some s₁) : p ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

theorem AState.aPos_ne_of_tr {s s₁ p} [hs : AState s]
(h : sys.tr s p = some s₁) : s₁.aPos ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

theorem AState.exi_dState_of_aSimPtsNcard_eq_succ
{s : State} {st : Strat} {set n} [hs : AState s] [hst : st.WF]
(h : s.aSimPtsNcard st set = some (n + 1)) : ∃ n s₁,
sys.simulate st.f s (n * 2 + 1) = (s₁, 0) ∧ s₁.aPos ∈ set ∧ ∀ k s₂, 2 ≤ k →
sys.simulate st.f s₁ k = (s₂, 0) → s₂.aPos ∉ set := by
  rw [State.aSimPtsNcard, Set.ncard?] at h; split_ifs at h with h₁
  simp at h ⊢
  replace h := congrArg (· = 0) h; simp at h
  replace h := Set.nonempty_of_ncard_ne_zero h
  rw [State.finite_filter_aSimPairs_iff_image_length_hist] at h₁
  rw [State.nonempty_filter_aSimPairs_iff_image_length_hist] at h
  have h₂ := Set.exi_max h₁ h
  clear h₁ h n
  simp only [Set.mem_image, Set.mem_filter, Prod.exists, exists_and_right, forall_exists_index,
    and_imp, exists_exists_and_eq_and] at h₂
  obtain ⟨s₁, ⟨p, h₁, h₂⟩, h₃⟩ := h₂
  rw [State.mem_aSimPairs_iff_simulate_tr] at h₁
  rcases h₁ with ⟨hs₁, n, h₁, s₂, h₄, rfl⟩
  have hs₂ := DState.of_tr h₄
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
  obtain ⟨s₃, h₅⟩ := st.d.validTr s₂
  have hs₃ := AState.of_tr h₅
  use n, s₂
  simp [h₁, h₄]
  split_ands
  · rwa [AState.aPos_eq_of_tr h₄]
  intro k s' hk h₆
  iterate 2 cases k; simp at hk; nm k
  clear hk
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h₆
  simp at h₆
  obtain ⟨sd, ⟨sa, H₁, H₂⟩, H₃⟩ := h₆
  have hsa : sys.WF sa := sys.wf_of_simulate_eq H₁
  have hsd := sys.wf_of_tr H₂
  replace hs' := s'.aState_or_dState; rcases hs' with hs' | hs'
  · replace hsd := DState.of_tr' H₃
    replace hsa := AState.of_tr' H₂
    simp at H₂ H₃
    specialize h₃ sa.hist.length sa (st.a.f sa) _
    · rw [State.mem_aSimPairs_iff_simulate_tr]
      use hsa, n * 2 + 1 + k
      simp [*]
    contrapose! h₃
    simp
    split_ands
    · rw [DState.aPos_eq_of_tr H₃, AState.aPos_eq_of_tr H₂] at h₃
      exact h₃
    rw [State.length_hist_eq_of_simulate_eq H₁, length_hist_eq_of_tr h₄]
    omega
  · rename' sa => sd, sd => sa, hsa => hsd, hsd => hsa
    replace hsa := AState.of_tr' H₃
    replace hsd := DState.of_tr' H₂
    simp at H₂ H₃
    specialize h₃ sa.hist.length sa (st.a.f sa) _
    · rw [State.mem_aSimPairs_iff_simulate_tr]
      use hsa, n * 2 + 1 + k + 1
      simp [*]
    contrapose! h₃
    simp
    split_ands
    · rwa [←AState.aPos_eq_of_tr H₃]
    rw [length_hist_eq_of_tr H₂, State.length_hist_eq_of_simulate_eq H₁, length_hist_eq_of_tr h₄]
    omega

theorem AState.exi_aState_of_aSimPtsNcard_eq_succ
{s : State} {st : Strat} {set n} [hs : AState s] [hst : st.WF]
(h : s.aSimPtsNcard st set = some (n + 1)) : ∃ n s₁,
sys.simulate st.f s (n * 2) = (s₁, 0) ∧ s₁.aPos ∈ set ∧ ∀ k s₂, k ≠ 0 →
sys.simulate st.f s₁ k = (s₂, 0) → s₂.aPos ∉ set := by
  choose k s₁ h₁ h₂ h₃ using exi_dState_of_aSimPtsNcard_eq_succ h
  use k + 1
  simp at h₁
  choose s' h₁ h₄ using h₁
  have hs' := AState.of_simulate_mul_two_eq_full h₁
  have hs₁ := DState.of_tr h₄
  simp at h₄
  obtain ⟨s₂, h₅⟩ : sys.validTr s₁ # st.d.f s₁; simp
  use s₂
  simp_rw [Nat.add_mul]
  simp [h₁, h₄, h₅, DState.aPos_eq_of_tr h₅, h₂]
  intro r s₃ hr h₆
  apply h₃ (r + 1) s₃ (by omega)
  rw [sys.simulate_succ_full']
  simpa [h₅]

theorem AState.getd_aSimPtsNcard_lt_of_odd {s st₁ st₂ set} (n : ℕ)
[hs : AState s] (hn : Odd n) (h₁ : s.aWins st₁) (h₂ : s.aWins st₂)
(h₃ : s.aSimPtsNcard st₁ set |>.isSome) (h₄ : s.aSimPtsNcard st₂ set |>.isSome)
(h₅ : ∀ k s₁ s₂, sys.simulate st₁.f s k = (s₁, 0) → sys.simulate st₂.f s k = (s₂, 0) →
s₁.aPos ∈ set → s₂.aPos ∈ set) (h₆ : ∀ s₁, sys.simulate st₁.f s n = (s₁, 0) → s₁.aPos ∉ set)
(h₇ : ∀ s₁, sys.simulate st₂.f s n = (s₁, 0) → s₁.aPos ∈ set) :
(s.aSimPtsNcard st₁ set).getd < (s.aSimPtsNcard st₂ set).getd := by
  obtain ⟨n, rfl⟩ := Nat.odd_iff_exi.mp hn; clear hn
  rw [Option.isSome_iff_exists] at h₃ h₄
  rcases h₃, h₄ with ⟨⟨N₁, h₃⟩, ⟨N₂, h₄⟩⟩
  simp [h₃, h₄, Option.getd]
  simp [State.aSimPtsNcard, Set.ncard?] at h₃ h₄
  rcases h₃ with ⟨H₁, rfl⟩
  rcases h₄ with ⟨H₃, rfl⟩
  rw [State.finite_filter_aSimPairs_iff_image_length_hist] at H₁ H₃
  simp_rw [State.ncard_filter_aSimPairs_eq_image_length_hist]
  apply Set.ncard_lt_ncard _ H₃
  clear H₁ H₃
  replace h₆ : ∃ sd₁, sys.simulate st₁.f s (n * 2 + 1) = (sd₁, 0) ∧ sd₁.aPos ∉ set
  · specialize h₁ (n * 2 + 1); grind
  replace h₇ : ∃ sd₂, sys.simulate st₂.f s (n * 2 + 1) = (sd₂, 0) ∧ sd₂.aPos ∈ set
  · specialize h₂ (n * 2 + 1); grind
  choose sd₁ G₁ G₂ using h₆
  choose sd₂ G₃ G₄ using h₇
  simp at G₁ G₃
  choose sa₁ G₁ G₅ using G₁
  choose sa₂ G₃ G₆ using G₃
  have hsa₁ := AState.of_simulate_mul_two_eq_full G₁
  have hsa₂ := AState.of_simulate_mul_two_eq_full G₃
  have hsd₁ := DState.of_tr G₅
  have hsd₂ := DState.of_tr G₆
  simp at G₅ G₆
  apply Set.ssubset_of # s.hist.length + n * 2
  · intro k hk
    simp at hk ⊢
    obtain ⟨s₁, ⟨p, H₁, H₂⟩, hk⟩ := hk
    have h₂' := h₂
    specialize h₂ (k - s.hist.length)
    generalize hr : sys.simulate st₂.f s (k - s.hist.length) = r
    rcases r with ⟨s₁', r⟩
    simp [hr] at h₂; subst h₂
    rw [State.mem_aSimPairs_iff_simulate_tr] at H₁
    choose hs₁ c H₁ H₃ using H₁
    simp [State.length_hist_eq_of_simulate_eq H₁] at hk
    subst hk
    simp at hr
    obtain ⟨s₂, H₃, rfl⟩ := H₃
    have hs₁' : AState s₁'
    · obtain ⟨c, rfl⟩ := Nat.even_iff_exi.mp # AState.even_of_simulate H₁
      exact AState.of_simulate_mul_two_eq_full hr
    specialize h₂' (c + 1)
    simp [hr] at h₂'
    choose s₂' H₄ using h₂'
    refine ⟨s₁', ⟨st₂.f s₁', ?_, ?_⟩, ?_⟩
    · rw [State.mem_aSimPairs_iff_simulate_tr]
      use hs₁'
      use c, hr, s₂', H₄
      simp
    · simp
      rw [←AState.aPos_eq_of_tr H₄]
      specialize h₅ (c + 1)
      simp [H₁, hr, H₃, H₄] at h₅
      apply h₅
      rwa [AState.aPos_eq_of_tr H₃]
    · simp [State.length_hist_eq_of_simulate_eq hr]
  · simp
    intro S p H₁ H₂ H₃
    rw [State.mem_aSimPairs_iff_simulate_tr] at H₁
    choose hS k H₁ S' H₄ H₅ using H₁
    subst H₅
    simp [State.length_hist_eq_of_simulate_eq H₁] at H₃
    subst H₃
    simp [G₁] at H₁
    subst H₁
    simp [AState.aPos_eq_of_tr G₅, H₂] at G₂
  · simp
    refine ⟨sa₂, ⟨st₂.a.f sa₂, ?_, ?_⟩, ?_⟩
    · rw [State.mem_aSimPairs_iff_simulate_tr]
      use hsa₂, n * 2, G₃
      simp [G₆]
    · rwa [←AState.aPos_eq_of_tr G₆]
    · rw [State.length_hist_eq_of_simulate_eq G₃]; rfl

theorem AState.getd_aSimPtsNcard_lt_of {s st₁ st₂ set} (n : ℕ)
[hs : AState s] (h₁ : s.aWins st₁) (h₂ : s.aWins st₂)
(h₃ : s.aSimPtsNcard st₁ set |>.isSome) (h₄ : s.aSimPtsNcard st₂ set |>.isSome)
(h₅ : ∀ k s₁ s₂, sys.simulate st₁.f s k = (s₁, 0) → sys.simulate st₂.f s k = (s₂, 0) →
s₁.aPos ∈ set → s₂.aPos ∈ set) (h₆ : ∀ s₁, sys.simulate st₁.f s n = (s₁, 0) → s₁.aPos ∉ set)
(h₇ : ∀ s₁, sys.simulate st₂.f s n = (s₁, 0) → s₁.aPos ∈ set) :
(s.aSimPtsNcard st₁ set).getd < (s.aSimPtsNcard st₂ set).getd := by
  induction n using Nat.mod_2_ind <;> nm n
  rotate_left
  · apply getd_aSimPtsNcard_lt_of_odd (n * 2 + 1) <;> try assumption;; simp
  generalize hk : n * 2 - 1 = k
  replace hk : n * 2 = k + 1
  · cases n
    · simp at h₆ h₇; contradiction
    nm n; omega
  rw [hk] at h₆ h₇
  obtain ⟨m, hm⟩ : ∃ m, k = m * 2 + 1
  · rw [←Nat.odd_iff_exi, Nat.odd_iff]; omega
  apply getd_aSimPtsNcard_lt_of_odd k <;> try assumption
  · simp [hm]
  · intro s₁ H₁
    specialize h₁ (k + 1)
    simp [H₁] at h₁
    choose s₂ h₁ using h₁
    rw [hm] at H₁
    have hs₁ := DState.of_simulate_mul_two_add_one_eq_full H₁
    rw [←DState.aPos_eq_of_tr h₁]
    apply h₆
    rw [←hm] at H₁
    simp at h₁
    simpa [H₁]
  · intro s₁ H₁
    specialize h₂ (k + 1)
    simp [H₁] at h₂
    choose s₂ h₂ using h₂
    rw [hm] at H₁
    have hs₁ := DState.of_simulate_mul_two_add_one_eq_full H₁
    rw [←DState.aPos_eq_of_tr h₂]
    apply h₇
    rw [←hm] at H₁
    simp at h₂
    simpa [H₁]

theorem State.validTr_of_mem_aSimPairs {s s' p st} [hs : sys.WF s]
(h : (s', p) ∈ s.aSimPairs st) : sys.validTr s' p := by
  rw [mem_aSimPairs_iff_simulate_tr] at h; rw [sys.validTr_iff_isSome]; grind

theorem steps_eq_of_simulate_full_eq {s s₁ n m f} [hs : sys.WF s]
(h₁ : sys.simulate f s n = (s₁, 0)) (h₂ : sys.simulate f s m = (s₁, 0)) : n = m := by
  rw [←length_hist_sub_eq_of_simulate h₁, length_hist_sub_eq_of_simulate h₂]

theorem State.mem_simStatesRangeAux_iff {s s₁ s' : State} {st r n} [hr : DecidableRel r]
(h : sys.simulate st.f s n = (s₁, 0)) : s' ∈ s.simStatesRangeAux r s₁ st ↔
s' ∈ s.simStates st ∧ s' ∈ (s.simStates st |>.filter (λ s₃ =>
s₃.hist.length ≤ s₁.hist.length ∧ r s₃.hist.length s₁.hist.length)) := by
  have h' : ∃ n, sys.simulate st.f s n = (s₁, 0) := ⟨_, h⟩
  simp [simStatesRangeAux, h', diff_eq_of_simulate_full h]
  constructor
  · rintro ⟨⟨k, hk, h₂⟩, h₃⟩
    simp [Prod.ext_iff]
    generalize hc : sys.simulate st.f s k = c at h₂
    rcases c with ⟨s', c⟩; simp at h₂; subst h₂
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
    simp [hc] at h
    rcases h with ⟨rfl, h⟩
    split_ands
    · use k
      simp [hc]
    · apply length_hist_le_of_reachable
      exact sys.reachable_of_simulate_eq h
    · exact h₃
  · rintro ⟨⟨k, h₁⟩, h₂, h₃⟩
    simp [h₃]
    use k
    simp [h₁]
    have := length_hist_eq_of_simulate_eq h
    have := length_hist_eq_of_simulate_eq h₁
    omega

theorem State.mem_simStatesIcc_iff_of {s s₁ s₂ : State} {st : Strat} {n}
(h : sys.simulate st.f s n = (s₁, 0)) : s₂ ∈ s.simStatesIcc s₁ st ↔
∃ k, k ≤ n ∧ sys.simulate st.f s k = (s₂, 0) := by
  simp [simStatesIcc, mem_simStatesRangeAux_iff h]; constructor
  · rintro ⟨⟨k, h₁⟩, h₂⟩; use k; simp [h₁]; have := length_hist_eq_of_simulate_eq h
    have := length_hist_eq_of_simulate_eq h₁; omega
  · rintro ⟨k, h₁, h₂⟩; use by use k;; have := length_hist_eq_of_simulate_eq h
    have := length_hist_eq_of_simulate_eq h₂; omega

theorem State.mem_simStatesIco_iff_of {s s₁ s₂ : State} {st : Strat} {n}
(h : sys.simulate st.f s n = (s₁, 0)) : s₂ ∈ s.simStatesIco s₁ st ↔
∃ k, k < n ∧ sys.simulate st.f s k = (s₂, 0) := by
  simp [simStatesIco, mem_simStatesRangeAux_iff h]; constructor
  · rintro ⟨⟨k, h₁⟩, h₂⟩; use k; simp [h₁]; have := length_hist_eq_of_simulate_eq h
    have := length_hist_eq_of_simulate_eq h₁; omega
  · rintro ⟨k, h₁, h₂⟩; use by use k;; have := length_hist_eq_of_simulate_eq h
    have := length_hist_eq_of_simulate_eq h₂; omega

theorem State.mem_aSimStatesIcc_iff_of {s s₁ s₂ : State} {st : Strat} {n} [hs : sys.WF s]
(h : sys.simulate st.f s n = (s₁, 0)) : s₂ ∈ s.aSimStatesIcc s₁ st ↔ AState s₂ ∧
∃ k, k ≤ n ∧ sys.simulate st.f s k = (s₂, 0) := by
  simp [aSimStatesIcc, mem_simStatesIcc_iff_of h]
  rw [and_comm]; constructor
  · rintro ⟨h₁, k, hk, h₂⟩
    have hs₂ := sys.wf_of_simulate_eq h₂
    rw [aTurn_iff_aState] at h₁; tauto
  · rintro ⟨h₁, k, hk, h₂⟩; simp; tauto

theorem State.mem_aSimStatesIco_iff_of {s s₁ s₂ : State} {st : Strat} {n} [hs : sys.WF s]
(h : sys.simulate st.f s n = (s₁, 0)) : s₂ ∈ s.aSimStatesIco s₁ st ↔ AState s₂ ∧
∃ k, k < n ∧ sys.simulate st.f s k = (s₂, 0) := by
  simp [aSimStatesIco, mem_simStatesIco_iff_of h]
  rw [and_comm]; constructor
  · rintro ⟨h₁, k, hk, h₂⟩
    have hs₂ := sys.wf_of_simulate_eq h₂
    rw [aTurn_iff_aState] at h₁; tauto
  · rintro ⟨h₁, k, hk, h₂⟩; simp; tauto

theorem State.mem_simStatesIcc_iff {s s₁ s₂ : State} {st : Strat} [hs : sys.WF s] :
s₁ ∈ s.simStatesIcc s₂ st ↔ ∃ k n, k ≤ n ∧ sys.simulate st.f s k = (s₁, 0) ∧
sys.simulate st.f s n = (s₂, 0) := by
  by_cases h₁ : ∃ n, sys.simulate st.f s n = (s₂, 0)
  · choose n h₁ using h₁
    rw [mem_simStatesIcc_iff_of h₁]
    constructor
    · rintro ⟨k, hk, h₂⟩
      use k, n
    · rintro ⟨k, n', hk, h₂, h₃⟩
      cases steps_eq_of_simulate_full_eq h₁ h₃
      use k
  · simp [simStatesIcc, simStatesRangeAux, h₁]
    push_neg at h₁
    intro k n hk h₂
    apply h₁

theorem State.mem_simStatesIco_iff {s s₁ s₂ : State} {st : Strat} [hs : sys.WF s] :
s₁ ∈ s.simStatesIco s₂ st ↔ ∃ k n, k < n ∧ sys.simulate st.f s k = (s₁, 0) ∧
sys.simulate st.f s n = (s₂, 0) := by
  by_cases h₁ : ∃ n, sys.simulate st.f s n = (s₂, 0)
  · choose n h₁ using h₁
    rw [mem_simStatesIco_iff_of h₁]
    constructor
    · rintro ⟨k, hk, h₂⟩
      use k, n
    · rintro ⟨k, n', hk, h₂, h₃⟩
      cases steps_eq_of_simulate_full_eq h₁ h₃
      use k
  · simp [simStatesIco, simStatesRangeAux, h₁]
    push_neg at h₁
    intro k n hk h₂
    apply h₁

theorem State.mem_aSimStatesIcc_iff {s s₁ s₂ : State} {st : Strat} [hs : sys.WF s] :
s₁ ∈ s.aSimStatesIcc s₂ st ↔ AState s₁ ∧ ∃ k n, k ≤ n ∧ sys.simulate st.f s k = (s₁, 0) ∧
sys.simulate st.f s n = (s₂, 0) := by
  simp [aSimStatesIcc, mem_simStatesIcc_iff]; rw [and_comm]; constructor
  · rintro ⟨ht, k, n, hk, h₁, h₂⟩; have hs₁ := sys.wf_of_simulate_eq h₁
    rw [aTurn_iff_aState] at ht; use ht, k, n
  · rintro ⟨hs₁, h⟩; simpa

theorem State.mem_aSimStatesIco_iff {s s₁ s₂ : State} {st : Strat} [hs : sys.WF s] :
s₁ ∈ s.aSimStatesIco s₂ st ↔ AState s₁ ∧ ∃ k n, k < n ∧ sys.simulate st.f s k = (s₁, 0) ∧
sys.simulate st.f s n = (s₂, 0) := by
  simp [aSimStatesIco, mem_simStatesIco_iff]; rw [and_comm]; constructor
  · rintro ⟨ht, k, n, hk, h₁, h₂⟩; have hs₁ := sys.wf_of_simulate_eq h₁
    rw [aTurn_iff_aState] at ht; use ht, k, n
  · rintro ⟨hs₁, h⟩; simpa

@[simp]
theorem State.simulate_full_eq_self_iff {s : State} {f n} :
sys.simulate f s n = (s, 0) ↔ n = 0 := by
  symm; constructor; rintro ⟨rfl, rfl⟩; simp
  intro h; have := length_hist_eq_of_simulate_eq h; omega

@[simp]
theorem State.mem_simStatesIcc_self_iff {s s' : State} {st} [hs : sys.WF s] :
s' ∈ s.simStatesIcc s st ↔ s' = s := by
  simp [mem_simStatesIcc_iff]; constructor
  · rintro ⟨k, n, hk, h₁, h₂⟩; rfl
  · rintro rfl; rfl

theorem State.exi_aPos_simulate_eq_of_aPos_simulate_ne {s s₁ : State} {f n}
[hs : sys.WF s] (h₁ : sys.simulate f s n = (s₁, 0)) (h₂ : s₁.aPos ≠ s.aPos) :
∃ k < n, ∃ s₀ s', AState s₀ ∧ DState s' ∧ sys.simulate f s k = (s₀, 0) ∧
sys.tr s₀ (f s₀) = some s' ∧ s'.aPos = s₁.aPos := by
  induction n generalizing s₁
  · simp at h₁; simp [h₁] at h₂
  nm n ih; rename' s₁ => s₂; simp at h₁; rcases h₁ with ⟨s₁, h₁, h₃⟩
  have hs₁ := sys.wf_of_simulate_eq h₁; replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  · have hs₂ := DState.of_tr h₃; use n, by simp, s₁, s₂
  · specialize ih h₁; rw [DState.aPos_eq_of_tr h₃] at h₂ ⊢
    specialize ih h₂; choose k hk s₀ s' hs₀ hs' h₄ h₅ h₆ using ih
    use k, by omega, s₀, s'

theorem State.mem_aVisitedIcc_of_mem_simStatesIcc {s s' s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0))
(h₂ : s' ∈ s.simStatesIcc s₁ st) : s'.aPos ∈ s.aVisitedIcc s₁ := by
  rw [mem_simStatesIcc_iff_of h₁] at h₂; choose k hk h₂ using h₂
  rw [mem_aVisitedIcc_iff_of h₁, or_iff_not_imp_left]; intro h₃
  choose r hr s₀ s₂ hs₀ hs₂ h₄ h₅ h₆ using exi_aPos_simulate_eq_of_aPos_simulate_ne h₂ h₃
  use r, by omega, s₀, hs₀, h₄; rwa [←AState.aPos_eq_of_tr h₅]

theorem State.mem_aVisitedIcc_iff_mem_simStatesIcc {s s₁ : State} {st : Strat} {n p}
[hs : sys.WF s] (h : sys.simulate st.f s n = (s₁, 0)) :
p ∈ s.aVisitedIcc s₁ ↔ ∃ s' ∈ s.simStatesIcc s₁ st, s'.aPos = p := by
  symm; constructor; rintro ⟨s', h₁, rfl⟩; exact mem_aVisitedIcc_of_mem_simStatesIcc h h₁
  rw [mem_aVisitedIcc_iff_of h]; intro h₁; simp [mem_simStatesIcc_iff]
  rcases h₁ with (rfl | ⟨k, hk, s', hs', h₁, rfl⟩); use s; simp; use n
  replace hk : ∃ r, k + 1 + r = n; use n - k - 1; omega
  obtain ⟨n, rfl⟩ := hk; simp [h₁] at h; choose s' h h₂ using h
  nm s₀; simp [←AState.aPos_eq_of_tr h]; use s'
  simp; use k + 1, k + 1 + n, by omega;; simpa [h₁, h]

theorem State.mem_simStatesIcc_of_mem_simStatesIco {s s₁ s' : State} {st} [hs : sys.WF s]
(h : s' ∈ s.simStatesIco s₁ st) : s' ∈ s.simStatesIcc s₁ st := by
  rw [mem_simStatesIco_iff] at h; rw [mem_simStatesIcc_iff]
  choose k n hk h₁ h₂ using h; use k, n, by omega

theorem State.mem_aSimStatesIcc_of_mem_aSimStatesIco {s s₁ s' : State} {st} [hs : sys.WF s]
(h : s' ∈ s.aSimStatesIco s₁ st) : s' ∈ s.aSimStatesIcc s₁ st := by
  rw [mem_aSimStatesIco_iff] at h; rw [mem_aSimStatesIcc_iff]
  choose hs' k n hk h₁ h₂ using h; use hs', k, n, by omega

theorem State.simStatesIco_subset_simStatesIcc {s s₁ : State} {st} [hs : sys.WF s] :
s.simStatesIco s₁ st ⊆ s.simStatesIcc s₁ st :=
  λ _ => mem_simStatesIcc_of_mem_simStatesIco

theorem State.aSimStatesIco_subset_aSimStatesIcc {s s₁ : State} {st} [hs : sys.WF s] :
s.aSimStatesIco s₁ st ⊆ s.aSimStatesIcc s₁ st :=
  λ _ => mem_aSimStatesIcc_of_mem_aSimStatesIco

theorem State.simStatesIco_eq_erase_simStatesIcc {s s₁ : State} {st} [hs : sys.WF s] :
s.simStatesIco s₁ st = (s.simStatesIcc s₁ st).erase s₁ := by
  ext s'; simp [mem_simStatesIco_iff, mem_simStatesIcc_iff]; constructor
  · rintro ⟨k, n, hk, h₁, h₂⟩
    symm; split_ands; use k, n, by omega
    rintro rfl
    simp [steps_eq_of_simulate_full_eq h₁ h₂] at hk
  · rintro ⟨h, k, n, hk, h₁, h₂⟩
    use k, n
    split_ands <;> try assumption
    contrapose! h
    replace h : n = k; omega
    simp [h, h₁] at h₂
    exact h₂

theorem State.aSimStatesIco_eq_erase_aSimStatesIcc {s s₁ : State} {st} [hs : sys.WF s] :
s.aSimStatesIco s₁ st = (s.aSimStatesIcc s₁ st).erase s₁ := by
  unfold aSimStatesIco aSimStatesIcc
  rw [simStatesIco_eq_erase_simStatesIcc]
  ext; simp; tauto

theorem State.mem_simStatesIco_mem_simStatesIcc_and_ne {s s₁ s' : State} {st} [hs : sys.WF s]
(h₁ : s' ∈ s.simStatesIcc s₁ st) (h₂ : s' ≠ s₁) : s' ∈ s.simStatesIco s₁ st := by
  simp [simStatesIco_eq_erase_simStatesIcc]; tauto

theorem State.mem_aSimStatesIco_of_mem_aSimStatesIcc_and_ne {s s₁ s' : State} {st} [hs : sys.WF s]
(h₁ : s' ∈ s.aSimStatesIcc s₁ st) (h₂ : s' ≠ s₁) : s' ∈ s.aSimStatesIco s₁ st := by
  simp [aSimStatesIco_eq_erase_aSimStatesIcc]; tauto

theorem State.mem_simStatesIcc_of_mem_aSimStatesIcc {s s₁ s' : State} {st}
(h : s' ∈ s.aSimStatesIcc s₁ st) : s' ∈ s.simStatesIcc s₁ st := by
  simp [aSimStatesIcc] at h; exact h.1

theorem State.mem_simStatesIco_of_mem_aSimStatesIco {s s₁ s' : State} {st}
(h : s' ∈ s.aSimStatesIco s₁ st) : s' ∈ s.simStatesIco s₁ st := by
  simp [aSimStatesIco] at h; exact h.1

theorem State.mem_aVisitedIcc_of_mem_aSimStatesIcc {s s' s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0))
(h₂ : s' ∈ s.aSimStatesIcc s₁ st) : s'.aPos ∈ s.aVisitedIcc s₁ :=
  mem_aVisitedIcc_of_mem_simStatesIcc h₁ # mem_simStatesIcc_of_mem_aSimStatesIcc h₂

theorem State.mem_aVisitedIcc_of_mem_aSimStatesIco {s s' s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0))
(h₂ : s' ∈ s.aSimStatesIco s₁ st) : s'.aPos ∈ s.aVisitedIcc s₁ :=
  mem_aVisitedIcc_of_mem_aSimStatesIcc h₁ # mem_aSimStatesIcc_of_mem_aSimStatesIco h₂

theorem wf_of_mem_simStates {s s' : State} {st} [hs : sys.WF s]
(h : s' ∈ s.simStates st) : sys.WF s' := by
  rw [State.mem_simStates_iff] at h; choose n h using h; exact sys.wf_of_simulate_eq h

theorem wf_of_mem_simStatesRangeAux {s s₁ s' : State} {st r} [hr : DecidableRel r] [hs : sys.WF s]
(h : s' ∈ s.simStatesRangeAux r s₁ st) : sys.WF s' := by
  simp [State.simStatesRangeAux] at h; split_ifs at h with h₁ <;> simp at h
  obtain ⟨⟨-, -, rfl⟩, -⟩ := h; infer_instance

theorem wf_of_mem_simStatesIcc {s s₁ s' : State} {st} [hs : sys.WF s]
(h : s' ∈ s.simStatesIcc s₁ st) : sys.WF s' :=
  wf_of_mem_simStatesRangeAux h

theorem wf_of_mem_simStatesIco {s s₁ s' : State} {st} [hs : sys.WF s]
(h : s' ∈ s.simStatesIco s₁ st) : sys.WF s' :=
  wf_of_mem_simStatesRangeAux h

theorem State.mem_aVisitedIcc_iff_mem_aSimStatesIcc {s s₁ : State} {st : Strat} {n p}
[hs : sys.WF s] [hs₁ : AState s₁] (h : sys.simulate st.f s n = (s₁, 0)) :
p ∈ s.aVisitedIcc s₁ ↔ ∃ s' ∈ s.aSimStatesIcc s₁ st, s'.aPos = p := by
  symm; constructor; rintro ⟨s', h₂, rfl⟩; exact mem_aVisitedIcc_of_mem_aSimStatesIcc h h₂
  intro h₁
  rw [mem_aVisitedIcc_iff_of h] at h₁
  simp [mem_aSimStatesIcc_iff]
  simp [and_assoc]
  rcases h₁ with (rfl | ⟨k, hk, s', hs', h₁, rfl⟩)
  · replace hs := s.aState_or_dState
    rcases hs with hs | hs
    · use s
      simp
      use hs, n
    cases n
    · simp at h
      subst h
      cases s.false_of_aState_and_dState
    nm n
    rw [add_comm] at h
    simp at h
    choose s' h₁ h₃ using h
    have hs' := AState.of_tr h₁
    use s'
    simp [hs', DState.aPos_eq_of_tr h₁]
    use 1, 1 + n, by simp
    simp; tauto
  replace hk : ∃ r, k + 1 + r = n; use n - k - 1; omega
  obtain ⟨n, rfl⟩ := hk; simp [h₁] at h; choose s' h h₂ using h
  nm s₀; simp [←AState.aPos_eq_of_tr h]
  cases n
  · simp at h₂
    subst h₂
    have h₁ := DState.of_tr h
    cases s'.false_of_aState_and_dState
  nm n
  rw [add_comm] at h₂
  simp at h₂
  choose s₂ h₂ h₃ using h₂
  rename' hs' => hs₀
  have hs' := sys.wf_of_tr h
  replace hs' := s'.aState_or_dState
  rcases hs' with hs' | hs'
  · use s', hs'
    simp
    use k + 1, k + 2 + n, by omega
    simp at h₂
    simpa [h, h₁, h₂]
  · have hs₂ := AState.of_tr h₂
    use s₂, hs₂
    simp [←DState.aPos_eq_of_tr h₂]
    use k + 2, k + 2 + n, by omega
    simp at h₂
    simpa [h, h₁, h₂]

theorem State.wf_prev_of_reachable_and_ne {s s₁ : State} [hs : sys.WF s]
(h₁ : sys.Reachable s s₁) (h₂ : s ≠ s₁) : sys.WF s₁.prev := by
  have hs₁ := sys.wf_of_reachable h₁
  apply wf_prev
  rw [System.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  cases ps
  · simp [h₂] at h₁
  nm p ps
  rw [isInit_iff_length_hist_eq_one]
  rw [length_hist_eq_of_trs_eq h₁]
  simp
  suffices : s.hist.length ≠ 0; omega
  simp

theorem State.reachable_prev_of_reachable_and_ne {s s₁ : State} [hs : sys.WF s]
(h₁ : sys.Reachable s s₁) (h₂ : s ≠ s₁) : sys.Reachable s s₁.prev := by
  rw [System.reachable_iff_exi_trs] at h₁ ⊢
  choose ps h₁ using h₁
  induction ps using List.reverseRecOn
  · simp [h₂] at h₁
  nm ps p ih; clear ih
  simp at h₁
  choose s' h₁ h₃ using h₁
  use ps
  simp [h₁]
  have hs' := sys.wf_of_trs h₁
  rw [prev_eq_of_tr h₃]

theorem State.mem_aVisitedIcc'_append {s : State} {ps₁ ps₂ p}
(h : p ∈ s.aVisitedIcc' ps₁) : p ∈ s.aVisitedIcc' (ps₁ ++ ps₂) := by
  induction ps₁ generalizing s
  · simp at h
  nm p₁ ps₁ ih
  simp [aVisitedIcc'] at h ⊢
  split_ifs at h ⊢ with h₁
  · simp at h ⊢
    rcases h with rfl | h
    · left; rfl
    right
    exact ih h
  exact ih h

theorem State.mem_aVisitedIcc_of_mem_aVisitedIco {s s₁ : State} {p} [hs : sys.WF s]
(h₁ : sys.Reachable s s₁) (h₂ : p ∈ s.aVisitedIco s₁) : p ∈ s.aVisitedIcc s₁ := by
  rw [aVisitedIco] at h₂
  split_ifs at h₂ with h₃
  · simp at h₂
  unfold aVisitedIcc at h₂ ⊢
  simp [h₁]
  have hs₁ := sys.wf_of_reachable h₁
  have hsp := wf_prev_of_reachable_and_ne h₁ h₃
  simp [reachable_prev_of_reachable_and_ne h₁ h₃] at h₂
  rcases h₂ with rfl | h₂
  · simp
  right
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  induction ps using List.reverseRecOn
  · simp [h₃] at h₁
  nm ps p₁ ih; clear ih
  simp at h₁
  choose s' h₁ h₄ using h₁
  have hs' := sys.wf_of_trs h₁
  rw [prev_eq_of_tr h₄] at h₂
  rw [diffTrs_eq_of_tr h₄ # sys.reachable_of_trs h₁]
  exact mem_aVisitedIcc'_append h₂

set_option linter.unusedVariables false in
theorem State.false_of_simulate_eq_simulate (s f s₁ s₂ n m) [hs : sys.WF s]
(h₁ : sys.simulate f s n = (s₁, 0)) (h₂ : sys.simulate f s m = (s₁, 0))
(h₃ : s₁ = s₂) (h₄ : n ≠ m) : False := by
  subst h₃; exact h₄ # steps_eq_of_simulate_full_eq h₁ h₂

theorem State.mem_aVisitedIco_iff_of {s f n s₁ p} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, 0)) : p ∈ s.aVisitedIco s₁ ↔ (n ≠ 0 ∧ p = s.aPos) ∨
∃ k, k + 1 < n ∧ ∃ s', AState s' ∧ sys.simulate f s k = (s', 0) ∧ f s' = p := by
  unfold aVisitedIco
  cases n
  · simp at h
    simp [h]
  nm n
  simp at h
  choose s' h₁ h₂ using h
  rw [if_neg]; rotate_left
  · rintro rfl
    apply s.false_of_simulate_eq_simulate f s s 0 (n + 1) <;> simp_all
  have hs₁ := sys.wf_of_simulate_eq h₁; dsimp at hs₁
  rw [prev_eq_of_tr h₂, mem_aVisitedIcc_iff_of h₁]; grind

theorem State.mem_aVisitedIco_of_mem_simStatesIco {s s' s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0))
(h₂ : s' ∈ s.simStatesIco s₁ st) : s'.aPos ∈ s.aVisitedIco s₁ := by
  rw [mem_simStatesIco_iff_of h₁] at h₂; choose k hk h₂ using h₂
  rw [mem_aVisitedIco_iff_of h₁, or_iff_not_imp_left]; intro h₃
  rw [not_and_iff_or] at h₃
  simp at h₃
  rcases h₃ with rfl | h₃
  · simp at hk
  choose r hr s₀ s₂ hs₀ hs₂ h₄ h₅ h₆ using exi_aPos_simulate_eq_of_aPos_simulate_ne h₂ h₃
  use r, by omega, s₀, hs₀, h₄; rwa [←AState.aPos_eq_of_tr h₅]

theorem State.mem_aVisitedIco_iff_mem_simStatesIco {s s₁ : State} {st : Strat} {n p}
[hs : sys.WF s] (h : sys.simulate st.f s n = (s₁, 0)) :
p ∈ s.aVisitedIco s₁ ↔ ∃ s' ∈ s.simStatesIco s₁ st, s'.aPos = p := by
  symm; constructor; rintro ⟨s', h₁, rfl⟩; exact mem_aVisitedIco_of_mem_simStatesIco h h₁
  rw [mem_aVisitedIco_iff_of h]; intro h₁; simp [mem_simStatesIco_iff]
  rcases h₁ with (⟨hn, rfl⟩ | ⟨k, hk, s', hs', h₁, rfl⟩)
  · use s; simp; use n
    simp [h]
    omega
  replace hk : ∃ r, k + 2 + r = n; use n - k - 2; omega
  obtain ⟨n, rfl⟩ := hk; simp [h₁] at h; choose s' h h₂ using h
  nm s₀
  rename' hs' => hs₀
  choose sx h h₃ using h
  simp [←AState.aPos_eq_of_tr h]
  use sx
  simp
  use k + 1, k + 2 + n, by omega;;
  simpa [h₁, h, h₃]

@[simp]
theorem State.simStatesIco_self {s : State} {st} : s.simStatesIco s st = ∅ := by
  simp [simStatesIco, simStatesRangeAux]

@[simp]
theorem State.aSimStatesIco_self {s : State} {st} : s.aSimStatesIco s st = ∅ := by
  simp [aSimStatesIco]

@[simp]
theorem State.aVisitedIco_self {s : State} : s.aVisitedIco s = ∅ := by
  simp [aVisitedIco]

theorem State.simStatesIcc_eq_of_tr {s s₁} {st : Strat} [hs : sys.WF s]
(h : sys.tr s (st.f s) = some s₁) : s.simStatesIcc s₁ st = {s, s₁} := by
  have h' : sys.simulate st.f s 1 = (s₁, 0); simpa
  ext s'; simp [simStatesIcc, mem_simStatesRangeAux_iff h']; constructor
  · rintro ⟨⟨n, h₁⟩, h₂⟩; obtain rfl | rfl : n = 0 ∨ n = 1
    · have := length_hist_eq_of_tr h; have := length_hist_eq_of_simulate_eq h₁; omega
    all_goals simp [h] at h₁; grind
  · rintro (rfl | rfl); all_goals simp [length_hist_eq_of_tr h]
    clear h'; use 1; simpa

theorem State.simStatesIco_eq_of_tr {s s₁} {st : Strat}
(h : sys.tr s (st.f s) = some s₁) : s.simStatesIco s₁ st = {s} := by
  have h' : sys.simulate st.f s 1 = (s₁, 0); simpa
  ext s'; simp [simStatesIco, mem_simStatesRangeAux_iff h']; constructor
  · rintro ⟨⟨n, h₁⟩, h₂⟩; obtain rfl | rfl : n = 0 ∨ n = 1
    · have := length_hist_eq_of_tr h; have := length_hist_eq_of_simulate_eq h₁; omega
    all_goals simp [h] at h₁; grind
  · rintro (rfl | rfl); all_goals simp [length_hist_eq_of_tr h]

theorem State.simStatesIco_eq_simStatesIcc_prev_of {s s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0)) (h₂ : n ≠ 0) :
s.simStatesIco s₁ st = s.simStatesIcc s₁.prev st := by
  ext s'
  cases n
  · simp at h₂
  nm n
  clear h₂
  have h₁' := h₁
  simp at h₁
  choose sx h₁ h₃ using h₁
  have hsx := sys.wf_of_simulate_eq h₁; dsimp at hsx
  rw [prev_eq_of_tr h₃]
  simp [simStatesIco_eq_erase_simStatesIcc, simStatesIcc]
  simp [mem_simStatesRangeAux_iff h₁, mem_simStatesRangeAux_iff h₁']
  constructor
  · rintro ⟨h₄, ⟨k, h₅⟩, h₆⟩
    use by use k
    have := length_hist_eq_of_simulate_eq h₁
    have := length_hist_eq_of_simulate_eq h₅
    have := length_hist_eq_of_tr h₃
    have hk : k ≤ n + 1
    · omega
    rw [le_iff_eq_or_lt] at hk
    rcases hk with rfl | hk
    · rw [h₁'] at h₅
      grind
    omega
  · rintro ⟨⟨k, h₄⟩, h₅⟩
    rw [length_hist_eq_of_simulate_eq h₁] at h₅
    rw [length_hist_eq_of_simulate_eq h₄] at h₅
    simp at h₅
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₅
    clear h₅
    clear h₁'
    simp [h₄] at h₁
    have hs' := sys.wf_of_simulate_eq h₄
    dsimp at hs'
    split_ands
    · rintro rfl
      apply s'.false_of_simulate_eq_simulate st.f s' s' 0 (n + 1) <;> simp_all
    · use k
    · apply length_hist_le_of_reachable
      apply sys.reachable_of_simulate_eq h₁ |>.trans
      exact sys.reachable_of_tr h₃

theorem State.aSimStatesIco_eq_aSimStatesIcc_prev_of {s s₁ : State} {st : Strat} {n}
[hs : sys.WF s] (h₁ : sys.simulate st.f s n = (s₁, 0)) (h₂ : n ≠ 0) :
s.aSimStatesIco s₁ st = s.aSimStatesIcc s₁.prev st := by
  rw [aSimStatesIco, aSimStatesIcc, simStatesIco_eq_simStatesIcc_prev_of h₁ h₂]