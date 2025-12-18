import AP.AP.WF

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

@[simp]
theorem take_length_sub_one : xs.take (xs.length - 1) = xs.init := by
  induction xs using List.reverseRecOn <;> simp

@[simp]
theorem length_init : xs.init.length = xs.length - 1 := by
  induction xs using List.reverseRecOn <;> simp

-- #check 0 #exit

end List

namespace AP

def State.diff (s₁ s : State) : ℕ :=
  s₁.hist.length - s.hist.length

def State.diffTrs (s₁ s : State) : List PointZ :=
  s₁.hist.take (s₁.diff s) |>.reverse

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

def State.aVisited' (s : State) (ps : List PointZ) : Set' PointZ :=
  match ps with
  | [] => ∅
  | p :: ps =>
    let set := sys.tr s p |>.iget.aVisited' ps
    if s.aTurn then set.insert p else set

def State.aVisited (s s₁ : State) : Set' PointZ :=
  State.aVisited' s (s₁.diffTrs s) |>.insert s.aPos

def State.aPtsSimAt (s : State) (st : Strat) : Set (State × PointZ) :=
  {(s₁, p) | ∃ s₂, s.aMoveSim st s₁ = some (p, s₂)}

def State.aPtsSim (s : State) (st : Strat) : Set PointZ :=
  Prod.snd '' s.aPtsSimAt st

def State.init (s : State) : State :=
  initState s.pw s.aPos₀

def State.prev (s : State) : State :=
  sys.trs s.init (s.diffTrs s.init |>.init) |>.1

def State.lastMove (s : State) : PointZ :=
  s.diffTrs s.prev |>.getLast!

def State.IsInit (s : State) : Prop :=
  sys.Initial s

-- #check 0 #exit

-----

theorem State.diff_eq_of_simulate' {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s + r = n := by
  unfold diff
  rw [length_hist_eq_of_simulate_eq h]
  have h₁ := sys.snd_le_of_simulate_eq h
  omega

theorem State.diff_eq_of_simulate {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s = n - r := by
  have := diff_eq_of_simulate' h; omega

theorem State.diff_eq_of_simulate_full {s f n s₁}
(h : sys.simulate f s n = (s₁, 0)) : s₁.diff s = n :=
  diff_eq_of_simulate h

@[simp]
theorem State.length_diffTrs {s s₁ : State} : (s₁.diffTrs s).length = s₁.diff s := by
  simp [diffTrs, diff]

@[simp]
theorem State.diff_self {s : State} : s.diff s = 0 := by
  simp [diff]

@[simp]
theorem State.diffTrs_self {s : State} : s.diffTrs s = [] := by
  simp [diffTrs]

@[simp]
theorem State.aVisited'_nil {s : State} : s.aVisited' [] = ∅ := rfl

@[simp]
theorem State.aVisited_self {s : State} : s.aVisited s = Set'.singleton s.aPos := by
  simp [aVisited]

theorem State.diff_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diff s = s₁.diff s + 1 := by
  simp [diff, length_hist_eq_of_tr h]; have := length_hist_le_of_reachable h₁; omega

theorem State.diffTrs_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diffTrs s = s₁.diffTrs s ++ [p] := by
  simp [diffTrs, diff_eq_of_tr h h₁, hist_eq_of_tr h]

theorem State.diffTrs_eq_of_trs_full {s ps s₁}
(h : sys.trs s ps = (s₁, [])) : s₁.diffTrs s = ps := by
  induction ps using List.reverseRecOn generalizing s₁
  · simp at h; simp [h]
  nm ps p ih
  simp at h
  choose s' h₁ h₂ using h
  specialize ih h₁
  simpa [diffTrs_eq_of_tr h₂ # sys.reachable_of_trs h₁]

@[simp]
theorem State.aVisited'_singleton {s : State} {p} :
s.aVisited' [p] = if s.aTurn then Set'.singleton p else ∅ := by
  simp [aVisited']

theorem AState.aVisited'_cons {s s' : State} {p ps} [hs : AState s]
(h : sys.tr s p = some s') : s.aVisited' (p :: ps) =
(s'.aVisited' ps).insert p := by
  simp [State.aVisited', h]

theorem DState.aVisited'_cons {s s' : State} {p ps} [hs : DState s]
(h : sys.tr s p = some s') : s.aVisited' (p :: ps) = s'.aVisited' ps := by
  simp [State.aVisited', h]

theorem AState.aVisited'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : AState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisited' (ps ++ [p]) = (s.aVisited' ps).insert p := by
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
  · simp_rw [AState.aVisited'_cons h₁, ih, Set'.insert_comm]
  · simp_rw [DState.aVisited'_cons h₁, ih]

theorem DState.aVisited'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : DState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisited' (ps ++ [p]) = s.aVisited' ps := by
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
  · simp_rw [AState.aVisited'_cons h₁, ih]
  · simp_rw [DState.aVisited'_cons h₁, ih]

theorem AState.aVisited_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : AState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisited s₂ = (s.aVisited s₁).insert p := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisited]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [State.diffTrs_eq_of_trs_full h₂, Set'.insert_comm]
  rw [aVisited'_snoc h₁]

theorem DState.aVisited_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : DState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisited s₂ = s.aVisited s₁ := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisited]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [State.diffTrs_eq_of_trs_full h₂]
  rw [aVisited'_snoc h₁]

theorem State.mem_aVisited_iff {s f n s₁ p} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, 0)) : p ∈ s.aVisited s₁ ↔ p = s.aPos ∨
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
  all_goals simp [hs'.aVisited_eq_of_tr h₂ h₃, ih]; clear ih
  · grind
  apply iff_of_eq; congr 1; apply propext
  apply exists_congr; intro k
  rw [Nat.lt_add_one_iff]
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

theorem State.aPtsSim_eq_setOf {s : State} {st} : s.aPtsSim st =
{p | ∃ s₁ s₂, s.aMoveSim st s₁ = some (p, s₂)} := by
  ext; simp [aPtsSim, aPtsSimAt]

theorem State.mem_aPtsSim_iff_aPtsSimAt {s : State} {st p} :
p ∈ s.aPtsSim st ↔ ∃ s₁, (s₁, p) ∈ s.aPtsSimAt st := by
  simp [aPtsSim]

theorem State.mem_aPtsSimAt_iff_simulate_tr {s s₁ p} {st : Strat} [hs : sys.WF s] :
(s₁, p) ∈ s.aPtsSimAt st ↔ AState s₁ ∧ ∃ n, sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp only [aPtsSimAt, aMoveSim, moveSim, Option.pure_def, Option.bind_eq_bind,
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

theorem State.mem_aPtsSim_iff_simulate_tr {s p} {st : Strat} [hs : sys.WF s] :
p ∈ s.aPtsSim st ↔ ∃ n s₁, AState s₁ ∧ sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp_rw [mem_aPtsSim_iff_aPtsSimAt, mem_aPtsSimAt_iff_simulate_tr]; grind

theorem State.mem_aPtsSim_iff_simulate_ge_two {s p} {st : Strat} [hst : st.WF] [hs : sys.WF s] :
p ∈ s.aPtsSim st ↔ ∃ n s₁, 2 ≤ n ∧ sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos = p := by
  rw [mem_aPtsSim_iff_simulate_tr]
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

theorem State.aVisited_subset_of_simulate_le  (st : Strat) k n {s s₁ s₂} [hs : sys.WF s]
(hn : k ≤ n) (h₁ : sys.simulate st.f s k = (s₁, 0)) (h₂ : sys.simulate st.f s n = (s₂, 0)) :
s.aVisited s₁ ⊆ s.aVisited s₂ := by
  intro p; rw [mem_aVisited_iff h₁, mem_aVisited_iff h₂]; grind

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