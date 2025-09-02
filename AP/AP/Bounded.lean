import AP.AP.King

namespace AP

theorem State.length_hist_lt_of_tr {s s' p}
(h : sys.tr s p = some s') : s.hist.length < s'.hist.length := by
  simp [hist_eq_of_tr h]

theorem State.forall_d_wins_bounded_of_forall_d_wins {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] (h : ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩) :
∃ (n : ℕ), ∀ (a : AStrat), a.WF → (sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  contrapose! h
  simp
  apply exi_a_wins_of_ind (p := λ s => ∀ (n : ℕ), ∃ (a : AStrat), a.WF ∧
    (sys.simulate (Strat.mk a d).f s n).2 = 0) h <;> clear! s; rotate_left
  · intro sd hd sa ih h₁ n
    specialize ih (n + 1)
    obtain ⟨a, Ha, ih⟩ := ih
    simp [h₁] at ih
    use a
  intro sa ha ih
  have ht : sys.hasTr sa
  · specialize ih 1
    obtain ⟨a, h₁, h₂⟩ := ih
    simp at h₂; split at h₂; simp at h₂; nm x sd h₃; clear x
    exact ⟨_, _, h₃⟩
  rw [skolemize'] at ih
  obtain ⟨f, hf⟩ := ih
  obtain ⟨g, hg⟩ : ∃ (g : ℕ → {pa : PointZ // pa.dist sa.aPos ≤ sa.pw}),
    ∀ n, n ≠ 0 → (g n).1 = (f n).f sa
  · refine' ⟨_, _⟩
    · intro n
      use if n = 0 then sa.aPos else (f n).f sa
      specialize hf n
      rcases hf with ⟨h₁, h₂⟩
      cases n <;> simp; nm n
      simp at h₂; split at h₂; simp at h₂; nm x sd h₃; clear x
      simp at h₃
      exact h₃.1.2.2
    intro n hn
    simp [hn]
  have h₂ := @Point.finite_setOf_dist_le sa.aPos sa.pw
  obtain ⟨⟨pa, h₃⟩, h₄⟩ := Set.exists_infinite_preimage_of (f := g) (hb := h₂)
  simp at h₃
  suffices h₅ : ∀ n, n ≠ 0 → ∃ (a : AStrat), a.WF ∧ a.f sa = pa ∧
    (sys.simulate (Strat.mk a d).f sa n).2 = 0
  · obtain ⟨a, h₆, h₇, h₈⟩ := h₅ 1 (by simp)
    clear h₈
    obtain ⟨sd, h₈⟩ := a.validTr ht
    rw [h₇] at h₈; clear h₇
    use pa, sd, h₈
    clear! a
    intro n
    specialize h₅ (n + 1) (by simp)
    obtain ⟨a, Ha, h₅, h₆⟩ := h₅
    simp [h₅, h₈] at h₆
    use a
  suffices h₅ : ∀ (k : ℕ), ∃ (n : ℕ), k ≤ n ∧ g n = ⟨pa, h₃⟩
  · intro k hk
    specialize h₅ k
    obtain ⟨n, hn, h₅⟩ := h₅
    specialize hg n _
    · rintro rfl; simp [hk] at hn
    rw [Subtype.ext_iff, hg] at h₅
    specialize hf n
    rcases hf with ⟨hf, h₆⟩
    use f n, hf, h₅
    exact System.simulate_snd_eq_zero_of_le_and_eq_zero h₆ hn
  contrapose! h₄
  simp [Set.preimage]
  obtain ⟨k, hk⟩ := h₄
  apply Set.finite_of_subset_finset # Finset.Ico 0 k
  simp
  intro n h₄
  specialize hk n
  simp [h₄] at hk
  exact hk

theorem State.forall_d_wins_iff_forall_d_wins_bounded {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] : (∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩) ↔
∃ (n : ℕ), ∀ (a : AStrat), a.WF → (sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  use forall_d_wins_bounded_of_forall_d_wins
  rintro ⟨n, h₁⟩
  intro a Ha
  specialize h₁ a Ha
  use n

theorem State.d_hws_bounded_of_d_hws {s} [hs : sys.WF s]
(h : s.d_hws) : ∃ (n : ℕ) (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
(sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  obtain ⟨d, Hd, h⟩ := h
  rw [forall_d_wins_iff_forall_d_wins_bounded] at h
  obtain ⟨n, h₁⟩ := h
  use n, d

theorem State.d_hws_iff_d_hws_bounded {s} [hs : sys.WF s] :
s.d_hws ↔ ∃ (n : ℕ) (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
(sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  use d_hws_bounded_of_d_hws
  rintro ⟨n, d, Hd, h⟩
  use d, Hd
  intro a Ha
  specialize h a Ha
  use n

def State.aTrap (s : State) : Set PointZ :=
  {p | ∃ s', sys.Reachable s s' ∧ s'.aPos = p}

def State.aTrapped (s : State) : Prop :=
  s.aTrap.Finite

def State.aTrappedIn (s : State) (ps : Set PointZ) : Prop :=
  ∀ s', sys.Reachable s s' → s'.aPos ∈ ps

def State.dEntrapsAIn (s : State) (st : Strat) (ps : Set PointZ) : Prop :=
  ∃ n, (sys.simulate st.f s n).1.aTrappedIn ps

theorem State.aTrappedIn_iff_of_not_hasTr {sa ps}
(h : ¬sys.hasTr sa) : sa.aTrappedIn ps ↔ sa.aPos ∈ ps := by
  constructor
  · intro h₁; exact h₁ sa # by rfl
  intro h₁ s' h₂
  have h₃ := System.eq_of_reachable_and_not_hasTr h₂ h
  subst h₃
  exact h₁

theorem aPos_dist_le_of_simulate {s r f n} [hs : sys.WF s]
(h : sys.simulate f s n = r) : s.aPos.dist r.1.aPos ≤ n * s.pw := by
  induction n generalizing s r
  · simp at h; simp [←h]
  nm n ih
  simp at h; split at h
  · nm x h₁; clear x
    subst h
    simp
  nm x s' h₁; clear x
  have h₂ := System.wf_of_tr h₁
  specialize ih h
  simp [Int.add_mul]
  replace hs := s.aState_or_dState
  rcases hs with ha | hd
  rotate_left
  · simp at h₁
    rcases h₁ with ⟨h₁, rfl⟩
    simp at ih
    linarith
  simp at h₁
  rcases h₁ with ⟨⟨h₁, h₃, h₄⟩, rfl⟩
  clear h h₁ h₂ h₃
  simp at ih
  have h₁ : s.aPos.dist r.1.aPos ≤ s.aPos.dist (f s) + (f s).dist r.1.aPos
  · exact Point.triangle
  apply h₁.trans; clear h₁
  rw [Point.dist_comm]
  linarith

theorem State.dEntrapsAIn_of_forall_d_wins {s} [hs : sys.WF s] {d : DStrat} [Hd : d.WF]
(h : ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩) :
∃ (N : ℕ), ∀ (a : AStrat), a.WF → s.dEntrapsAIn ⟨a, d⟩ {p | p ∈ (0 : PointZ).nbhd N} := by
  rw [forall_d_wins_iff_forall_d_wins_bounded] at h
  obtain ⟨n, h⟩ := h
  use (Point.dist 0 s.aPos).toNat + n * s.pw
  intro a Ha
  specialize h a Ha
  use n
  generalize hr : sys.simulate (Strat.mk a d).f s n = r at h ⊢
  rcases r with ⟨s₁, r⟩
  simp at h ⊢
  rw [aTrappedIn_iff_of_not_hasTr]
  rotate_left; exact System.not_hasTr_of_snd_simulate_ne_zero hr h
  simp
  trans Point.dist 0 s.aPos + s.aPos.dist s₁.aPos
  · exact Point.triangle
  simp; apply aPos_dist_le_of_simulate hr

theorem State.aTrapped_of_aTrappedIn_and_finite {s : State} {ps}
(h₁ : s.aTrappedIn ps) (h₂ : ps.Finite) : s.aTrapped := by
  unfold aTrappedIn at h₁
  unfold aTrapped aTrap
  apply Set.finite_of_subset_finset h₂.toFinset
  simpa

theorem State.aTrap_eq_of_not_hasTr {s} (h : ¬sys.hasTr s) : s.aTrap = {s.aPos} := by
  unfold aTrap
  ext p
  simp
  symm; constructor; rintro rfl; use s
  rintro ⟨s', h₁, rfl⟩
  rw [System.eq_of_reachable_and_not_hasTr h₁ h]

theorem State.aTrapped_of_not_hasTr {s} (h : ¬sys.hasTr s) : s.aTrapped := by
  simp [aTrapped, aTrap_eq_of_not_hasTr h]

@[simp]
theorem State.mem_aTrap_iff {s p} : p ∈ s.aTrap ↔ ∃ s', sys.Reachable s s' ∧ s'.aPos = p := by
  simp [aTrap]

inductive State.AReachable (s : State) : PointZ → Prop where
| mk₁ : s.AReachable s.aPos
| mk₂ : ∀ {p p' : PointZ}, s.AReachable p → p.dist p' ≤ s.pw → p' ∉ s.taken → s.AReachable p'

theorem State.taken_subset_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : s.taken ⊆ s'.taken := by
  intro p' hp'
  replace hs := s.aState_or_dState
  rcases hs with hs | hs <;> simp at h
  · rcases h with ⟨⟨h₁, h₂, h₃⟩, rfl⟩; simpa
  · rcases h with ⟨⟨h₁, h₂⟩, rfl⟩; simp [hp']

theorem State.taken_subset_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : s.taken ⊆ s'.taken := by
  revert hs
  induction h; simp
  clear! s s'
  nm a b c p h₁ h₂ ih
  intro ha
  have hb := sys.wf_of_tr h₁
  have hc := sys.wf_of_reachable h₂
  specialize @ih hb
  apply Set'.subset_trans (taken_subset_of_tr h₁) ih

theorem State.mem_taken_of_tr {s s' p p'} [hs : sys.WF s]
(h₁ : sys.tr s p = some s') (h₂ : p' ∈ s.taken) : p' ∈ s'.taken :=
  taken_subset_of_tr h₁ _ h₂

theorem State.mem_taken_of_reachable {s s' p} [hs : sys.WF s]
(h₁ : sys.Reachable s s') (h₂ : p ∈ s.taken) : p ∈ s'.taken :=
  taken_subset_of_reachable h₁ _ h₂

@[simp]
theorem initState_aPos {pw} : (initState pw).aPos = 0 := rfl

@[simp]
theorem initState_taken {pw} : (initState pw).taken = ∅ := rfl

@[simp]
theorem State.not_aPos_mem_taken {s} [hs : sys.WF s] : s.aPos ∉ s.taken := by
  apply sys.invariant_wf (p := λ s => s.aPos ∉ s.taken) hs <;> clear! s
  · intro s hs
    simp at hs
    rw [←hs]
    simp
  intro s s' p hs hs' h₁ h₂
  replace hs := s.aState_or_dState
  rcases hs with hs | hs <;> simp at h₂
  · rcases h₂ with ⟨⟨h₃, h₄, h₅⟩, rfl⟩; simpa
  · rcases h₂ with ⟨⟨h₃, h₄⟩, rfl⟩; simp [h₁, h₃]

theorem State.aReachable_of_mem_aTrap {s p} [hs : sys.WF s]
(h : p ∈ s.aTrap) : s.AReachable p := by
  obtain ⟨s', h, rfl⟩ := h
  revert hs
  induction h using sys.reachable_ind_right <;> clear! s s'
  · intros; constructor
  nm s₀ s s' p h₁ h₂ ih
  intro hs₀
  have hs' := sys.wf_of_reachable h₁
  have hs₁ := sys.wf_of_tr h₂
  specialize ih
  replace hs := s.aState_or_dState
  rcases hs with hs | hs <;> simp at h₂
  · rcases h₂ with ⟨⟨h₃, h₄, h₅⟩, h₆⟩
    apply AReachable.mk₂ ih
    · rw [←pw_eq_of_reachable h₁]
      rw [Point.dist_comm, ←h₆]
      simpa
    · rw [←h₆]; simp
      contrapose! h₄
      exact mem_taken_of_reachable h₁ h₄
  · rcases h₂ with ⟨⟨h₃, h₄⟩, h₅⟩
    apply AReachable.mk₂ ih
    · rw [←pw_eq_of_reachable h₁]
      rw [Point.dist_comm, ←h₅]
      simp
    · rw [←h₅]; simp
      have h₆ := s.not_aPos_mem_taken
      contrapose! h₆
      exact mem_taken_of_reachable h₁ h₆

@[simp]
theorem ASTate.tr_eq_none_iff {s p} [hs : AState s] :
sys.tr s p = none ↔ s.aPos = p ∨ p ∈ s.taken ∨ s.pw < p.dist s.aPos := by
  simp [sys, State.move, State.aMove]
  constructor
  · intro h
    by_contra! h₁
    simp [h₁] at h
  rintro h s' h₁ h₂ h₃ rfl
  simp [h₁, h₂] at h
  linarith

@[simp]
theorem DSTate.tr_eq_none_iff {s p} [hs : DState s] :
sys.tr s p = none ↔ s.aPos = p ∨ p ∈ s.taken := by
  simp [sys, State.move, State.dMove]; tauto

instance {f} [hf : sys.SimFn f] : AStrat.WF ⟨f⟩ := by
  rw [AStrat.wf_iff]; intro s hs h₁; exact hf.1 h₁

instance {f} [hf : sys.SimFn f] : DStrat.WF ⟨f⟩ := by
  rw [DStrat.wf_iff]; intro s hs h₁; exact hf.1 h₁

theorem exi_strat_of_simFn f [hf : sys.SimFn f] :
∃ (a : AStrat) (d : DStrat), a.WF ∧ d.WF ∧ f = Strat.f ⟨a, d⟩ := by
  use ⟨f⟩, ⟨f⟩, inferInstance, inferInstance
  ext:1; nm s; unfold Strat.f; split_ifs <;> rfl

theorem exi_strat_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : ∃ (a : AStrat) (d : DStrat) (n : ℕ),
a.WF ∧ d.WF ∧ sys.simulate (Strat.f ⟨a, d⟩) s n = (s', 0) := by
  rw [System.reachable_iff_exi_simulate] at h
  obtain ⟨f, hf, n, h⟩ := h
  obtain ⟨a, d, ha, hd, rfl⟩ := exi_strat_of_simFn f
  use a, d, n

def aMimic (st : Strat) (s₀ : State) : AStrat := .mk' # λ s => some #
  let n := s.hist.length - s₀.hist.length
  let r := sys.simulate st.f s₀ n
  st.a.f r.1

instance {st s₀} : (aMimic st s₀).WF := by unfold aMimic; infer_instance

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

theorem aMimic_apply_eq_of {st st' : Strat} {s₀ s₁ s₂ n} [hs₀ : sys.WF s₀]
(h₁ : sys.simulate st.f s₀ n = (s₁, 0)) (h₂ : sys.simulate st'.f s₀ n = (s₂, 0))
(h₃ : sys.validTr s₂ (st.a.f s₁)) : (aMimic st s₀).f s₂ = st.a.f s₁ := by
  simp [aMimic, mk_strat_fn, guard, h₁, h₃, length_hist_sub_eq_of_simulate h₂]

-- #check 0 #exit

theorem State.exi_taken_disjoint_of_reachable
{s₀ s} [hs₀ : sys.WF s₀] {ps : Set PointZ}
(h₁ : ps.Finite) (h₂ : ∀ p ∈ ps, p ∉ s₀.taken) (h₃ : sys.Reachable s₀ s) :
∃ s₁, sys.Reachable s₀ s₁ ∧ s₁.aTurn = s.aTurn ∧
s₁.aPos = s.aPos ∧ ∀ p ∈ ps, p ∉ s₁.taken := by
  obtain ⟨a, d, n, ha, hd, h₄⟩ := exi_strat_of_reachable h₃
  generalize hS : (Finset.Icc 0 n).map' (λ k =>
    sys.simulate (Strat.f ⟨a, d⟩) s₀ k |>.1.aPos) = S
  generalize hp' : (ps ∪ s.taken ∪ S : Set' _) = ps'
  generalize ha' : aMimic ⟨a, d⟩ s₀ = a'
  generalize hd' : DStrat.mk' (λ sd => some # (sd.taken ∪ ps').max! + ⟨1, 0⟩) = d'
  have Ha : a'.WF; subst ha'; infer_instance
  have Hd : d'.WF; subst hd'; infer_instance
  generalize hr : sys.simulate (Strat.f ⟨a', d'⟩) s₀ n = r
  have hc := System.simulate_congr_rel_full (g := Strat.f ⟨a', d'⟩) (a₂ := s₀)
    (r := λ s₁ s₂ => s₁.aTurn = s₂.aTurn ∧ s₁.aPos = s₂.aPos ∧ s₂.taken ∩ ps' ⊆ s₀.taken) h₄
  specialize hc (by simp) _
  · clear hc
    dsimp
    rintro k hk s₁ s₂ s₁' hs₁ hs₂ ⟨ih₁, ih₂, ih₃⟩ H₁
    have Hs₁ := sys.wf_of_simulate_eq hs₁
    have Hs₂ := sys.wf_of_simulate_eq hs₂
    dsimp at Hs₁ Hs₂
    replace Hs₁ := s₁.aState_or_dState
    have hr₁ := System.reachable_of_simulate_full hs₁
    have hr₂ := System.reachable_of_simulate_full hs₂
    rcases Hs₁ with Hs₁ | Hs₁ <;> simp only [Hs₁.start_f_eq] at H₁
    · generalize hp : a.f s₁ = p at H₁
      replace Hs₂ : AState s₂; use Hs₂; simp [←ih₁]
      have H₁' := H₁
      simp at H₁
      rcases H₁ with ⟨⟨H₁, H₃, H₄⟩, rfl⟩
      rw [pw_eq_of_reachable hr₁] at H₄
      have H : ¬s₂.aPos = p ∧ p ∉ s₂.taken ∧ Point.dist p s₂.aPos ≤ ↑s₂.pw
      · simp [←ih₂, H₁, pw_eq_of_reachable hr₂, H₄]
        contrapose! H₃
        specialize ih₃ p
        simp [H₃] at ih₃; clear H₃
        apply mem_taken_of_reachable hr₁
        apply ih₃; clear ih₃
        subst hp' hS
        clear hd'
        simp [Set'.mem_ofSet h₁]
        right
        use k + 1, by linarith
        rw [System.simulate_add]
        simp [hs₁, hp, H₁']
      have H₂ : a'.f s₂ = p
      · rw [←ha', ←hp]; apply aMimic_apply_eq_of hs₁ hs₂
        simpa [hp, AState.validTr_iff]
      simp [H₂]; use H
    · generalize hp : d.f s₁ = p at H₁
      replace Hs₂ : DState s₂; use Hs₂; simp [←ih₁]
      sorry
  obtain ⟨s₁, H₁, H₂, H₃, H₄⟩ := hc
  use s₁
  simp [H₂, H₃]
  use System.reachable_of_simulate_full H₁
  intro p hp H₅
  specialize H₄ p
  simp [H₅, ←hp', Set'.mem_ofSet h₁, hp] at H₄
  sorry

-- #check 0 #exit

theorem State.exi_taken_disjoint_of_reachable_with_turn
{s₀ s} [hs₀ : sys.WF s₀] {ps : Set PointZ} {t : Bool}
(h₁ : ps.Finite) (h₂ : ∀ p ∈ ps, p ∉ s₀.taken) (h₃ : sys.Reachable s₀ s) (h₄ : s.aTurn → t) :
∃ s₁, sys.Reachable s₀ s₁ ∧ s₁.aTurn = t ∧ s₁.aPos = s.aPos ∧ ∀ p ∈ ps, p ∉ s₁.taken := by
  obtain ⟨s', h₅, h₆, h₇, h₈⟩ := exi_taken_disjoint_of_reachable h₁ h₂ h₃
  by_cases ht : s.aTurn = t; subst ht; use s'
  replace ht : s.aTurn = false
  · contrapose! ht; simp at ht; rwa [h₄ ht]
  have hs : DState s
  · use System.wf_of_reachable h₃
  clear ht
  have hs' : DState s'
  · use System.wf_of_reachable h₅
    simp [h₆]
  clear h₄ h₆
  cases t; use s', h₅, by simp
  generalize hm : (ps ∪ insert s'.aPos s'.taken : Set' _).max! = m
  generalize hp : m + ⟨1, 0⟩ = p
  have hm₁ : m < p
  · subst hp
    rw [lt_add_iff_pos_right]
    simp [Point.zero_def]
  generalize H₂ : sys.tr s' p = s₁
  have H₂' := H₂
  rcases s₁ with _ | s₁ <;> simp at H₂
  · contrapose H₂; clear H₂
    simp
    constructor
    · intro H₂
      contrapose! hm₁
      subst hm
      apply Set'.le_max!_of_mem
      simp [H₂]
    contrapose! hm₁
    subst hm
    apply Set'.le_max!_of_mem
    simp [hm₁]
  rcases H₂ with ⟨⟨H₂, H₃⟩, H₄⟩
  have hs₁ := sys.wf_of_tr H₂'
  use s₁
  refine' ⟨_, _, _, _⟩
  · apply h₅.trans
    exact System.reachable_of_tr H₂'
  · simp [←H₄]
  · simpa [←H₄]
  · simp [←H₄]
    intro p' hp'
    simp [h₈ _ hp']
    rintro rfl
    contrapose! hm₁
    subst hm
    apply Set'.le_max!_of_mem
    simp [Set'.mem_ofSet h₁, hp']

theorem State.mem_aTrap_of_aReachable {s p} [hs : sys.WF s]
(h : s.AReachable p) : p ∈ s.aTrap := by
  induction h; use s
  clear p
  rename' s => s₀, hs => hs₀
  nm p p' h₁ h₂ h₃ ih
  simp at ih ⊢
  rcases ih with ⟨s, h₄, rfl⟩
  have h₆ := @exi_taken_disjoint_of_reachable_with_turn s₀ s _ {p'} true
  simp [h₃, h₄] at h₆
  obtain ⟨s₁, h₆, h₇, h₈, h₉⟩ := h₆
  have hs₁ : AState s₁; use sys.wf_of_reachable h₆
  generalize H₁ : sys.tr s₁ p' = s'
  have H₂ := H₁
  rcases s' with _ | s' <;> simp at H₁
  · simp [h₈, h₉] at H₁
    rcases H₁ with rfl | H₁; use s
    rw [Point.dist_comm, pw_eq_of_reachable h₆] at H₁
    linarith
  use s', System.reachable_right h₆ H₂
  rcases H₁ with ⟨⟨H₁, H₂, H₃⟩, rfl⟩
  simp

theorem State.mem_aTrap_iff_aReachable {s p} [hs : sys.WF s] :
p ∈ s.aTrap ↔ s.AReachable p := ⟨aReachable_of_mem_aTrap, mem_aTrap_of_aReachable⟩

@[simp]
theorem State.aReachable_aPos {s : State} : s.AReachable s.aPos :=
  AReachable.mk₁

theorem State.not_mem_taken_of_tr {s s' p p'} [hs : sys.WF s]
(h₁ : sys.tr s p = some s') (h₂ : p' ∉ s'.taken) : p' ∉ s.taken := by
  contrapose! h₂; exact mem_taken_of_tr h₁ h₂

theorem AState.aTrap_eq_of_tr {s s' p} [hs : AState s]
(h₂ : sys.tr s p = some s') : s'.aTrap = s.aTrap := by
  rename' p => p₀
  have hs' := sys.wf_of_tr h₂
  ext p₁
  simp_rw [State.mem_aTrap_iff_aReachable]
  have h₃ := h₂
  simp at h₃
  rcases h₃ with ⟨⟨h₃, h₄, h₅⟩, h₆⟩
  constructor <;> intro h
  · induction h
    · subst h₆
      apply State.AReachable.mk₂ (p := s.aPos)
      · simp
      · rwa [Point.dist_comm]
      · simpa
    nm p p' h₇ h₈ h₉ ih
    rw [pw_eq_of_tr h₂] at h₈
    apply State.AReachable.mk₂ (p := p) ih h₈
    exact State.not_mem_taken_of_tr h₂ h₉
  · induction h
    · apply State.AReachable.mk₂ (p := s'.aPos)
      · simp
      · rwa [←h₆]
      · simp [←h₆]
    nm p p' h₇ h₈ h₉ ih
    apply State.AReachable.mk₂ (p := p) ih
    · rwa [pw_eq_of_tr h₂]
    · rwa [←h₆]

-- #check 0 #exit

theorem State.exi_d_wins_of_aTrapped {s} [hs : sys.WF s] {a : AStrat} [Ha : a.WF]
(h : s.aTrapped) : ∃ (d: DStrat), d.WF ∧ s.d_wins ⟨a, d⟩ := by
  classical
  generalize hd : DStrat.mk' (λ s => choose? # λ p => p ∈ s.aTrap ∧ p ≠ s.aPos) = d
  have Hd : d.WF; rw [←hd]; infer_instance
  use d, Hd
  apply d_wins_of_decreasing_dState (f := (·.aTrap.ncard))
  intro sd hsd sa hsa sd' hsd' h₁ h₂
  -- rw [←hsd.aTrap_eq_of_tr h₁]
  sorry

-- #check 0 #exit

theorem State.exi_d_wins_of_simulate_aTrapped {s} [hs : sys.WF s] {n}
{a : AStrat} [Ha : a.WF] {d : DStrat} [Hd : d.WF]
(h : (sys.simulate (Strat.mk a d).f s n).1.aTrapped) :
∃ (d : DStrat), d.WF ∧ s.d_wins ⟨a, d⟩ := by
  classical
  generalize hr : sys.simulate (Strat.mk a d).f s n = r at h
  rcases r with ⟨s₁, r⟩
  dsimp at h
  by_cases hr' : r = 0; rotate_left
  · use d, Hd, n; simpa [hr]
  subst hr'
  have hs₁ : sys.WF s₁ := System.wf_of_simulate_eq hr
  obtain ⟨d₁, Hd₁, h₁⟩ : ∃ d, d.WF ∧ s₁.d_wins ⟨a, d⟩
  · exact exi_d_wins_of_aTrapped h
  generalize hD : DStrat.mk'
    (λ sd => if sys.Reachable s₁ sd then d₁.f sd else d.f sd) = D
  have HD : D.WF; subst hD; infer_instance
  use D, HD
  rw [d_wins_iff_add n]
  have h₂ : sys.simulate (Strat.mk a D).f s n = (s₁, 0)
  · rw [←hr]
    apply simulate_congr # by simp
    intro k hk sd hd h₂ h₃ h₄
    rw [←hD]
    have h₅ := System.not_reachable_of_acyclic_and_simulate_and_lt hr hk
    simp [h₃] at h₅
    simp [mk_strat_fn, h₅]
  simp [System.simulate_add, h₂]
  rcases h₁ with ⟨n', h₁⟩
  use n'
  convert h₁ using 3
  clear h₁ h₂
  have H : (Strat.mk a d₁).WF
  · rw [Strat.wf_iff]; use Ha
  apply simulate_congr # by simp
  intro k hk sd hd h₁ h₂ h₃
  simp
  have h₄ : sys.Reachable s₁ sd
  · exact System.reachable_of_simulate_full h₁
  rw [←hD]
  simp [mk_strat_fn, h₄, Hd₁.1 h₃]

theorem State.exi_d_wins_iff_exi_aTrapped {s} [hs : sys.WF s] {a : AStrat} [Ha : a.WF] :
(∃ (d : DStrat), d.WF ∧ s.d_wins ⟨a, d⟩) ↔
∃ (n : ℕ) (d : DStrat), d.WF ∧ (sys.simulate (Strat.mk a d).f s n).1.aTrapped := by
  symm; constructor
  · rintro ⟨n, d, Hd, h⟩
    exact exi_d_wins_of_simulate_aTrapped h
  rintro ⟨d, Hd, n, h⟩
  use n, d, Hd
  generalize hr : sys.simulate (Strat.mk a d).f s n = r at h ⊢
  rcases r with ⟨s₁, r⟩
  dsimp at h ⊢
  have h₁ : ¬sys.hasTr s₁
  · exact System.not_hasTr_of_snd_simulate_ne_zero hr h
  exact aTrapped_of_not_hasTr h₁

theorem State.d_hws_iff_exi_dEntrapsAIn {s} [hs : sys.WF s] :
s.d_hws ↔ ∃ (N : ℕ) (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
s.dEntrapsAIn ⟨a, d⟩ {p | p ∈ (0 : PointZ).nbhd N} := by
  symm; constructor
  · rintro ⟨N, d, Hd, h⟩
    rw [←not_a_hws_iff, a_hws]
    push_neg; simp
    intro a Ha
    specialize h a Ha
    rcases h with ⟨n, h⟩
    replace h := aTrapped_of_aTrappedIn_and_finite h
    specialize h _
    · apply Set.finite_of_subset_finset # (0 : PointZ).nbhd N |>.toFinset; simp
    exact exi_d_wins_of_simulate_aTrapped h
  rw [d_hws_iff_d_hws_bounded]
  rintro ⟨n, d, Hd, h⟩
  have h₁ := @dEntrapsAIn_of_forall_d_wins s hs d Hd
  specialize h₁ _
  · clear h₁
    intro a Ha
    specialize h a Ha
    use n
  obtain ⟨N, h₁⟩ := h₁
  use N, d

theorem State.d_hws_of_exi_aTrapped {s} [hs : sys.WF s]
(h : ∃ (d : DStrat), d.WF ∧ ∀ (a: AStrat), a.WF → ∃ n,
(sys.simulate (Strat.mk a d).f s n).1.aTrapped) : s.d_hws := by
  rcases h with ⟨d, Hd, h⟩
  rw [←not_a_hws_iff, a_hws]; push_neg; simp
  intro a Ha
  specialize h a Ha
  rcases h with ⟨n, h⟩
  exact exi_d_wins_of_simulate_aTrapped h