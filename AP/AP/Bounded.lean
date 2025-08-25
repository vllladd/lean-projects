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

def State.getATrap (s : State) : Set PointZ :=
  {p | ∃ s', sys.Reachable s s' ∧ s'.aPos = p}

def State.aTrapped (s : State) : Prop :=
  s.getATrap.Finite

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
  unfold aTrapped getATrap
  apply Set.finite_of_subset_finset h₂.toFinset
  simpa

theorem State.getATrap_eq_of_not_hasTr {s} (h : ¬sys.hasTr s) : s.getATrap = {s.aPos} := by
  unfold getATrap
  ext p
  simp
  symm; constructor; rintro rfl; use s
  rintro ⟨s', h₁, rfl⟩
  rw [System.eq_of_reachable_and_not_hasTr h₁ h]

theorem State.aTrapped_of_not_hasTr {s} (h : ¬sys.hasTr s) : s.aTrapped := by
  simp [aTrapped, getATrap_eq_of_not_hasTr h]

theorem DState.getATrap_eq_of_tr {s₁ s₂ p} [hd : DState s₁]
(h₁ : s₁.aTrapped) (h₂ : sys.tr s₁ p = some s₂) : s₂.getATrap = s₁.getATrap := by
  rename' h₁ => H₁, h₂ => H₂
  unfold State.getATrap
  ext p₁
  simp
  have h₁ := H₂
  simp at h₁
  rcases h₁ with ⟨⟨h₁, h₂⟩, h₃⟩
  constructor
  · rintro ⟨b, h₄, h₅⟩
    refine' ⟨b, _, h₅⟩
    trans s₂
    · exact System.reachable_of_tr H₂
    · exact h₄
  rintro ⟨b, h₄, h₅⟩
  sorry

-- #check 0 #exit

theorem State.exi_d_wins_of_aTrapped {s} [hs : sys.WF s] {a : AStrat} [Ha : a.WF]
(h : s.aTrapped) : ∃ (d: DStrat), d.WF ∧ s.d_wins ⟨a, d⟩ := by
  classical
  generalize hd : DStrat.mk' (λ s => choose? # λ p => p ∈ s.getATrap ∧ p ≠ s.aPos) = d
  have Hd : d.WF; rw [←hd]; infer_instance
  use d, Hd
  apply d_wins_of_decreasing_dState (f := (·.getATrap.ncard))
  intro sd hsd sa hsa sd' hsd' h₁ h₂
  -- rw [←hsd.getATrap_eq_of_tr h₁]
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