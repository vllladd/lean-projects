import AP.AP.Moves
import AP.AP.FreshA.Tile

namespace AP

def AhwsFspCnd (f : State → State → FSP → FSP) (s s₂ : State) (fsp : FSP) : Prop :=
  s₂.aHwsDisj # f s s₂ # fsp.offset # s₂.diff s

def AStrat.RespectsFSP (f : State → State → FSP → FSP)
(a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aPos ∉ fsp.get 0 ∧ ∀ (d : DStrat), d.WF →
  ∀ n, ∃ s₁ s₂, sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧
  sys.tr s₁ (a.f s₁) = some s₂ ∧ AhwsFspCnd f s s₂ fsp

def AStrat.Fresh1 (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aSimPairs ⟨a, d⟩ → p ∉ s.aVisitedIcc s₁

def aFresh1FSP (s s₂ : State) (fsp : FSP) : FSP :=
  fsp.insertSet 0 (s.aVisitedIcc s₂.prev).toSet

def AStrat.Fresh1Aux (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.RespectsFSP aFresh1FSP s fsp

noncomputable
def aFresh1 (s : State) (fsp : FSP) : AStrat :=
  aSeek (AhwsFspCnd aFresh1FSP s · fsp)

-- #check 0 #exit

-----

theorem AStrat.Fresh1.wf {a : AStrat} {s fsp} (h : a.Fresh1 s fsp) : a.WF := h.1

theorem State.aPos_notMem_of_aWinsDisj {s : State} {fsp a d}
(h : s.aWinsDisj fsp ⟨a, d⟩) : s.aPos ∉ fsp.get 0 := by
  specialize h 0; simp at h; exact h

theorem State.aPos_notMem_of_aForallWinsDisj {s : State} {fsp a}
(h : s.aForallWinsDisj fsp a) : s.aPos ∉ fsp.get 0 :=
  aPos_notMem_of_aWinsDisj # h default inferInstance

theorem State.aPos_notMem_of_aHwsDisj {s : State} {fsp}
(h : s.aHwsDisj fsp) : s.aPos ∉ fsp.get 0 := by
  choose a ha h using h; exact aPos_notMem_of_aForallWinsDisj h

theorem State.hasTr_of_aWinsDisj {s fsp a d} [hs : sys.WF s]
(h : s.aWinsDisj fsp ⟨a, d⟩) : sys.hasTr s := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  rotate_left; simp
  specialize h 1
  choose s₁ h₁ h₂ using h
  simp at h₁
  use a.f s, s₁

theorem State.hasTr_of_aForallWinsDisj {s fsp a} [hs : sys.WF s]
(h : s.aForallWinsDisj fsp a) : sys.hasTr s :=
  hasTr_of_aWinsDisj # h default inferInstance

theorem State.hasTr_of_aHwsDisj {s fsp} [hs : sys.WF s]
(h : s.aHwsDisj fsp) : sys.hasTr s := by
  choose a ha h using h; exact hasTr_of_aForallWinsDisj h

@[simp]
instance {s fsp} : aFresh1 s fsp |>.WF := by
  unfold aFresh1; infer_instance

theorem AState.aForallWinsDisj_of_fresh1Aux {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Aux s fsp) : s.aForallWinsDisj fsp a := by
  choose ha h₀ h using h
  intro d hd n
  specialize h d hd
  induction n using Nat.mod_2_ind <;> nm n
  · cases n; simpa; nm n
    specialize h n
    simp at h
    choose s₁ h₁ s₂ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    have hs₂ := DState.of_tr h₂
    simp [Nat.add_mul, h₁, h₂]
    choose a₁ ha₁ h₃ using h₃
    specialize h₃ d hd 1
    simp at h₃
    choose s₃ h₃ h₄ using h₃
    use s₃, h₃
    simp [aFresh1FSP] at h₄
    simp [FSP.hasLe, FSP.insertSet] at h₄ ⊢
    intro k hk
    have h₅ := h₄ 0
    specialize h₄ 1
    simp at h₄ h₅
    choose h₅ h₆ using h₅
    rw [Nat.le_add_one_iff] at hk
    have H₁ : sys.simulate (Strat.f ⟨a, d⟩) s (n * 2 + 1) = (s₂, 0); simp_all
    rw [State.diff_eq_of_simulate H₁] at *
    rcases hk with hk | rfl
    · exact h₆ k hk
    · exact h₄
  · specialize h n
    choose s₁ s₂ h₁ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    simp [h₁, h₂]
    replace h₃ := State.aPos_notMem_of_aHwsDisj h₃
    simp at h₃
    simp [FSP.hasLe]
    have H₁ : sys.simulate (Strat.f ⟨a, d⟩) s (n * 2 + 1) = (s₂, 0); simp_all
    rw [State.diff_eq_of_simulate H₁] at *
    simp [aFresh1FSP] at h₃
    exact h₃.2

theorem AState.fresh1_of_fresh1Aux {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Aux s fsp) : a.Fresh1 s fsp := by
  have H₀ := h
  choose ha h₀ h using h
  use ha, aForallWinsDisj_of_fresh1Aux H₀
  intro d hd s₁ p h₁
  rw [State.mem_aSimPairs_iff_simulate_tr] at h₁
  choose hs₁ n h₁ s₂ h₂ h₃ using h₁
  simp at h₂ h₃; subst h₃
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
  specialize h d hd n
  simp [h₁, h₂] at h
  rw [←AState.aPos_eq_of_tr h₂]
  choose a₁ ha₁ h using h
  specialize h d hd 0
  simp at h
  have H₁ : sys.simulate (Strat.f ⟨a, d⟩) s (n * 2 + 1) = (s₂, 0); simp_all
  simp [aFresh1FSP] at h
  rw [State.diff_eq_of_simulate H₁, State.prev_eq_of_tr h₂] at h
  exact h.1

theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
(h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
  use aFresh1 s fsp
  apply hs.fresh1_of_fresh1Aux
  use inferInstance
  use State.aPos_notMem_of_aHwsDisj h
  intro d hd n
  induction n
  · simp
    simp [aFresh1FSP, AhwsFspCnd]
    have h₁ := @hs.aSeek_exi_tr_of (P := (AhwsFspCnd aFresh1FSP s · fsp))
    specialize h₁ _
    · clear h₁
      simp [AhwsFspCnd, aFresh1FSP]
      replace h := aHwsDisj_insert_one_aPos h
      choose a₁ ha₁ h using h
      have h₁ := h d hd 1
      simp at h₁
      choose s₁ h₁ h₂ using h₁
      use a₁.f s, s₁, h₁, a₁, ha₁
      simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁]
      intro d₁ hd₁ n
      specialize h d₁ hd₁ (n + 1)
      simp_rw [sys.simulate_succ_full'] at h
      simp [h₁] at h
      choose s₂ h h₃ using h
      use s₂, h
      simp [FSP.hasLe, FSP.insert, FSP.insertSet, FSP.next] at h₃ ⊢
      grind
    unfold aFresh1
    choose s₂ h₁ h₂ using h₁
    simp [AhwsFspCnd, aFresh1FSP] at h₁ h₂ ⊢
    use s₂, h₁
  nm n ih
  choose s₁ s₂ h₁ h₂ h₃ using ih
  have hs₁ := AState.of_simulate_mul_two_eq' h₁
  have hs₂ := DState.of_tr h₂
  choose s₃ h₄ using hd.validTr s₂
  have hs₃ := AState.of_tr h₄
  simp [Nat.add_mul, h₁, h₂, h₄]
  have G₁ := sys.reachable_of_simulate h₁
  have G₂ := sys.reachable_right G₁ h₂
  have G₃ := sys.reachable_right G₂ h₄
  have h₅ := @hs₃.aSeek_exi_tr_of (P := (AhwsFspCnd aFresh1FSP s · fsp))
  specialize h₅ _
  · clear h₅
    simp [AhwsFspCnd, aFresh1FSP] at h₃ ⊢
    replace h₃ := DState.aHwsDisj_insert_two_aPos h₃
    choose a₁ ha₁ h₃ using h₃
    have H₁ := h₃ d hd 2
    simp [h₄] at H₁
    choose s₄ H₁ H₂ using H₁
    use a₁.f s₃, s₄, H₁, a₁, ha₁
    rw [State.diff_eq_of_tr H₁ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁,
      State.diff_eq_of_simulate_full h₁, State.prev_eq_of_tr H₁,
      DState.aVisitedIcc_eq_of_tr h₄ G₂, AState.aVisitedIcc_eq_of_tr h₂ G₁]
    intro d₁ hd₁ n₁
    specialize h₃ (d₁.set s₂ # d.f s₂) (DStrat.wf_set_of_tr h₄) (n₁ + 2)
    simp_rw [sys.simulate_succ_full'] at h₃
    simp [h₄, H₁] at h₃
    choose s₅ H₃ H₄ using h₃
    use s₅
    have hs₄ := sys.wf_of_tr H₁
    split_ands
    · convert H₃ using 1
      symm
      apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, h₄⟩
      rw [length_hist_eq_of_tr H₁, length_hist_eq_of_tr h₄]
      omega
    simp
    rw [←AState.aPos_eq_of_tr h₂]
    simp [FSP.hasLe] at H₄ ⊢
    simp [Nat.add_assoc]
    intro k hk
    rw [State.diff_eq_of_tr h₂ # sys.reachable_of_simulate h₁] at H₄
    rw [State.diff_eq_of_simulate_full h₁] at H₄
    rw [State.prev_eq_of_tr h₂] at *
    cases k
    rotate_left
    · nm k
      specialize H₄ (k + 3) (by omega)
      simp at H₄ ⊢
      ring_nf at H₄ ⊢
      exact H₄
    simp
    split_ands
    · specialize H₄ 2 (by omega)
      simp at H₄
      exact H₄.1
    · specialize H₄ 0 (by omega)
      simp at H₄
      exact H₄.1
    · intro k hk
      iterate 2 rw [Nat.le_add_one_iff] at hk
      rcases hk with ((hr | rfl) | rfl)
      · specialize H₄ 0 (by omega)
        simp at H₄
        exact H₄.2 k hr
      · specialize H₄ 1 (by omega)
        simp at H₄
        exact H₄
      · specialize H₄ 2 (by omega)
        simp at H₄
        exact H₄.2
  choose s₄ h₅ h₆ using h₅
  use s₄, h₅

theorem State.aSimPairs_state_eq_of_point_eq_of_fresh1 {s : State} {a : AStrat} {d : DStrat}
{s₁ s₂ p fsp} [hs : sys.WF s] [hd : d.WF] (h : a.Fresh1 s fsp)
(h₁ : (s₁, p) ∈ s.aSimPairs ⟨a, d⟩) (h₂ : (s₂, p) ∈ s.aSimPairs ⟨a, d⟩) : s₁ = s₂ := by
  choose ha h₃ h₄ using h
  specialize h₄ d hd
  have H₁ := h₄ _ _ h₁
  have H₂ := h₄ _ _ h₂
  clear h₄
  rw [mem_aSimPairs_iff_simulate_tr] at h₁ h₂
  choose hs₁ n₁ h₁ s₁' h₅ h₆ using h₁
  choose hs₂ n₂ h₂ s₂' h₇ h₈ using h₂
  simp at h₅ h₆ h₇ h₈
  by_cases H₃ : n₁ = n₂
  · subst H₃
    simp [h₁] at h₂
    exact h₂
  exfalso
  wlog H₄ : n₁ < n₂ with ih
  · push_neg at H₄
    specialize @ih s a d s₂ s₁ p fsp _ _ ha h₃
    grind
  clear H₃
  apply H₂; clear H₂
  rw [mem_aVisitedIcc_iff_of h₂]
  right
  use n₁, H₄, s₁, hs₁, h₁
  simpa

theorem State.aSimPtsNcard_spec_of_fresh1 {s fsp} {a : AStrat} [hs : sys.WF s]
(h : a.Fresh1 s fsp) (set : Set' PointZ) : ∀ (d : DStrat) [d.WF],
∃ n, s.aSimPtsNcard ⟨a, d⟩ set.toSet = some n ∧ n ≤ set.size := by
  intro d hd; simp [aSimPtsNcard]
  suffices h₁ : ∃ n, (s.aSimPairs ⟨a, d⟩ |>.filter (·.2 ∈ set)
    |>.image (·.2) |>.ncard?) = some n ∧ n ≤ set.size
  · choose n h₁ h₂ using h₁
    refine ⟨n, ?_, h₂⟩; clear h₂
    rwa [Set.ncard?_image_of_injOn] at h₁
    intro ⟨s₁, p₁⟩ hx ⟨s₂, p₂⟩ hy h₂
    simp at hx hy h₂
    rcases hx with ⟨hx, h₃⟩
    rcases hy with ⟨hy, h₄⟩
    subst h₂
    simp [aSimPairs_state_eq_of_point_eq_of_fresh1 h hx hy]
  suffices h₁ : ∃ n, (s.aSimPts ⟨a, d⟩ |>.filter (· ∈ set) |>.ncard?) = some n ∧ n ≤ set.size
  · choose n h₁ h₂ using h₁
    refine ⟨n, ?_, h₂⟩; clear h₂
    simp [Set.filter, aSimPts] at h₁ ⊢
    convert h₁; ext; simp
  simp_rw [←Set'.mem_toSet, Set.filter_fn_mem, Set.ncard?]
  rw [if_pos]
  rotate_left
  · apply Set.Finite.inter_of_right; simp
  simp; rw [←Set'.ncard_toSet]
  apply Set.ncard_inter_le_ncard_right; simp