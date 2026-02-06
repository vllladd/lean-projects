import AP.AP.FreshA.Nbhd
import AP.Temp

namespace AP

def AStrat.Fresh (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.Fresh1 s fsp ∧ ∀ (d : DStrat), d.WF → ∀ s₁ s' p p', (s₁, p) ∈ s.aSimPairs ⟨a, d⟩ →
  s' ∈ s.aSimStatesIco s₁ ⟨a, d⟩ → sys.validTr s' p' → p' ≠ a.f s' → p ≠ p'

def AStrat.FreshAux (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aPos ∉ fsp.get 0 ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁ s₂,
  sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧ sys.tr s₁ (a.f s₁) = some s₂ ∧
  s₂.aHwsDisj (fsp.offset (n * 2 + 1)
  |>.insertSet 0 (s.aVisited s₁ |>.erase s₁.aPos |>.bind (·.nbhd s.pw)).toSet
  |>.insertSet 2 (s₁.aPos.nbhd s.pw).toSet)

def aFreshCnd (s : State) (fsp : FSP) (s₂ : State) : Prop :=
  s₂.aHwsDisj # fsp.offset (s₂.diff s)
  |>.insertSet 0 (s.aVisited s₂.prev |>.erase s₂.prev.aPos |>.bind (·.nbhd s.pw)).toSet
  |>.insertSet 2 (s₂.prev.aPos.nbhd s.pw).toSet

noncomputable
def aFresh (s : State) (fsp : FSP) : AStrat :=
  aSeek # aFresh1Cnd s fsp

-----

theorem AStrat.Fresh.fresh1 {a : AStrat} {s fsp} (h : a.Fresh s fsp) : a.Fresh1 s fsp := h.1
theorem AStrat.Fresh.wf {a : AStrat} {s fsp} (h : a.Fresh s fsp) : a.WF := h.fresh1.wf

theorem AStrat.fresh_iff_alt₁ {a : AStrat} {s fsp} [hs : AState s] : a.Fresh s fsp ↔
a.Fresh1 s fsp ∧ ∀ (d : DStrat), d.WF → ∀ s₁ s' p p', (s₁, p) ∈ s.aSimPairs ⟨a, d⟩ →
s' ∈ s.aSimStatesIco s₁ ⟨a, d⟩ → sys.validTr s' p' → p ≠ p' := by
  unfold Fresh
  rw [and_congr_right_iff]
  intro h
  symm; constructor <;> intro h₁ d hd s₁ s' p p' h₂ h₃ h₄ <;>
    specialize h₁ d hd s₁ s' p p' h₂ h₃ h₄; simp [h₁]
  rw [imp_iff_or_not] at h₁
  simp at h₁
  rcases h₁ with h₁ | rfl; exact h₁
  replace h := h.2.2 d hd
  rw [State.mem_aSimPairs_iff_simulate_tr] at h₂
  rcases h₂ with ⟨hs₁, n, h₂, s₂, h₅, h₆⟩
  simp at h₅ h₆
  contrapose! h
  rw [←h] at h₄
  rw [h₆] at h₅
  use s₁, p
  split_ands
  · simp [State.mem_aSimPairs_iff_simulate_tr, hs₁, h₆]
    exact ⟨⟨_, h₂⟩, _, h₅⟩
  rcases h₄ with ⟨sx, h₄⟩
  rw [State.mem_aSimStatesIco_iff_of h₂] at h₃
  rcases h₃ with ⟨hs', k, hk, h₃⟩
  rw [State.mem_aVisited_iff_of h₂]
  right
  use k, hk, s', hs', h₃
  simp [h]

theorem AStrat.fresh_iff_alt₂ {a : AStrat} {s fsp} [hs : AState s] : a.Fresh s fsp ↔
a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF → ∀ s₁ s' p p',
(s₁, p) ∈ s.aSimPairs ⟨a, d⟩ → s' ∈ s.aSimStatesIco s₁ ⟨a, d⟩ →
p'.dist s'.aPos ≤ ↑s.pw → p ≠ p' := by
  rw [fresh_iff_alt₁]
  constructor
  · rintro ⟨⟨ha, hw, h₁⟩, h₂⟩
    use ha, hw
    intro d hd s₁ s' p p' h₃ h₄ h₅
    specialize h₁ d hd
    specialize h₂ d hd
    rintro rfl
    by_cases h₆ : s'.aPos = p
    · clear h₂
      subst h₆
      specialize h₁ _ _ h₃
      apply h₁; clear h₁ h₅
      rw [State.mem_aSimStatesIco_iff] at h₄
      rcases h₄ with ⟨hs', k, n, hk, h₄, h₁⟩
      rw [State.mem_aSimPairs_iff_simulate_tr] at h₃
      rcases h₃ with ⟨hs₁, n', H₁, s₂, H₂, H₃⟩
      dsimp at H₂ H₃
      cases steps_eq_of_simulate_full_eq h₁ H₁
      clear H₁
      rw [State.mem_aVisited_iff_of h₁]
      have H₄ := AState.even_of_simulate h₄
      rw [Nat.even_iff_exi] at H₄
      rcases H₄ with ⟨k, rfl⟩
      cases k
      · left
        simp at h₄
        rw [h₄]
      nm k
      right
      simp [add_mul] at h₄
      obtain ⟨s₄, ⟨s₃, h₄, H₁⟩, H₅⟩ := h₄
      have hs₃ := AState.of_simulate_mul_two_eq_full h₄
      have hs₄ := DState.of_tr H₁
      use k * 2, by omega, s₃, hs₃, h₄
      simp at H₁ ⊢
      rw [DState.aPos_eq_of_tr H₅, AState.aPos_eq_of_tr H₁]
    · clear h₁
      specialize h₂ s₁ s' p p h₃ h₄
      simp at h₂
      rw [State.mem_aSimPairs_iff_simulate_tr] at h₃
      rcases h₃ with ⟨hs₁, n, h₃, s₂, H₁, H₂⟩
      dsimp at H₁ H₂
      subst H₂
      rw [State.mem_aSimStatesIco_iff] at h₄
      rcases h₄ with ⟨hs', k, n', hk, H₃, H₄⟩
      cases steps_eq_of_simulate_full_eq h₃ H₄
      clear H₄
      rw [Option.eq_none_iff_forall_ne_some] at h₂
      simp [AState.tr_eq_some_iff] at H₁ h₂
      simp [h₆] at h₂
      rcases H₁ with ⟨⟨H₁, H₅, H₆⟩, rfl⟩
      contrapose! h₂; clear h₂
      replace hk := Nat.exists_eq_add_of_le # le_of_lt hk
      obtain ⟨n, rfl⟩ := hk
      simp [H₃] at h₃
      have H₇ := sys.reachable_of_simulate_eq h₃
      split_ands
      · apply Set'.not_mem_of_subset _ H₅
        exact taken_subset_of_reachable H₇
      rw [←pw_eq_of_reachable H₇, State.pw_eq_of_simulate_eq h₃]
      rwa [State.pw_eq_of_simulate_eq H₃]
  · rintro ⟨ha, hw, h⟩
    symm; constructor
    · intro d hd s₁ s' p p' h₁ h₂ h₃
      apply h d hd s₁ s' p p' h₁ h₂; clear h
      rw [State.mem_aSimStatesIco_iff] at h₂
      rcases h₂ with ⟨hs', k, n, hk, h₂, h₄⟩
      choose s₂ h₃ using h₃
      have h₅ := sys.reachable_of_simulate_eq h₂
      rw [←pw_eq_of_reachable h₅]
      rw [←AState.aPos_eq_of_tr h₃]
      exact AState.aPos_dist_le_of_tr h₃
    use ha, hw
    intro d hd s₁ p h₁
    specialize h d hd
    rw [State.mem_aSimPairs_iff_simulate_tr] at h₁
    rcases h₁ with ⟨hs₁, n, h₁, s₂, h₂, h₃⟩
    dsimp at h₂ h₃; subst h₃
    rw [State.mem_aVisited_iff_of h₁]
    push_neg
    split_ands
    · intro h₃
      specialize h s₁ s s.aPos s.aPos
      simp [State.mem_aSimPairs_iff_simulate_tr] at h
      specialize h hs₁ n h₁ s₂ h₂ h₃
      apply h; clear h
      simp [State.mem_aSimStatesIco_iff]
      use hs
      have h₄ : n ≠ 0
      · rintro rfl
        simp at h₁
        subst h₁
        contrapose! h₃; clear h₃
        rw [←AState.aPos_eq_of_tr h₂]
        exact AState.aPos_ne_of_tr h₂
      use n, by omega
    intro k hk s' hs' h₃ h₄
    simp at h₄
    specialize h s₁ s' s₂.aPos s₂.aPos
    simp [State.mem_aSimPairs_iff_simulate_tr] at h
    specialize h hs₁ n h₁ s₂ h₂ _ _
    · rw [AState.aPos_eq_of_tr h₂]
    · simp [State.mem_aSimStatesIco_iff]
      use hs', k, n
    contrapose! h; clear h
    rw [AState.aPos_eq_of_tr h₂, ←h₄]
    suffices h₅ : sys.validTr s' (a.f s')
    · choose s₃ h₅ using h₅
      rw [←AState.aPos_eq_of_tr h₅]
      rw [←State.pw_eq_of_simulate_eq h₃]
      exact AState.aPos_dist_le_of_tr h₅
    have h₅ : ∃ s₃, sys.simulate (Strat.f ⟨a, d⟩) s (k + 1) = (s₃, 0)
    · simp only [Prod.ext_iff, exists_and_right, exists_eq', true_and]
      apply sys.simulate_snd_eq_zero_of_le_and_eq_zero (n := n)
      simp [h₁]; omega
    choose s₃ h₅ using h₅
    simp [h₃] at h₅
    use s₃

theorem AStrat.fresh_iff_alt₃ {a : AStrat} {s fsp} [hs : AState s] : a.Fresh s fsp ↔
a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF → ∀ s₁ s' p,
(s₁, p) ∈ s.aSimPairs ⟨a, d⟩ → s' ∈ s.aSimStatesIco s₁ ⟨a, d⟩ → p ∉ s'.aPos.nbhd s.pw := by
  rw [fresh_iff_alt₂]
  congr!
  nm d hd s₁ s' p
  simp
  constructor
  · intro h h₁ h₂
    specialize h p h₁ h₂
    simp at h
    rwa [Point.dist_comm]
  · intro h p' h₁ h₂ h₃ rfl
    specialize h h₁ h₂
    contrapose! h; clear h
    rwa [Point.dist_comm]

#check 0 #exit

theorem AStrat.fresh_iff_alt₄ {a : AStrat} {s fsp} [hs : AState s] : a.Fresh s fsp ↔
a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF → ∀ s₁ p, (s₁, p) ∈ s.aSimPairs ⟨a, d⟩ →
p ∉ (s.aVisited s₁ |>.erase s₁.aPos |>.bind (·.nbhd s.pw)) := by
  rw [fresh_iff_alt₃]
  congr!
  nm d hd s₁
  simp
  constructor
  ·
    rintro h p h₁ p' h₂ h₃
    
    choose hs₁ n h₅ s₂ h₆ h₇ using State.mem_aSimPairs_iff_simulate_tr.mp h₁
    dsimp at h₆ h₇
    subst h₇
    
    rw [State.mem_aVisited_iff_mem_simStatesIcc h₅] at h₃
    obtain ⟨s', h₃, rfl⟩ := h₃
    rw [←AState.aPos_eq_of_tr h₆] at *
    
    specialize h s' _ h₁ _
    ·
      apply State.mem_aSimStatesIco_mem_aSimStatesIcc_and_ne
      ·
        use h₃
        simp

#check 0 #exit

@[simp]
instance {s fsp} : aFresh s fsp |>.WF := by
  unfold aFresh; infer_instance

theorem AState.aForallWinsDisj_of_freshAux {s fsp} {a : AStrat} [hs : AState s]
(h : a.FreshAux s fsp) : s.aForallWinsDisj fsp a := by
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
    simp [FSP.hasLe, FSP.insertSet] at h₄ ⊢
    intro k hk
    have h₅ := h₄ 0
    specialize h₄ 1
    simp at h₄ h₅
    choose h₅ h₆ using h₅
    rw [Nat.le_add_one_iff] at hk
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
    exact h₃.2

theorem AState.fresh_of_freshAux {s fsp} {a : AStrat} [hs : AState s]
(h : a.FreshAux s fsp) : a.Fresh s fsp := by
  have H₀ := h
  choose ha h₀ h using h
  rw [AStrat.fresh_iff_alt₁]
  use ha, aForallWinsDisj_of_freshAux H₀
  intro d hd s₁ p p' h₁ ⟨s', h₁'⟩
  rw [State.mem_aPtsSimAt_iff_simulate_tr] at h₁
  choose hs₁ n h₁ s₂ h₂ h₃ using h₁
  simp at h₂ h₃; subst h₃
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
  specialize h d hd n
  simp [h₁, h₂] at h
  rw [←AState.aPos_eq_of_tr h₁']
  choose a₁ ha₁ h using h
  specialize h d hd 0
  simp at h
  
  replace h := h.1
  contrapose! h
  
  use s'.aPos
  simp [h]
  simp [ne_symm' # AState.aPos_ne_of_tr h₁']
  
  -- specialize h _ H₁
  -- contrapose! h; clear h
  -- rw [AState.tr_eq_some_iff] at h₁' h₂
  -- rcases h₁' with ⟨⟨H₂, H₃, H₄⟩, rfl⟩
  -- rcases h₂ with ⟨⟨H₅, H₆, H₇⟩, rfl⟩
  -- simp
  -- dsimp at H₁

#check 0 #exit

-- theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
-- (h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
--   use aFresh1 s fsp
--   apply hs.fresh1_of_fresh1Aux
--   use inferInstance
--   use State.aPos_notMem_of_aHwsDisj h
--   intro d hd n
--   induction n
--   · simp
--     have h₁ := @hs.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
--     specialize h₁ _
--     · clear h₁
--       unfold aFresh1Cnd
--       replace h := aHwsDisj_insert_one_aPos h
--       choose a₁ ha₁ h using h
--       have h₁ := h d hd 1
--       simp at h₁
--       choose s₁ h₁ h₂ using h₁
--       use a₁.f s, s₁, h₁, a₁, ha₁
--       simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁]
--       intro d₁ hd₁ n
--       specialize h d₁ hd₁ (n + 1)
--       simp_rw [sys.simulate_succ_full'] at h
--       simp [h₁] at h
--       choose s₂ h h₃ using h
--       use s₂, h
--       simp [FSP.hasLe, FSP.insert, FSP.insertSet, FSP.next] at h₃ ⊢
--       grind
--     unfold aFresh1
--     choose s₂ h₁ h₂ using h₁
--     use s₂, h₁
--     unfold aFresh1Cnd at h₂
--     simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁] at h₂
--     exact h₂
--   nm n ih
--   choose s₁ s₂ h₁ h₂ h₃ using ih
--   have hs₁ := AState.of_simulate_mul_two_eq' h₁
--   have hs₂ := DState.of_tr h₂
--   choose s₃ h₄ using hd.validTr s₂
--   have hs₃ := AState.of_tr h₄
--   simp [Nat.add_mul, h₁, h₂, h₄]
--   have G₁ := sys.reachable_of_simulate_eq h₁
--   have G₂ := sys.reachable_right G₁ h₂
--   have G₃ := sys.reachable_right G₂ h₄
--   have h₅ := @hs₃.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
--   specialize h₅ _
--   · clear h₅
--     unfold aFresh1Cnd
--     replace h₃ := DState.aHwsDisj_insert_two_aPos h₃
--     choose a₁ ha₁ h₃ using h₃
--     have H₁ := h₃ d hd 2
--     simp [h₄] at H₁
--     choose s₄ H₁ H₂ using H₁
--     use a₁.f s₃, s₄, H₁, a₁, ha₁
--     rw [State.diff_eq_of_tr H₁ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁]
--     rw [State.diff_eq_of_simulate_full h₁]
--     rw [State.prev_eq_of_tr H₁, DState.aVisited_eq_of_tr h₄ G₂, AState.aVisited_eq_of_tr h₂ G₁]
--     intro d₁ hd₁ n₁
--     specialize h₃ (d₁.set s₂ # d.f s₂) (DStrat.wf_set_of_tr h₄) (n₁ + 2)
--     simp_rw [sys.simulate_succ_full'] at h₃
--     simp [h₄, H₁] at h₃
--     choose s₅ H₃ H₄ using h₃
--     use s₅
--     have hs₄ := sys.wf_of_tr H₁
--     split_ands
--     · convert H₃ using 1
--       symm
--       apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, h₄⟩
--       rw [length_hist_eq_of_tr H₁, length_hist_eq_of_tr h₄]
--       omega
--     simp
--     rw [←AState.aPos_eq_of_tr h₂]
--     simp [FSP.hasLe] at H₄ ⊢
--     simp [Nat.add_assoc]
--     intro k hk
--     cases k
--     rotate_left
--     · nm k
--       specialize H₄ (k + 3) (by omega)
--       simp at H₄ ⊢
--       ring_nf at H₄ ⊢
--       exact H₄
--     simp
--     split_ands
--     · specialize H₄ 2 (by omega)
--       simp at H₄
--       exact H₄.1
--     · specialize H₄ 0 (by omega)
--       simp at H₄
--       exact H₄.1
--     · intro k hk
--       iterate 2 rw [Nat.le_add_one_iff] at hk
--       rcases hk with ((hr | rfl) | rfl)
--       · specialize H₄ 0 (by omega)
--         simp at H₄
--         exact H₄.2 k hr
--       · specialize H₄ 1 (by omega)
--         simp at H₄
--         exact H₄
--       · specialize H₄ 2 (by omega)
--         simp at H₄
--         exact H₄.2
--   choose s₄ h₅ h₆ using h₅
--   use s₄, h₅
--   unfold aFresh1Cnd at h₆
--   rw [State.diff_eq_of_tr h₅ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁] at h₆
--   rw [State.diff_eq_of_simulate_full h₁] at h₆
--   simp [Nat.add_assoc] at h₆ ⊢
--   have hs₄ := DState.of_tr h₅
--   rw [State.prev_eq_of_tr h₅] at h₆
--   exact h₆

-- theorem State.aPtsSimAt_state_eq_of_point_eq_of_fresh1 {s : State} {a : AStrat} {d : DStrat}
-- {s₁ s₂ p fsp} [hs : sys.WF s] [hd : d.WF] (h : a.Fresh1 s fsp)
-- (h₁ : (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩) (h₂ : (s₂, p) ∈ s.aPtsSimAt ⟨a, d⟩) : s₁ = s₂ := by
--   choose ha h₃ h₄ using h
--   specialize h₄ d hd
--   have H₁ := h₄ _ _ h₁
--   have H₂ := h₄ _ _ h₂
--   clear h₄
--   rw [mem_aPtsSimAt_iff_simulate_tr] at h₁ h₂
--   choose hs₁ n₁ h₁ s₁' h₅ h₆ using h₁
--   choose hs₂ n₂ h₂ s₂' h₇ h₈ using h₂
--   simp at h₅ h₆ h₇ h₈
--   by_cases H₃ : n₁ = n₂
--   · subst H₃
--     simp [h₁] at h₂
--     exact h₂
--   exfalso
--   wlog H₄ : n₁ < n₂ with ih
--   · push_neg at H₄
--     specialize @ih s a d s₂ s₁ p fsp _ _ ha h₃
--     grind
--   clear H₃
--   apply H₂; clear H₂
--   rw [mem_aVisited_iff_of h₂]
--   right
--   use n₁, H₄, s₁, hs₁, h₁
--   simpa