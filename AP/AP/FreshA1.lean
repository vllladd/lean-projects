import AP.AP.DisjA

namespace AP

def State.HasDReenter (s : State) (fsp : FSP) : Prop :=
  ∀ (a : AStrat), a.WF → s.aForallWinsDisj fsp a → ∃ (d : DStrat), d.WF ∧
  ∃ n sd, DState sd ∧ sys.simulate (Strat.f ⟨a, d⟩) s n = (sd, 0) ∧ sd.aPos = s.aPos

-----

theorem AState.hasDReenter_of_not_aHwsDisj_insert_aPos {s fsp}
[hs : AState s] (h₁ : ¬s.aHwsDisj (fsp.insert 1 s.aPos)) : s.HasDReenter fsp := by
  intro a ha h₂
  simp [State.aHwsDisj, State.aForallWinsDisj] at h₁
  specialize h₁ a ha
  choose d hd h₁ using h₁
  use d, hd
  simp [State.aWinsDisj] at h₁
  choose n h₁ using h₁
  specialize h₂ d hd
  rw [State.aWinsDisj_iff] at h₂
  choose h₂ h₃ using h₂
  specialize h₂ n
  generalize hr : sys.simulate (Strat.f ⟨a, d⟩) s n = r at h₂
  rcases r with ⟨s₁, r⟩
  dsimp at h₂; subst h₂
  specialize h₁ s₁ hr
  simp [FSP.hasLe, FSP.insert, FSP.insertSet] at h₁
  choose k hk h₁ using h₁
  specialize h₃ n
  simp [hr, FSP.hasLe] at h₃
  specialize h₃ k hk
  split_ifs at h₁ with h₄
  rotate_left; contradiction
  subst h₄
  simp [h₃] at h₁
  have hs₁ : sys.WF s₁ := sys.wf_of_simulate_eq hr
  replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  rotate_left; use n, s₁
  cases n
  · simp at hk
  nm n
  have hr₁' := hr
  rw [sys.simulate_add] at hr
  simp at hr
  rename' hr => hr₁
  generalize hr : sys.simulate (Strat.f ⟨a, d⟩) s n = r at hr₁
  rcases r with ⟨s', r⟩
  dsimp at hr₁
  obtain rfl : r = 0
  · rw [Prod.snd_eq_of_eq_mk hr]
    apply sys.simulate_snd_eq_zero_of_le_and_eq_zero # Prod.snd_eq_of_eq_mk hr₁' |>.symm
    simp
  simp at hr₁
  have hs' : DState s'
  · use sys.wf_of_simulate_eq hr
    simp [State.aTurn_eq_of_tr' hr₁]
  use n, s', hs', hr
  rw [←DState.aPos_eq_of_tr hr₁, h₁]

theorem AState.not_aHwsDisj_insert_aPos_of_hasDReenter {s fsp}
[hs : AState s] (h : s.HasDReenter fsp) : ¬s.aHwsDisj (fsp.insert 1 s.aPos) := by
  rintro ⟨a, ha, h₁⟩
  specialize h a ha # State.aForallWinsDisj_of_aForallWinsDisj_insert h₁
  choose d hd n sd hsd h₄ h₅ using h
  specialize h₁ d hd n
  choose sd' h₁ h₆ using h₁
  simp [h₄] at h₁
  subst h₁
  simp [FSP.hasLe, FSP.insert, FSP.insertSet, h₅] at h₆
  have h₇ : n ≠ 0
  · rintro rfl
    simp at h₄
    subst h₄
    cases hsd; nm H₁ H₂; simp at H₂
  specialize h₆ 1 (by omega)
  simp at h₆

theorem AState.hasDReenter_iff_not_aHwsDisj_insert_aPos {s fsp}
[hs : AState s] : s.HasDReenter fsp ↔ ¬s.aHwsDisj (fsp.insert 1 s.aPos) :=
  ⟨not_aHwsDisj_insert_aPos_of_hasDReenter, hasDReenter_of_not_aHwsDisj_insert_aPos⟩

theorem AState.hasDReenter_of_taken_subset {fsp s s'} [hs : AState s] [hs' : AState s']
(h : s.HasDReenter fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (h₁ : s.taken ⊆ s'.taken) : s'.HasDReenter fsp := by
  rw [hasDReenter_iff_not_aHwsDisj_insert_aPos] at h ⊢
  contrapose! h
  symm at hpw ht hpa
  have h₃ := @State.aHwsDisj_of_taken_subset (fsp.insert 1 s.aPos) s' s _ _
    (by rwa [hpa]) hpw ht hpa h₁
  exact State.aHwsDisj_of_aHwsDisj_insertSet h₃

theorem AState.aHwsDisj_insert_one_aPos {s fsp} [hs : AState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insert 1 s.aPos := by
  choose a ha h using h
  by_contra h₀
  rw [←AState.hasDReenter_iff_not_aHwsDisj_insert_aPos] at h₀
  choose d hd n sd hsd h₂ h₃ using h₀ a ha h
  generalize hM : (Set'.ofList # s.aPos.nbhd s.pw).erase s.aPos = M
  generalize hN : (M \ sd.taken).size = N
  induction N using Nat.strong_induction_on generalizing s d n sd
  nm N ih
  by_cases h₄ : N = 0
  · clear ih
    subst h₄ hM
    simp at hN
    rw [Set'.diff_eq_empty_iff_subset] at hN
    specialize h d hd
    rw [State.aWinsDisj_iff] at h
    replace h := h.1
    specialize h (n + 2)
    rw [sys.simulate_add] at h
    simp [h₂] at h
    choose s₁ h₄ s₂ h₅ using h
    have hs₁ := AState.of_tr h₄
    simp at h₅
    specialize hN s₂.aPos
    simp at hN
    rw [AState.tr_eq_some_iff] at h₅
    rcases h₅ with ⟨⟨h₅, h₆, h₇⟩, rfl⟩
    rw [DState.aPos_eq_of_tr h₄, h₃] at *
    dsimp at hN
    specialize hN h₅
    rw [Point.dist_comm, pw_eq_of_tr h₄, State.pw_eq_of_simulate_eq h₂] at h₇
    specialize hN h₇
    apply h₆
    apply Set'.mem_of_subset _ hN
    exact taken_subset_of_tr h₄
  obtain ⟨p, hp₁, hp₂, hp₃⟩ : ∃ p, p ∉ sd.taken ∧ p.dist sd.aPos ≤ sd.pw ∧ sd.aPos ≠ p
  · replace h₄ : M \ sd.taken ≠ ∅
    · rw [←hN] at h₄
      simp at h₄
      exact h₄
    replace h₄ := Set'.exi_mem_of_ne_empty h₄
    choose p h₄ using h₄
    simp [←hM] at h₄
    use p
    obtain ⟨⟨hp₃, hp₂⟩, hp₁⟩ := h₄
    rw [h₃]
    refine ⟨hp₁, ?_, hp₃⟩
    rwa [Point.dist_comm, State.pw_eq_of_simulate_eq h₂]
  have h₅ : sys.validTr sd p
  · rw [DState.validTr_iff]
    use hp₃
  choose sa h₅ using h₅
  have hsa := AState.of_tr h₅
  have h₆ : sd.aForallWinsDisj fsp a
  · have h := State.aForallWinsDisj_of_simulate_eq h h₂
    exact State.aForallWinsDisj_of_aForallWinsDisj_offset h
  replace h₆ := DState.tr_of_aForallWinsDisj h₆ h₅
  replace h₆ := State.aForallWinsDisj_of_aForallWinsDisj_next h₆
  have h₇ : s.taken ⊆ sa.taken
  · apply Set'.subset_trans _ # taken_subset_of_tr h₅
    exact taken_subset_of_reachable # sys.reachable_of_simulate_eq h₂
  have h₈ : sa.HasDReenter fsp
  · apply AState.hasDReenter_of_taken_subset h₀
    · rw [pw_eq_of_tr h₅, State.pw_eq_of_simulate_eq h₂]
    · simp
    · rwa [DState.aPos_eq_of_tr h₅]
    · exact h₇
  choose d₁ hd₁ n₁ sd₁ hsd₁ H₁ H₂ using h₈ a ha h₆
  generalize hN₁ : (M \ sd₁.taken).size = N₁
  have H₄ : sys.Reachable sd sd₁
  · apply sys.reachable_of_tr h₅ |>.trans
    exact sys.reachable_of_simulate_eq H₁
  have H₃ := taken_subset_of_reachable H₄
  have H₅ : N₁ < N
  · rw [←hN, ←hN₁]
    apply Set'.size_lt_of_ssubset
    apply Set'.diff_ssubset_of_right H₃
    use p
    simp [←hM, hp₁, ←h₃, hp₃, ←State.pw_eq_of_simulate_eq h₂]
    rw [Point.dist_comm]
    use hp₂
    apply State.mem_taken_of_reachable # sys.reachable_of_simulate_eq H₁
    exact DState.mem_taken_of_tr h₅
  apply @ih N₁ H₅ sa hsa h₆ h₈ d₁ hd₁ n₁ sd₁ hsd₁ H₁ H₂ _ hN₁
  rw [DState.aPos_eq_of_tr h₅, h₃]
  rw [pw_eq_of_tr h₅, State.pw_eq_of_simulate_eq h₂]
  exact hM

theorem DState.forall_tr_of_aHwsDisj {s fsp} [hs : DState s] (h : s.aHwsDisj fsp) :
∀ p s', sys.tr s p = some s' → s'.aHwsDisj fsp.next :=
  λ _ _ h₁ => tr_of_aHwsDisj h h₁

theorem DState.forall_tr_exi_aForallWinsDisj_of_aHwsDisj {s fsp} [hs : DState s]
(h : s.aHwsDisj fsp) : ∀ p, ∃ (a : AStrat), a.WF ∧
∀ s', sys.tr s p = some s' → s'.aForallWinsDisj fsp.next a := by
  intro p
  have h₁ := DState.forall_tr_of_aHwsDisj h p
  cases h₂ : sys.tr s p
  · use default, inferInstance; simp
  nm s₁
  simp
  specialize h₁ s₁ h₂
  exact h₁

theorem DState.aHwsDisj_iff_forall_tr_exi_aForallWinsDisj {s fsp} [hs : DState s] :
s.aHwsDisj fsp ↔ ∀ p, ∃ (a : AStrat), a.WF ∧
∀ s', sys.tr s p = some s' → s'.aForallWinsDisj fsp.next a := by
  use forall_tr_exi_aForallWinsDisj_of_aHwsDisj
  intro h
  choose A hA h using h
  use .mk # λ s₁ => A (s₁.getMoveAt s).iget |>.f s₁
  use inferInstance
  intro d hd
  obtain ⟨s', h₁⟩ := d.validTr s
  specialize h _ _ h₁
  intro n
  cases n
  · simp
    specialize h d hd 0
    simp at h
    rw [←DState.aPos_eq_of_tr h₁]
    exact h.1
  nm n
  specialize h d hd n
  have hs' := AState.of_tr h₁
  choose s₁ h₂ h₃ using h
  use s₁
  split_ands
  rotate_left
  · contrapose! h₃
    rwa [FSP.hasLe_next]
  simp [h₁]
  rw [←h₂]
  apply simulate_congr _ # by simp
  intro k hk sa hsa H₁ H₂ H₃
  simp
  have H₄ : sa.getMoveAt s = some (d.f s)
  · apply getMoveAt_eq_some_of_tr_and_reachable h₁
    exact sys.reachable_of_simulate_eq H₂
  simp [H₄, Option.iget, AStrat.validTr H₃]

theorem DState.aHwsDisj_iff_forall_tr {s fsp} [hs : DState s] :
s.aHwsDisj fsp ↔ ∀ p s', sys.tr s p = some s' → s'.aHwsDisj fsp.next := by
  rw [aHwsDisj_iff_forall_tr_exi_aForallWinsDisj]
  unfold State.aHwsDisj
  apply forall_congr'; intro p
  cases h : sys.tr s p
  · simp
    use default
    infer_instance
  nm s₁
  simp

theorem DState.aHwsDisj_insert_two_aPos {s fsp} [hs : DState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insert 2 s.aPos := by
  rw [DState.aHwsDisj_iff_forall_tr]
  intro p s' h₁
  have hs' := AState.of_tr h₁
  replace h := tr_of_aHwsDisj h h₁
  replace h := AState.aHwsDisj_insert_one_aPos h
  rwa [FSP.next_insert_succ, ←DState.aPos_eq_of_tr h₁]

theorem State.aHwsDisj_insert_two_aPos {s fsp} [hs : sys.WF s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insert 2 s.aPos := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · apply State.aHwsDisj_insert_of_le
    . exact hs.aHwsDisj_insert_one_aPos h
    · simp
  · exact DState.aHwsDisj_insert_two_aPos h

-- #check 0 #exit

theorem AState.aHwsDisj_nbhd_pw {s : State} {fsp : FSP} [hs : AState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insertSet 3 # s.aPos.nbhd s.pw |>.toSet := by
  --   obtain ⟨a, Ha, h⟩ := h
  --   
  --   -- have H₀ := s.eventually_simulate_dChooseFromSet_subset_taken
  --   --   (a := a) (ps := s.aPos.nbhd s.pw)
  --   -- dsimp at h
  --   -- use N
  --   -- intro n hn s' h₁
  --   -- specialize h n hn s' h₁
  --   -- have hs' := sys.wf_of_simulate_eq h₁
  --   -- intro h₂
  --   -- specialize h _ h₂
  --   -- simp at h
  -- 
  --   have H₀ := s.eventually_simulate_dChooseFromSet_subset_taken
  --     (a := a) (ps := s.aPos.nbhd s.pw)
  --   simp at H₀
  --   generalize h₀ : dChooseFromSet (Set'.ofList # s.aPos.nbhd s.pw) = d at H₀
  --   have hd : d.WF; subst h₀; infer_instance
  --   generalize hF : sys.simulate (Strat.f ⟨a, d⟩) = F at H₀
  --   rw [eventually_iff_exi_least] at H₀
  --   rcases H₀ with H₀ | H₀
  --   · subst hF
  --     specialize H₀ 0 s rfl s.aPos
  --     simp at H₀
  --   
  --   push_neg at H₀
  --   obtain ⟨k, ⟨sa, h₁, h₃'⟩, H₂'⟩ := H₀
  --   
  --   have h₃ : Point.dist s.aPos sa.aPos ≤ s.pw
  --   ·
  --     
  --   
  --   #check 0 #exit
  --   
  --   have h₂ : ∀ (n : ℕ), N < n → ∀ (s' : State), F s n = (s', 0) →
  --     ↑s.pw < Point.dist s.aPos s'.aPos
  --   
  --   replace h₂ : ∀ {n s'}, F s n = (s', 0) → k < n →
  --     s.pw < Point.dist s.aPos s'.aPos; tauto
  --   
  --   push_neg at h₁
  --   
  --   have H₁ : ∀ {n r s'}, F s n = (s', r) → sys.WF s'
  --   · intro n r hn h₄; rw [←hF] at h₄
  --     exact sys.wf_of_simulate_eq h₄
  --   
  --   have H₂ : ∀ n, ∃ s', F s n = (s', 0)
  --   · rw [←hF]
  --     intro n
  --     specialize h d hd
  --     replace h := State.aWins_of_aWinsDisj h
  --     specialize h n
  --     simpa [Prod.ext_iff]
  --   
  --   have H₃ : ∀ {n r s'}, F s n = (s', r) → sys.Reachable s s'
  --   · intro n r s' H₃; rw [←hF] at H₃
  --     exact sys.reachable_of_simulate_eq H₃
  --   
  --   obtain ⟨sd, h₄, h₅⟩ : ∃ sd, F s (k + 1) = (sd, 0) ∧ sys.tr sa (Strat.f ⟨a, d⟩ sa) = sd
  --   · obtain ⟨sd, h₄⟩ := H₂ (k + 1)
  --     use sd
  --     rw [←hF] at h₁ h₄ ⊢
  --     use h₄
  --     rw [sys.simulate_add, h₁] at h₄
  --     simp at h₄
  --     exact h₄
  --   
  --   have hsa := H₁ h₁
  --   
  --   have h₆ : s.pw < Point.dist s.aPos sd.aPos
  --   · apply h₂ h₄; simp
  --   
  --   replace hsa : AState sa
  --   · apply AState.of_tr_aPos_ne h₅
  --     apply ne_of_congr (Point.dist s.aPos · ≤ s.pw)
  --     simpa [h₃]
  --   
  --   have hsd := DState.of_tr h₅
  --   
  --   simp at h₅
  --   
  --   have hpwa := pw_eq_of_reachable # H₃ h₁
  --   
  --   have h₇ : sa.aPos ≠ s.aPos
  --   · have h₅' := h₅
  --     rw [AState.tr_eq_some_iff] at h₅
  --     rcases h₅ with ⟨⟨h₅, h₇, h₈⟩, rfl⟩
  --     intro H₄
  --     rw [hpwa, Point.dist_comm, H₄] at h₈
  --     linarith
  --   
  --   have hk : k ≠ 0
  --   · rintro rfl
  --     rw [←hF] at h₁
  --     simp at h₁
  --     subst h₁
  --     simp at h₇
  --   
  --   -- have h₈ : sa.aForallWinsDisj fsp.next a
  --   -- · rw [←hF] at h₁
  --   --   have H₄ := s.aForallWinsDisj_of_simulate_eq h h₁
  --   --   cases k; simp at hk; nm k
  --   --   rw [FSP.offset_succ] at H₄
  --   --   exact sa.aForallWinsDisj_of_aForallWinsDisj_offset H₄
  --   
  --   have h₈ : sa.aForallWinsDisj (fsp.insertSet 1 (s.aPos.nbhd s.pw).toSet) a
  --   · rw [←hF] at h₁
  --     have H₄ := s.aForallWinsDisj_of_simulate_eq h h₁
  --     replace H₄ := State.aForallWinsDisj_of_aForallWinsDisj_offset H₄
  --     sorry
  --   
  -- -- #check 0 #exit
  -- 
  --   obtain ⟨s', H₄⟩ : ∃ s', sys.tr s sa.aPos = some s'
  --   · simp [AState.tr_eq_some_iff] at h₅ ⊢
  --     rcases h₅ with ⟨⟨H₄, H₅, H₆⟩, rfl⟩
  --     dsimp at *
  --     rw [Point.dist_comm]
  --     refine ⟨ne_symm' h₇, ?_, h₃⟩
  --     rw [←hF] at h₁
  --     have H : sa.aPos ∉ sa.taken; simp
  --     contrapose! H
  --     apply State.mem_taken_of_reachable _ H
  --     exact sys.reachable_of_simulate_eq h₁
  --   
  --   have hs' := DState.of_tr H₄
  --   
  --   -- have G : sd.pw = s.pw
  --   -- · rw [pw_eq_of_tr h₅, hpwa]
  --   -- have G₁ : s'.pw = s.pw
  --   -- · rw [pw_eq_of_tr H₄]
  --   -- have G₂ : s'.aPos = sd.aPos
  --   
  --   obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ + 1 = k
  --   ·
  --     cases k
  --     · simp at hk
  --     simp
  --   clear hk
  --   
  --   -----
  --   
  --   obtain ⟨sd₀, H₅⟩ := H₂ k₀
  --   have hsd₀ : DState sd₀
  --   ·
  --     rw [←hF] at h₁ H₅
  --     rw [←hk₀] at h₁
  --     use sys.wf_of_simulate_eq H₅
  --     rw [State.aTurn_eq_of_simulate_eq H₅]
  --     have H₆ := State.aTurn_eq_of_simulate_eq h₁
  --     simp at H₆ ⊢
  --     exact H₆
  --   
  --   have H₆ : sys.tr sd₀ (d.f sd₀) = sa
  --   ·
  --     rw [←hF] at h₁ H₅
  --     rw [←hk₀] at h₁
  --     rw [sys.simulate_add, H₅] at h₁
  --     simp at h₁
  --     exact h₁
  --   
  --   have H₇ : F s k = (sa, 0)
  --   · rw [←hF] at H₅
  --     rw [←hk₀, ←hF, sys.simulate_add, H₅]
  --     simpa
  --   
  --   have H₈ : sd₀.aHwsDisj # fsp.insertSet 2 # s.aPos.nbhd s.pw |>.toSet
  --   ·
  --     -- use a, Ha
  --     -- intro d₁ hd₁
  --     -- rw [State.aWinsDisj_iff]
  --     -- split_ands
  --     -- ·
  --     --   specialize h₈ (d₁.set sd₀ # d.f sd₀) # DStrat.wf_set_of_tr H₆
  --     --   rw [State.aWinsDisj_iff] at h₈
  --     --   replace h₈ := h₈.1
  --     --   intro r
  --     --   cases r
  --     --   · simp
  --     --   nm r
  --     --   specialize h₈ r
  --     --   replace h₈ : (sys.simulate (Strat.f ⟨a, d₁⟩) sa r).2 = 0
  --     --   ·
  --     --     convert h₈ using 2
  --     --     symm;
  --     --     apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, H₆⟩
  --     --     simp [hist_eq_of_tr H₆]
  --     --   simp
  --     --   use sa
  --     --   simp [h₈]
  --     --   sorry
  --     -- ·
  --     --   sorry
  --     sorry
  --   
  --   sorry
  obtain ⟨a, Ha, h⟩ := h
  
  -- have H₀ := s.eventually_simulate_dChooseFromSet_subset_taken
  --   (a := a) (ps := s.aPos.nbhd s.pw)
  -- dsimp at h
  -- use N
  -- intro n hn s' h₁
  -- specialize h n hn s' h₁
  -- have hs' := sys.wf_of_simulate_eq h₁
  -- intro h₂
  -- specialize h _ h₂
  -- simp at h
  
  generalize hb : Set'.ofList (s.aPos.nbhd s.pw) = nbhd
  generalize h₀ : dChooseFromSet nbhd = d
  have hd : d.WF; subst h₀; infer_instance
  generalize hf : sys.simulate (Strat.f ⟨a, d⟩) s = F
  
  have hf₁ : ∀ n, ∃ s₁, sys.WF s₁ ∧ F n = (s₁, 0)
  ·
    intro n
    specialize h d hd n
    rw [←hf]
    choose s₁ h₁ h₂ using h
    use s₁, sys.wf_of_simulate_eq h₁
  
  obtain ⟨n, sa, hsa, h₁, h₂⟩ : ∃ n sa, sys.WF sa ∧ F n = (sa, 0) ∧
    sa.aForallWinsDisj (fsp.insertSet 0 nbhd.toSet) a
  ·
    obtain ⟨n, h₁⟩ := s.eventually_simulate_dChooseFromSet_subset_taken
      (a := a) (ps := nbhd)
    specialize h₁ n (by rfl)
    rw [h₀, hf] at h₁
    obtain ⟨s₁, hs₁, h₂⟩ := hf₁ n
    specialize h₁ s₁ h₂
    use n, s₁, hs₁, h₂
    apply State.aForallWinsDisj_insertSet_zero_of
    ·
      rw [←hf] at h₂
      have h₃ := State.aForallWinsDisj_of_simulate_eq h h₂
      exact State.aForallWinsDisj_of_aForallWinsDisj_offset h₃
    
    intro d₁ hd₁ k s₂ h₃
    contrapose! h₁
    simp at h₁
    simp [Set'.subset_def]
    use s₂.aPos, h₁
    apply Set'.not_mem_of_subset (s₂ := s₂.taken)
    ·
      apply taken_subset_of_reachable
      exact sys.reachable_of_simulate_eq h₃
    have hs₂ := sys.wf_of_simulate_eq h₃
    simp
  
  -- simp at H₀
  -- generalize h₀ : dChooseFromSet (Set'.ofList # s.aPos.nbhd s.pw) = d at H₀
  -- have hd : d.WF; subst h₀; infer_instance
  -- generalize hF : sys.simulate (Strat.f ⟨a, d⟩) = F at H₀
  -- rw [eventually_iff_exi_least] at H₀
  -- rcases H₀ with H₀ | H₀
  -- · subst hF
  --   specialize H₀ 0 s rfl s.aPos
  --   simp at H₀
  -- 
  -- push_neg at H₀
  -- obtain ⟨k, ⟨sa, h₁, h₃'⟩, H₂'⟩ := H₀
  
  sorry