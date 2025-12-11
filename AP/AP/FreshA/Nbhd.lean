import AP.AP.FreshA.Tile

namespace AP

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