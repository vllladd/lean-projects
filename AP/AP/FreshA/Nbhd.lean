import AP.AP.FreshA.Fresh1

namespace AP

theorem AState.aHwsDisj_of_tr {s s₁ p fsp} [hs : AState s] (h₁ : s₁.aHwsDisj fsp.next)
(h₂ : sys.tr s p = some s₁) (h₃ : s.aPos ∉ fsp.get 0) : s.aHwsDisj fsp := by
  have hs₁ := DState.of_tr h₂
  choose a ha h₁ using h₁
  use a.set s p, AStrat.wf_set_of_tr h₂
  intro d hd n
  cases n; simpa; nm n
  specialize h₁ d hd n
  choose s₂ h₁ h₄ using h₁
  use s₂
  rw [sys.simulate_succ_full']
  simp [h₂]
  symm; split_ands
  · rw [FSP.hasLe_next] at h₄; exact h₄
  rw [←h₁]
  apply State.simulate_set_a_eq_of_length_hist_lt ⟨_, h₂⟩
  simp [length_hist_eq_of_tr h₂]

-- #check 0 #exit

theorem AState.aHwsDisj_nbhd_pw {s : State} {fsp : FSP} [hs : AState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insertSet 3 # s.aPos.nbhd s.pw |>.toSet := by
  generalize hb : Set'.ofList (s.aPos.nbhd s.pw) = set
  replace h := exi_fresh1_of_aHwsDisj h
  choose a ha using h
  
  have h : (s.aPos.nbhd s.pw).toSet = set.toSet
  · simp [←hb]
  rw [h]; clear h
  
  have h₁ := State.aPtsSimNcard_spec_of_fresh1 ha set
  
  generalize hf : (λ d => s.aPtsSimNcard ⟨a, d⟩ set.toSet) = f
  replace h₁ : ∀ (d : DStrat) [d.WF], ∃ n, f d = some n ∧ n ≤ set.size; grind
  
  generalize hg : (λ d => f d |>.iget) = g
  have h₂ : ∀ (d : DStrat) [d.WF], g d ≤ set.size; grind
  
  have h₃ : ∃ (d : DStrat), d.WF ∧ ∀ (d₁ : DStrat) [d₁.WF], g d₁ ≤ g d
  ·
    generalize set.size = N at h₂
    induction N
    ·
      simp at h₂
      use default, inferInstance
      intro d₁ hd₁
      simp [h₂]
    nm N ih
    by_cases h₃ : ∃ (d : DStrat), d.WF ∧ g d = N + 1
    ·
      choose d hd h₃ using h₃
      use d, hd
      intro d₁ hd₁
      grind
    apply ih; grind
  
  choose d hd h₃ using h₃
  clear h₂
  
  replace h₁ : ∀ (d₁ : DStrat) [d₁.WF], ∃ n, n ≠ 0 ∧ f d₁ = some n ∧ n ≤ g d
  ·
    intro d₁ hd₁
    specialize h₁ d₁
    choose n h₁ h₄ using h₁
    use n; simp [h₁]
    symm; split_ands; grind
    rintro rfl
    simp [←hf] at h₁
    have h₅ := State.aWins_of_aWinsDisj (ha.2.1 d₁ hd₁) 1
    simp at h₅
    choose s₁ h₅ using h₅
    specialize h₁ 0 s s₁
    simp at h₁
    specialize h₁ h₅
    apply h₁; clear h₁
    simp [←hb]
    rw [Point.dist_comm]
    rw [AState.tr_eq_some_iff] at h₅
    grind
  
  rcases ha with ⟨ha, ha', -⟩
  
  have h₄ : ∃ n sd, DState sd ∧ sys.simulate (Strat.f ⟨a, d⟩) s (n * 2 + 1) = (sd, 0) ∧
    sd.aPos ∈ set ∧ ∀ k s₁, 2 ≤ k → sys.simulate (Strat.f ⟨a, d⟩) sd k = (s₁, 0) → s₁.aPos ∉ set
  ·
    specialize h₁ d
    choose N h₁ h₄ h₅ using h₁
    clear h₅
    simp [←hf] at h₄
    cases N; simp at h₁; nm N
    replace h₄ := AState.exi_dState_of_aPtsSimNcard_eq_succ h₄
    choose n s₁ H₁ H₂ H₃ using h₄
    have hs₁ := DState.of_simulate_mul_two_add_one_eq_full H₁
    use n, s₁, hs₁, H₁, H₂, H₃
  
  choose n sd hsd h₄ h₅ h₆ using h₄
  
  have h₇ : sd.aHwsDisj # fsp.next.insertSet 2 set.toSet
  ·
    use a, ha
    intro d₁ hd₁ k
    
    generalize H₁ : DStrat.mk (λ s => some # if s.hist.length < sd.hist.length
      then d.f s else d₁.f s) = d₂
    have hd₂ : d₂.WF; rw [←H₁]; infer_instance
    
    have H₂ : ∀ r, r ≤ n * 2 + 1 → sys.simulate (Strat.f ⟨a, d₂⟩) s r =
      sys.simulate (Strat.f ⟨a, d⟩) s r
    ·
      intro r hr
      apply simulate_congr; simp
      intro r hr sd hsd H₂ H₃ H₄
      simp [←H₁]
      rw [if_pos]
      rotate_left
      ·
        rw [State.length_hist_eq_of_simulate_eq H₂]
        rw [State.length_hist_eq_of_simulate_eq h₄]
        omega
      simp
    
    have H₂' : sys.simulate (Strat.f ⟨a, d₂⟩) s (n * 2 + 1) = (sd, 0)
    · rw [←h₄]; apply H₂; rfl
    
    have H₃ : sys.simulate (Strat.f ⟨a, d₂⟩) sd = sys.simulate (Strat.f ⟨a, d₁⟩) sd
    ·
      ext c :1
      apply simulate_congr; simp
      intro r hr sd hsd H₃ H₄ H₅
      simp [←H₁]
      rw [if_neg]
      rotate_left
      ·
        push_neg
        apply length_hist_le_of_reachable
        exact sys.reachable_of_simulate_eq H₃
      simp
    
    have ha₁ := ha' d₂ hd₂ (n * 2 + 1 + k)
    simp [H₂', H₃] at ha₁
    
    choose s₁ H₄ H₅ using ha₁
    use s₁, H₄
    
    replace H₅ : ¬fsp.next.hasLe k s₁.aPos
    ·
      contrapose! H₅
      rw [FSP.hasLe_next] at H₅
      apply FSP.hasLe_of_le H₅
      omega
    
    simp [FSP.hasLe, FSP.insertSet] at H₅ ⊢
    intro r hr
    specialize H₅ r hr
    split_ifs with H₆
    on_goal 2 => exact H₅
    subst H₆
    
    simp [H₅]; clear H₅
    
    -----
    
    rename' hr => hk
    
    specialize h₃ d₂
    contrapose! h₃
    simp [←hg, ←hf]
    
    apply iget_aPtsSimNcard_lt_of (n * 2 + 1 + k) (State.aWins_of_aWinsDisj # ha' d hd)
      (State.aWins_of_aWinsDisj # ha' d₂ hd₂) (by grind) (by grind)
    ·
      intro r S₁ S₂ G₁ G₂ G₃
      simp at G₃ ⊢
      
      by_cases hr : r ≤ n * 2 + 1
      ·
        grind
      
      push_neg at hr
      contrapose! G₃; clear G₃
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt # le_of_lt hr
      replace hr : r ≠ 0; omega
      
      by_cases hr' : r = 1
      ·
        clear hr
        subst hr'
        clear! G₂
        rw [sys.simulate_succ_full, ←H₂ _ # by rfl, H₂'] at G₁
        simp at G₁
        
        -- specialize H₂ _ (by rfl)
        -- rw [H₂'] at H₂
        
        sorry
      
      replace hr : 2 ≤ r
      · omega
      clear hr'
      
      apply h₆ _ _ hr
      
      rw [←Nat.add_one_add] at G₁
      rw [sys.simulate_add_full, ←H₂ _ # by rfl, H₂'] at G₁
      simp at G₁
      exact G₁
    ·
      intro S₃
      rw [sys.simulate_add_full]
      specialize H₂ (n * 2 + 1) (by omega)
      rw [←H₂, H₂']
      simp
      intro G₁
      grind
    ·
      simpa [H₂, h₄, H₃, H₄]
  
  generalize hk : n * 2 + 1 = k at h₄
  
  -- simp at h₄
  -- choose sd h₄ H₁ using h₄
  -- have hsd : sys.WF sd := sys.wf_of_simulate_eq h₄
  -- replace hsd := DState.of_tr' H₁
  -- simp at H₁
  -- replace h₇ : sd.aHwsDisj # fsp.insertSet 2 set.toSet
  -- ·
  --   -- use a, ha
  --   -- have H₂ := State.aForallWinsDisj_of_aForallWinsDisj_offset #
  --   --   State.aForallWinsDisj_of_simulate_eq ha' h₄
  --   -- intro d₁ hd₁ n
  --   -- specialize H₂ d₁ hd₁ n
  --   -- choose s₁ H₂ H₃ using H₂
  --   -- use s₁, H₂
  --   -- simp [FSP.hasLe, FSP.insertSet] at H₃ ⊢
  --   -- intro r hr
  --   -- split_ifs with H₄; on_goal 2 => grind
  --   -- subst H₄
  --   -- simp
  --   -- symm; split_ands; grind
  --   sorry
  
  have H₂ := sys.reachable_of_simulate_eq h₄
  have H₃ := taken_subset_of_reachable H₂
  
  replace h₆ : ∀ k, 2 ≤ k → ∃ s₁, sys.simulate (Strat.f ⟨a, d⟩) sd k = (s₁, 0) ∧ s₁.aPos ∉ set
  ·
    have h₆' : ∀ k, ∃ s₁, sys.simulate (Strat.f ⟨a, d⟩) sd k = (s₁, 0)
    ·
      intro r
      specialize ha' d hd (k + r)
      choose S h₈ h₉ using ha'
      simp [h₄] at h₈
      simp [h₈]
    intro r hr
    specialize h₆' r
    choose S h₆' using h₆'
    use S, h₆'
    exact h₆ r S hr h₆'
  
  obtain ⟨sd₀, H₁⟩ : sys.validTr s sd.aPos
  ·
    simp [AState.validTr_iff]
    split_ands
    ·
      specialize h₆ 2 (by omega)
      choose S h₆ H₄ using h₆
      have hS := DState.of_simulate_mul_two_eq_full (n := 1) h₆
      simp at h₆
      choose S' h₆ H₅ using h₆
      have hS' := AState.of_tr h₆
      simp at H₅
      simp [←hb] at H₄
      rw [AState.aPos_eq_of_tr H₅] at H₄
      contrapose! H₄
      rw [←DState.aPos_eq_of_tr h₆] at H₄
      rw [AState.tr_eq_some_iff] at H₅
      rw [Point.dist_comm, H₄]
      replace H₅ := H₅.1.2.2
      rw [pw_eq_of_tr h₆, pw_eq_of_reachable H₂] at H₅
      exact H₅
    · apply Set'.not_mem_of_subset (s₂ := sd.taken) H₃; simp
    · simp [←hb] at h₅; rwa [Point.dist_comm]
  
  have hsd₀ := DState.of_tr H₁
  replace h₇ : sd₀.aHwsDisj # fsp.next.insertSet 2 set.toSet
  · apply State.aHwsDisj_of_taken_subset' h₇
    · rw [pw_eq_of_tr H₁, pw_eq_of_reachable H₂]
    · simp
    · rw [aPos_eq_of_tr H₁]
    · rwa [AState.taken_eq_of_tr H₁]
  
  apply aHwsDisj_of_tr _ H₁
  · simp; exact State.aPos_not_mem_fsp_get_zero_of_aForallWinsDisj ha'
  
  rwa [FSP.next_insertSet_succ]