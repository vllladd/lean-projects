import AP.AP.FreshA.Fresh1

namespace AP

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
  
  have h₄ : ∃ n sa, AState sa ∧ sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (sa, 0) ∧
    sa.aPos ∈ set ∧ ∀ k s₁, k ≠ 0 → sys.simulate (Strat.f ⟨a, d⟩) sa k = (s₁, 0) → s₁.aPos ∉ set
  ·
    specialize h₁ d
    choose N h₁ h₄ h₅ using h₁
    clear h₅
    simp [←hf] at h₄
    cases N; simp at h₁; nm N
    replace h₄ := AState.of_aPtsSimNcard_eq_succ h₄
    choose n s₁ H₁ H₂ H₃ using h₄
    use n, s₁, AState.of_simulate_mul_two_eq_full H₁, H₁, H₂, H₃
  
  choose n sa hsa h₄ h₅ h₆ using h₄
  
  have h₇ : sa.aHwsDisj # fsp.insertSet 1 set.toSet
  ·
    use a, ha
    intro d₁ hd₁ k
    
    generalize H₁ : DStrat.mk (λ s => some # if s.hist.length < sa.hist.length
      then d.f s else d₁.f s) = d₂
    have hd₂ : d₂.WF; rw [←H₁]; infer_instance
    
    have H₂ : ∀ r, r ≤ n * 2 → sys.simulate (Strat.f ⟨a, d₂⟩) s r =
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
    
    have H₂' : sys.simulate (Strat.f ⟨a, d₂⟩) s (n * 2) = (sa, 0)
    · rw [←h₄]; apply H₂; rfl
    
    have H₃ : sys.simulate (Strat.f ⟨a, d₂⟩) sa = sys.simulate (Strat.f ⟨a, d₁⟩) sa
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
    
    have ha₁ := ha' d₂ hd₂ (n * 2 + k)
    simp [H₂', H₃] at ha₁
    
    choose s₁ H₄ H₅ using ha₁
    use s₁, H₄
    
    replace H₅ : ¬fsp.hasLe k s₁.aPos
    ·
      contrapose! H₅
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
    
    apply iget_aPtsSimNcard_lt_of (n * 2 + k) (State.aWins_of_aWinsDisj # ha' d hd)
      (State.aWins_of_aWinsDisj # ha' d₂ hd₂) (by grind) (by grind)
    
    ·
      intro r S₁ S₂ G₁ G₂ G₃
      
      by_cases hr : r ≤ n * 2
      · grind
      
      push_neg at hr
      contrapose! G₃; clear G₃
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le # le_of_lt hr
      replace hr : r ≠ 0; omega
      simp [h₄] at G₁
      simp; exact h₆ r S₁ hr G₁
    ·
      simp [h₄]
      grind
    ·
      simpa [H₂, h₄, H₃, H₄]
  
  generalize hk : n * 2 = k at h₄
  cases k
  ·
    simp at hk; subst hk
    simp at h₄
    subst h₄
    sorry
  nm k
  
  simp at h₄
  choose sd h₄ H₁ using h₄
  have hsd : sys.WF sd := sys.wf_of_simulate_eq h₄
  replace hsd := DState.of_tr' H₁
  simp at H₁
  replace h₇ : sd.aHwsDisj # fsp.insertSet 2 set.toSet
  ·
    -- use a, ha
    -- have H₂ := State.aForallWinsDisj_of_aForallWinsDisj_offset #
    --   State.aForallWinsDisj_of_simulate_eq ha' h₄
    -- intro d₁ hd₁ n
    -- specialize H₂ d₁ hd₁ n
    -- choose s₁ H₂ H₃ using H₂
    -- use s₁, H₂
    -- simp [FSP.hasLe, FSP.insertSet] at H₃ ⊢
    -- intro r hr
    -- split_ifs with H₄; on_goal 2 => grind
    -- subst H₄
    -- simp
    -- symm; split_ands; grind
    sorry
  
  sorry