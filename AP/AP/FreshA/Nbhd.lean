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
    
    have H₂ : sys.simulate (Strat.f ⟨a, d₂⟩) s (n * 2) = (sa, 0)
    ·
      rw [←h₄]
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
    
    have H₃ : sys.simulate (Strat.f ⟨a, d₂⟩) sa = sys.simulate (Strat.f ⟨a, d₁⟩) sa
    ·
      ext c :1
      apply simulate_congr; simp
      intro r hr
      intro sd hsd H₃ H₄ H₅
      simp [←H₁]
      rw [if_neg]
      rotate_left
      ·
        push_neg
        apply length_hist_le_of_reachable
        exact sys.reachable_of_simulate_eq H₃
      simp
    
    specialize ha' d₂ hd₂ (n * 2 + k)
    simp [H₂, H₃] at ha'
    
    choose s₁ H₄ H₅ using ha'
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
    
    specialize h₁ d₂
    choose N hN H₅ H₆ using h₁
    
    sorry
  
  sorry