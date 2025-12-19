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
  
  replace h₁ : ∀ (d : DStrat) [d.WF], ∃ n, n ≠ 0 ∧ f d = some n ∧ n ≤ g d
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
  
  have h₄ : ∃ n s₁, AState s₁ ∧ sys.simulate (Strat.f ⟨a, d⟩) s n = (s₁, 0) ∧
    s₁.aPos ∈ set ∧ ∀ k s₂, sys.simulate (Strat.f ⟨a, d⟩) s₁ k = (s₂, 0) → s₁.aPos ∉ set
  ·
    specialize h₁ d
    choose N h₁ h₄ h₅ using h₁
    clear h₅
    simp [←hf] at h₄
    sorry
  
  sorry