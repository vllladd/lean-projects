import AP.AP.FreshA1

namespace AP

class AStrat.Fresh (a : AStrat) (s : State) extends wf : a.WF where
  h₁ : ∀ {d : DStrat} [d.WF] {s₁ s₂ : State} [AState s₁] [AState s₂]
    {k n : ℕ}, k < n → sys.simulate (Strat.f ⟨a, d⟩) s k = (s₁, 0) →
    sys.simulate (Strat.f ⟨a, d⟩) s n = (s₂, 0) →
    sys.hasTr s₂ → s.pw < (a.f s₂).dist s₁.aPos

-- theorem State.wf_erase_taken {s p} [hs : sys.WF s] : ∃ s', sys.WF s' ∧
-- s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧ s'.taken = s.taken.erase p := by
--   by_cases h₁ : p ∉ s.taken
--   · use s; simp [hs, Set'.erase_eq_of_not_mem h₁]
--   simp at h₁
--   sorry

-- #check 0 #exit

theorem State.aHws_disjoint_of_taken_subset {s s' k} {set : Set PointZ}
[hs : sys.WF s] [hs' : sys.WF s'] (hpw : s'.pw = s.pw)
(h₂ : s'.aTurn = s.aTurn) (h₃ : s'.aPos = s.aPos) (h₄ : s'.taken ⊆ s.taken)
(h₁ : ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁,
sys.simulate (Strat.f ⟨a, d⟩) s (k + n) = (s₁, 0) ∧ s₁.aPos ∉ set) :
∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁,
sys.simulate (Strat.f ⟨a, d⟩) s' (k + n) = (s₁, 0) ∧ s₁.aPos ∉ set := by
  sorry

-- #check 0 #exit

  -- have H := aHws_of_ind' (p := λ s₂ => ∃ (s₁ : State), sys.Reachable s s₁ ∧
  --   (∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s₁.aWins ⟨a, d⟩ ∧
  --   ∀ n, sys.simulate (Strat.f ⟨a, d⟩) s₁ (n + 1) |>.1.aPos ∉ set) ∧
  --   s₁.aTurn = s₂.aTurn ∧ s₁.aPos = s₂.aPos ∧ s₂.taken ⊆ s₁.taken) (by use s)
  -- specialize H _ _; rotate_right
  -- · dsimp only at H
  --   replace H := H.2
  --   obtain ⟨s₁, H₁, ⟨a, Ha, H₂⟩, H₃⟩ := H
  --   use a, Ha
  --   intro d Hd
  --   specialize H₂ d Hd
  --   obtain ⟨H₂, H₄⟩ := H₂
  --   sorry
  -- all_goals clear h₁
  -- · rintro sa' hsa' H₁ ⟨sa, hr, ⟨a, Ha, Hx⟩, ht, ha, H₃⟩
  --   simp at ht; have hsa : AState sa; use sys.wf_of_reachable hr
  --   obtain ⟨sd, H₂⟩ : sys.validTr sa (a.f sa)
  --   · specialize Hx default inferInstance
  --     apply a.validTr # hsa.hasTr_of_aWins Hx.1
  --   use a.f sa
  --   obtain ⟨sd', H₆⟩ : ∃ sd', sys.tr sa' (a.f sa) = some sd'
  --   · simp at H₂ ⊢
  --     rcases H₂ with ⟨⟨H₅, H₆, H₇⟩, rfl⟩
  --     rw [pw_eq_of_reachable hr] at H₇
  --     simp [←ha, H₅, pw_eq_of_reachable H₁, ←hpw, H₇]
  --     contrapose! H₆; exact H₃ _ H₆
  --   use sd', H₆, sd, sys.reachable_right hr H₂
  --   refine ⟨?_, ?_, ?_, ?_⟩; rotate_left
  --   · simp [aTurn_eq_of_tr H₂, aTurn_eq_of_tr H₆]
  --   · rw [AState.aPos_eq_of_tr H₂, AState.aPos_eq_of_tr H₆]
  --   · rwa [AState.taken_eq_of_tr H₂, AState.taken_eq_of_tr H₆]
  --   use a, Ha
  --   intro d Hd
  --   specialize Hx d Hd
  --   rcases Hx with ⟨G₁, G₂⟩
  --   constructor
  --   · intro n; specialize G₁ (n + 1); simp [H₂] at G₁; exact G₁
  --   intro n; specialize G₂ (n + 1); simp [H₂] at G₂ ⊢; exact G₂
  -- · rintro sd' hsd' p sa' H₁ ⟨sd, hr, ⟨a, Ha, Hx⟩, ht, ha, H₃⟩ H₄
  --   simp at ht; have hsd : DState sd; use sys.wf_of_reachable hr
  --   have H₂ : ∀ p sa, sys.tr sd p = some sa → ∀ (d : DStrat), d.WF → sa.aWins ⟨a, d⟩
  --   · intro p₁ sa H₅ d Hd n
  --     have hsa := AState.of_tr H₅
  --     specialize Hx (d.set sd p₁) # d.wf_set_of_tr H₅
  --     replace Hx := Hx.1 (n + 1)
  --     simp [H₅] at Hx
  --     convert Hx using 2
  --     symm
  --     apply simulate_set_d_eq_of_length_hist_lt ⟨_, H₅⟩
  --     exact length_hist_lt_of_tr H₅
  --   have hsa' := AState.of_tr H₄
  --   by_cases hp : p ∉ sd.taken
  --   · specialize H₂ p
  --     simp at H₂
  --     have H₅ : sd.aPos ≠ p
  --     · rintro rfl; simp [ha] at H₄
  --     specialize H₂ H₅ hp
  --     generalize G₁ : (
  --       { pw := sd.pw, taken := sd.taken.insert p, aPos := sd.aPos,
  --         aTurn := true, hist := p :: sd.hist } : State) = sa at H₂
  --     use sa
  --     have G₀ : sys.tr sd p = some sa
  --     · simp_all only [System.simulate, DState.strat_f_eq, DState.tr_eq_some_iff,
  --         ne_eq, DState.turn', not_false_eq_true, and_self]
  --     have Ga := AState.of_tr G₀
  --     refine' ⟨?_, ?_, by simp [←G₁], ?_, ?_⟩
  --     · subst G₁; apply sys.reachable_right (t := p) hr; simp [H₅, hp]
  --     · use a, Ha
  --       intro d Hd
  --       use H₂ d Hd
  --       specialize Hx (d.set sd p) # d.wf_set_of_tr G₀
  --       replace Hx := Hx.2
  --       intro n
  --       specialize Hx (n + 1)
  --       generalize n + 1 = m at Hx ⊢
  --       simp [G₀] at Hx
  --       convert Hx using 4
  --       symm
  --       apply simulate_set_d_eq_of_length_hist_lt ⟨_, G₀⟩
  --       exact length_hist_lt_of_tr G₀
  --     · subst G₁; simpa [DState.aPos_eq_of_tr H₄]
  --     · subst G₁; intro p₁
  --       rw [DState.taken_eq_of_tr H₄]
  --       simp
  --       rintro (rfl | H₆)
  --       · simp
  --       right
  --       exact H₃ p₁ H₆
  --   simp at hp
  --   specialize H₂ sd.chooseDMove
  --   simp at H₂
  --   generalize G : (
  --     { pw := sd.pw, taken := sd.taken.insert sd.chooseDMove, aPos := sd.aPos,
  --       aTurn := true, hist := sd.chooseDMove :: sd.hist } : State) = sa at H₂
  --   have G₀ : sys.tr sd sd.chooseDMove = some sa; simp [←G]
  --   have Ga := AState.of_tr G₀
  --   use sa
  --   refine' ⟨?_, ?_, by simp [←G], ?_, ?_⟩
  --   · subst G; apply sys.reachable_right (t := sd.chooseDMove) hr; simp
  --   · use a, Ha
  --     intro d Hd
  --     use H₂ d Hd
  --     intro n
  --     specialize Hx (d.set sd sd.chooseDMove) # d.wf_set_of_tr G₀
  --     replace Hx := Hx.2 (n + 1)
  --     generalize n + 1 = m at Hx ⊢
  --     simp [G₀] at Hx
  --     convert Hx using 4
  --     symm
  --     apply simulate_set_d_eq_of_length_hist_lt ⟨_, G₀⟩
  --     exact length_hist_lt_of_tr G₀
  --   · simpa [←G, DState.aPos_eq_of_tr H₄]
  --   · simp [←G]
  --     intro p₁
  --     rw [DState.taken_eq_of_tr H₄]
  --     simp
  --     rintro (rfl | H₆) <;> right
  --     · exact hp
  --     exact H₃ p₁ H₆

-- #check 0 #exit

theorem State.aHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.aHws) (hpw : s'.pw = s.pw) (h₂ : s'.aTurn = s.aTurn) (h₃ : s'.aPos = s.aPos)
(h₄ : s'.taken ⊆ s.taken) : s'.aHws := by
  have H := @aHws_disjoint_of_taken_subset
  specialize @H s s' 0 ∅ _ _ hpw h₂ h₃ h₄ _
  · obtain ⟨a, Ha, h₁⟩ := h₁; use a, Ha; simp
    intro d Hd n; specialize h₁ d Hd n; simpa [Prod.ext_iff]
  obtain ⟨a, Ha, H⟩ := H; use a, Ha; intro d Hd n
  specialize H d Hd n; simp [Prod.ext_iff] at H; exact H

-- #check 0 #exit

theorem State.dHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.dHws) (hpw : s'.pw = s.pw) (h₂ : s'.aTurn = s.aTurn) (h₃ : s'.aPos = s.aPos)
(h₄ : s.taken ⊆ s'.taken) : s'.dHws := by
  contrapose h₁; simp at h₁ ⊢; symm at hpw h₂ h₃
  exact s'.aHws_of_taken_subset h₁ hpw h₂ h₃ h₄

theorem State.bounded_reenter_nbhd_pw_of_forall_aWins {s} {a : AStrat}
[hs : sys.WF s] [Ha : a.WF] (h : ∀ (d : DStrat) [d.WF], s.aWins ⟨a, d⟩) :
∃ (n : ℕ), ∀ (d : DStrat) [d.WF] (set : Set ℕ), {k | ∃ sa, AState sa ∧
sys.simulate (Strat.f ⟨a, d⟩) s k = (sa, 0) ∧ s.pw ≤ sa.aPos.dist s.aPos} = set →
set.Finite ∧ set.ncard ≤ n := by
  contrapose! h; simp
  sorry