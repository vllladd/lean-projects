import AP.AP.King

namespace AP

theorem State._aux_ {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.aHws) (hpw : s.pw = s'.pw) (h₂ : s.aTurn = s'.aTurn) (h₃ : s.aPos = s'.aPos)
(h₄ : s'.taken ⊆ s.taken) : s'.aHws := by
  apply aHws_of_ind (p := λ s₂ => ∃ (s₁ : State), sys.Reachable s s₁ ∧ s₁.aHws ∧
    s₁.aTurn = s₂.aTurn ∧ s₁.aPos = s₂.aPos ∧ s₂.taken ⊆ s₁.taken) (by use s)
  · rintro sa' hsa' H₁ ⟨sa, hr, H₂, ht, ha, H₃⟩
    simp at ht; have hsa : AState sa; use sys.wf_of_reachable hr
    rw [AState.aHws_iff_tr] at H₂
    obtain ⟨p, sd, H₂, H₄⟩ := H₂
    use p
    obtain ⟨sd', H₆⟩ : ∃ sd', sys.tr sa' p = some sd'
    · simp at H₂ ⊢
      rcases H₂ with ⟨⟨H₅, H₆, H₇⟩, rfl⟩
      rw [pw_eq_of_reachable hr] at H₇
      simp [←ha, H₅, pw_eq_of_reachable H₁, ←hpw, H₇]
      contrapose! H₆; exact H₃ p H₆
    use sd', H₆, sd, sys.reachable_right hr H₂, H₄
    refine ⟨?_, ?_, ?_⟩
    · simp [aTurn_eq_of_tr H₂, aTurn_eq_of_tr H₆]
    · rw [AState.aPos_eq_of_tr H₂, AState.aPos_eq_of_tr H₆]
    · rwa [AState.taken_eq_of_tr H₂, AState.taken_eq_of_tr H₆]
  · rintro sd' hsd' p sa' H₁ ⟨sd, hr, H₂, ht, ha, H₃⟩ H₄
    simp at ht; have hsd : DState sd; use sys.wf_of_reachable hr
    rw [DState.aHws_iff_tr] at H₂
    have hsa' := AState.of_tr H₄
    by_cases hp : p ∉ sd.taken
    · specialize H₂ p
      simp at H₂
      have H₅ : sd.aPos ≠ p
      · rintro rfl; simp [ha] at H₄
      specialize H₂ H₅ hp
      refine' ⟨?_, ?_, H₂, by simp, ?_, ?_⟩
      · apply sys.reachable_right (t := p) hr
        simp [H₅, hp]
      · simpa [DState.aPos_eq_of_tr H₄]
      · simp
        intro p₁
        rw [DState.taken_eq_of_tr H₄]
        simp
        rintro (rfl | H₆)
        · simp
        right
        exact H₃ p₁ H₆
    simp at hp
    specialize H₂ sd.chooseDMove
    simp at H₂
    refine' ⟨?_, ?_, H₂, by simp, ?_, ?_⟩
    · apply sys.reachable_right (t := sd.chooseDMove) hr; simp
    · simpa [DState.aPos_eq_of_tr H₄]
    · simp
      intro p₁
      rw [DState.taken_eq_of_tr H₄]
      simp
      rintro (rfl | H₆) <;> right
      · exact hp
      exact H₃ p₁ H₆

-- #check 0 #exit

theorem State.aHws_disjoint_of_taken_subset {s s'} {set : Set' PointZ}
[hs : sys.WF s] [hs' : sys.WF s'] (hpw : s.pw = s'.pw)
(h₂ : s.aTurn = s'.aTurn) (h₃ : s.aPos = s'.aPos) (h₄ : s'.taken ⊆ s.taken)
(h₁ : ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s.aWins ⟨a, d⟩ ∧
∀ n, sys.simulate (Strat.f ⟨a, d⟩) s (n + 1) |>.1.aPos ∉ set) : s'.aHws := by
  apply aHws_of_ind (p := λ s₂ => ∃ (s₁ : State), sys.Reachable s s₁ ∧
    (∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s₁.aWins ⟨a, d⟩ ∧
    ∀ n, sys.simulate (Strat.f ⟨a, d⟩) s₁ (n + 1) |>.1.aPos ∉ set) ∧
    s₁.aTurn = s₂.aTurn ∧ s₁.aPos = s₂.aPos ∧ s₂.taken ⊆ s₁.taken) (by use s)
  all_goals clear h₁
  · rintro sa' hsa' H₁ ⟨sa, hr, ⟨a, Ha, Hx⟩, ht, ha, H₃⟩
    simp at ht; have hsa : AState sa; use sys.wf_of_reachable hr
    obtain ⟨sd, H₂⟩ : sys.validTr sa (a.f sa)
    · specialize Hx default inferInstance
      apply a.validTr # hsa.hasTr_of_aWins Hx.1
    use a.f sa
    obtain ⟨sd', H₆⟩ : ∃ sd', sys.tr sa' (a.f sa) = some sd'
    · simp at H₂ ⊢
      rcases H₂ with ⟨⟨H₅, H₆, H₇⟩, rfl⟩
      rw [pw_eq_of_reachable hr] at H₇
      simp [←ha, H₅, pw_eq_of_reachable H₁, ←hpw, H₇]
      contrapose! H₆; exact H₃ _ H₆
    use sd', H₆, sd, sys.reachable_right hr H₂
    refine ⟨?_, ?_, ?_, ?_⟩; rotate_left
    · simp [aTurn_eq_of_tr H₂, aTurn_eq_of_tr H₆]
    · rw [AState.aPos_eq_of_tr H₂, AState.aPos_eq_of_tr H₆]
    · rwa [AState.taken_eq_of_tr H₂, AState.taken_eq_of_tr H₆]
    use a, Ha
    intro d Hd
    specialize Hx d Hd
    rcases Hx with ⟨G₁, G₂⟩
    constructor
    · intro n; specialize G₁ (n + 1); simp [H₂] at G₁; exact G₁
    intro n; specialize G₂ (n + 1); simp [H₂] at G₂ ⊢; exact G₂
  · rintro sd' hsd' p sa' H₁ ⟨sd, hr, ⟨a, Ha, Hx⟩, ht, ha, H₃⟩ H₄
    simp at ht; have hsd : DState sd; use sys.wf_of_reachable hr
    have H₂ : ∀ p sa, sys.tr sd p = some sa → ∀ (d : DStrat), d.WF → sa.aWins ⟨a, d⟩
    · sorry
    have hsa' := AState.of_tr H₄
    by_cases hp : p ∉ sd.taken
    · specialize H₂ p
      simp at H₂
      have H₅ : sd.aPos ≠ p
      · rintro rfl; simp [ha] at H₄
      specialize H₂ H₅ hp
      generalize G₁ : (
        { pw := sd.pw, taken := sd.taken.insert p, aPos := sd.aPos,
          aTurn := true, hist := p :: sd.hist } : State) = sa at H₂
      use sa
      refine' ⟨?_, ?_, by simp [←G₁], ?_, ?_⟩
      · subst G₁; apply sys.reachable_right (t := p) hr; simp [H₅, hp]
      · use a, Ha
        intro d Hd
        use H₂ d Hd
        specialize Hx d Hd
        replace Hx := Hx.2
        intro n
        specialize Hx (n + 1)
        simp at Hx ⊢
        sorry
      · subst G₁; simpa [DState.aPos_eq_of_tr H₄]
      · subst G₁; intro p₁
        rw [DState.taken_eq_of_tr H₄]
        simp
        rintro (rfl | H₆)
        · simp
        right
        exact H₃ p₁ H₆
    simp at hp
    specialize H₂ sd.chooseDMove
    simp at H₂
    use
      { pw := sd.pw, taken := sd.taken.insert sd.chooseDMove,
        aPos := sd.aPos, aTurn := true, hist := sd.chooseDMove :: sd.hist }
    refine' ⟨?_, ?_, by simp, ?_, ?_⟩
    · apply sys.reachable_right (t := sd.chooseDMove) hr; simp
    · sorry
    · simpa [DState.aPos_eq_of_tr H₄]
    · simp
      intro p₁
      rw [DState.taken_eq_of_tr H₄]
      simp
      rintro (rfl | H₆) <;> right
      · exact hp
      exact H₃ p₁ H₆

-- #check 0 #exit

theorem State.aHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.aHws) (hpw : s.pw = s'.pw) (h₂ : s.aTurn = s'.aTurn) (h₃ : s.aPos = s'.aPos)
(h₄ : s'.taken ⊆ s.taken) : s'.aHws := by
  apply @aHws_disjoint_of_taken_subset s s' ∅ _ _ hpw h₂ h₃ h₄
  obtain ⟨a, Ha, h₁⟩ := h₁; use a, Ha; simpa

-- #check 0 #exit

class AStrat.Fresh (a : AStrat) (s : State) extends wf : a.WF where
  h₁ : ∀ {d : DStrat} [d.WF] {s₁ s₂ : State} [AState s₁] [AState s₂]
    {k n : ℕ}, k < n → sys.simulate (Strat.f ⟨a, d⟩) s k = (s₁, 0) →
    sys.simulate (Strat.f ⟨a, d⟩) s n = (s₂, 0) →
    sys.hasTr s₂ → s.pw < (a.f s₂).dist s₁.aPos