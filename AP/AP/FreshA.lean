import AP.AP.King

namespace AP

class AStrat.Fresh (a : AStrat) (s : State) extends wf : a.WF where
  h₁ : ∀ {d : DStrat} [d.WF] {s₁ s₂ : State} [AState s₁] [AState s₂]
    {k n : ℕ}, k < n → sys.simulate (Strat.f ⟨a, d⟩) s k = (s₁, 0) →
    sys.simulate (Strat.f ⟨a, d⟩) s n = (s₂, 0) →
    sys.hasTr s₂ → s.pw < (a.f s₂).dist s₁.aPos

-- open Classical in noncomputable
-- def aFresh : AStrat :=
--   .mk # λ s => choose? # λ p => ∃ s', sys.tr s p = some s' ∧
--   s'.aHws ∧ ∀ p₁ s₁, sys.tr s p₁ = some s₁ → s₁.aHws → s'.taken ⊆ s₁.taken

theorem State.aHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
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

#check 0 #exit

instance : aFresh.WF := by unfold aFresh; infer_instance

-- #check 0 #exit

theorem exi_tr_aHws_min_taken_of_aHws {s} [hs : sys.WF s] (h : s.aHws) :
∃ p s', sys.tr s p = some s' ∧ s'.aHws ∧ ∀ p₁ s₁,
sys.tr s p₁ = some s₁ → s₁.aHws → s'.taken ⊆ s₁.taken := by
  sorry

-- #check 0 #exit

theorem aFresh_cnd_of_aHws {s} [hs : sys.WF s] (h : s.aHws) :
∃ s', sys.tr s (aFresh.f s) = some s' ∧ s'.aHws ∧ ∀ p₁ s₁,
sys.tr s p₁ = some s₁ → s₁.aHws → s'.taken ⊆ s₁.taken := by
  have h₃ := exi_tr_aHws_min_taken_of_aHws h
  have h₄ := Classical.epsilon_spec h₃
  generalize hp : (Classical.epsilon # λ p => ∃ s', sys.tr s p = some s' ∧ s'.aHws ∧
    ∀ p₁ s₁, sys.tr s p₁ = some s₁ → s₁.aHws → s'.taken ⊆ s₁.taken) = p at h₄
  obtain ⟨s₁, h₄, h₅, h₆⟩ := h₄
  simpa [-AState.tr_eq_some_iff, aFresh, choose?_eq_ite, h₃, hp,
    sys.validTr_of_eq_some h₄, h₄, h₅]

theorem aFresh_cnd_of_aHws_and_tr {s s'} [hs : sys.WF s] (h₁ : s.aHws)
(h₂ : sys.tr s (aFresh.f s) = some s') : s'.aHws ∧ ∀ p₁ s₁,
sys.tr s p₁ = some s₁ → s₁.aHws → s'.taken ⊆ s₁.taken := by
  obtain ⟨s₁, h₃, h₄⟩ := aFresh_cnd_of_aHws h₁
  simp [h₂] at h₃; subst h₃; exact h₄

theorem aHws_of_tr_aFresh {s s'} [hs : sys.WF s]
(h₁ : s.aHws) (h₂ : sys.tr s (aFresh.f s) = some s') : s'.aHws :=
  aFresh_cnd_of_aHws_and_tr h₁ h₂ |>.1

theorem aHws_of_simulate_aFresh {s} [hs : sys.WF s] {d : DStrat} {n}
(h : s.aHws) : sys.simulate (Strat.f ⟨aFresh, d⟩) s n |>.1.aHws := by
  induction n generalizing s; exact h
  nm n ih; simp; split; exact h; nm x s' h₁
  clear x; replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · have hs' := DState.of_tr h₁; apply ih
    simp [-AState.tr_eq_some_iff] at h₁
    exact aHws_of_tr_aFresh h h₁
  · have hs' := AState.of_tr h₁
    apply ih; exact DState.aHws_of_tr h₁ h

theorem aHws_of_simulate_aFresh_eq {s r} [hs : sys.WF s] {d : DStrat} {n}
(h₁ : s.aHws) (h₂ : sys.simulate (Strat.f ⟨aFresh, d⟩) s n = r) : r.1.aHws := by
  subst h₂; exact aHws_of_simulate_aFresh h₁

-- #check 0 #exit

theorem fresh_aFresh_of_aHws {s} [hs : sys.WF s]
(h : s.aHws) : aFresh.Fresh s := by
  constructor
  intro d hd s₁ s₂ hs₁ hs₂ k n hk h₁ h₂ h₃
  by_contra! h₄
  apply aFresh.validTr at h₃
  obtain ⟨s₃, h₃⟩ := h₃
  have H₁ := aHws_of_simulate_aFresh_eq h h₁
  have H₂ := aHws_of_simulate_aFresh_eq h h₂
  dsimp at H₁ H₂
  obtain ⟨H₃, H₄⟩ := aFresh_cnd_of_aHws_and_tr H₂ h₃
  by_cases h₅ : aFresh.f s₂ = s₁.aPos
  · sorry
  sorry