import AP.AP.FSP

namespace AP

structure WFCnd (s : State) : Prop where
  aPos_not_mem_taken : s.aPos ∉ s.taken
  taken_ne_empty_of_aTurn : s.aTurn → s.taken ≠ ∅
  size_taken_eq_one_of_aTurn_and_pw_eq_zero : s.aTurn → s.pw = 0 → s.taken.size = 1
  exi_aMove_of_not_aTurn_and_taken_ne_empty : s.aTurn = false → s.taken ≠ ∅ →
    ∃ p, s.aMove p |>.isSome

theorem State.wfCnd_of_wf {s} [hs : sys.WF s] : WFCnd s where
  aPos_not_mem_taken := by simp
  taken_ne_empty_of_aTurn ht := AState.mk hs ht |>.taken_ne_empty
  size_taken_eq_one_of_aTurn_and_pw_eq_zero ht h :=
    AState.mk hs ht |>.size_taken_eq_one_of_pw_eq_zero h
  exi_aMove_of_not_aTurn_and_taken_ne_empty ht h :=
    DState.mk hs ht |>.exi_aMove_of_taken_ne_empty h

theorem WFCnd.pw_ne_zero_of_not_aTurn_and_taken_ne_empty {s} (h : WFCnd s)
(ht : s.aTurn = false) (h₁ : s.taken ≠ ∅) : s.pw ≠ 0 := by
  intro hpw; obtain ⟨p, hp⟩ := h.exi_aMove_of_not_aTurn_and_taken_ne_empty ht h₁
  simp [State.isSome_aMove_iff, hpw] at hp; tauto

theorem State.exi_hist_wf_of_not_aTurn_and_taken_eq_empty {s : State}
(ht : s.aTurn = false) (h₁ : s.taken = ∅) : ∃ hist, sys.WF # s.setHist hist := by
  use [s.aPos]
  rw [wf_iff]
  use []
  simp
  rw [Option.iget]
  ext:1 <;> simp [ht, h₁]

-- #check 0 #exit

theorem State.exi_hist_wf_of_wfCnd_and_not_aTurn {s} (h : WFCnd s)
(ht : s.aTurn = false) : ∃ hist, sys.WF # s.setHist hist := by
  classical
  by_cases h₂ : s.taken = ∅
  · exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty ht h₂
  obtain ⟨p₂, h₃⟩ := h.exi_aMove_of_not_aTurn_and_taken_ne_empty ht h₂
  simp [isSome_aMove_iff] at h₃
  by_cases h₁ : s.pw = 0; simp [h₁] at h₃; tauto
  rcases h₃ with ⟨h₃, h₄, h₅⟩
  
  -- generalize ha : AStrat.mk (λ s' => if s'.aPos = s.aPos then p else s.aPos) = a
  -- generalize hd : DStrat.mk (λ s' => choose? (· ∈ s'.taken \ s.taken)) = d
  -- have Ha : a.WF; rw [←ha]; infer_instance
  -- have Hd : d.WF; rw [←hd]; infer_instance
  
  -- suffices h₆ : ∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.taken ⊆ s.taken ∧
  --   s'.aPos = if s'.aTurn ∧ Odd s'.taken.size then s.aPos else p
  -- · obtain ⟨s', H₁, H₂, H₃, H₄⟩ := h₆
  
  generalize hp₁ : s.aPos = p₁
  have H₁ : p₁ ≠ p₂; rwa [←hp₁]
  
  -- Use better condition for `H₂` (involving `n`)
  -- have H₂ : s.aPos = p₁ ∨ s.aPos = p₂; left; exact hp₁
  
  have H₃ : p₁ ∉ s.taken; rw [←hp₁]; exact h.aPos_not_mem_taken
  
  generalize hn : (s.taken.size + if s.aTurn then 1 else 0) = n
  clear ht h₂ h₃ h₅ hp₁
  
  induction n generalizing s
  · simp at hn; exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty hn.2 hn.1
  nm n ih
  -- split_ifs at hn with ht
  -- · simp at hn
  sorry

-- #check 0 #exit

theorem State.exi_hist_wf_of_wfCnd {s} (h : WFCnd s) : ∃ hist, sys.WF # s.setHist hist := by
  cases ht : s.aTurn
  · exact exi_hist_wf_of_wfCnd_and_not_aTurn h ht
  by_cases hpw : s.pw = 0
  · have h₁ := h.size_taken_eq_one_of_aTurn_and_pw_eq_zero ht hpw
    have h₃ := h₁
    rw [Set'.size_eq_one_iff] at h₁
    obtain ⟨p, hp, h₁⟩ := h₁
    use [p, s.aPos]
    rw [wf_iff]
    use [p]
    simp; rw [Option.iget_some]
    simp [sys, move, dMove, guard]
    split_ifs with h₂
    · subst h₂; cases h.aPos_not_mem_taken hp
    simp
    ext:1 <;> simp [ht]
    rw [Set'.eq_insert_empty_of_size_eq_one h₃ hp]
  have H₁ := h.aPos_not_mem_taken
  by_cases h₁ : ∃ p, p ∈ s.taken ∧ p.dist s.aPos ≤ s.pw
  · obtain ⟨p, hp, h₁⟩ := h₁
    have H₂ : s.aPos ≠ p; rintro rfl; contradiction
    generalize h₂ : {s with taken := s.taken.erase p, aTurn := false} = s₀
    have h₃ : WFCnd s₀
    · subst h₂
      constructor <;> simp [H₁]
      intro h₂
      use p
      simpa [isSome_aMove_iff, h₁]
    obtain ⟨hist, h₄⟩ := s₀.exi_hist_wf_of_wfCnd_and_not_aTurn h₃ # by simp [←h₂]
    have h₅ : sys.tr (s₀.setHist hist) p = some (s.setHist # p :: hist)
    · subst h₂; simp [sys, move, dMove, H₂, Set'.insert_erase_eq_of_mem hp]
      ext:1 <;> simp [ht]
    use p :: hist
    exact sys.wf_of_tr h₅
  push_neg at h₁
  have h₁' : ∀ (p : PointZ), p.dist s.aPos ≤ s.pw → p ∉ s.taken
  · intro p hp h₂; specialize h₁ p h₂; linarith
  have H₃ := h.taken_ne_empty_of_aTurn ht
  obtain ⟨p, hp⟩ := Set'.exi_mem_of_ne_empty H₃
  have H₂ : s.aPos ≠ p; rintro rfl; contradiction
  generalize h₂ : {s with taken := s.taken.erase p, aTurn := false} = s₀
  have h₃: WFCnd s₀
  · subst h₂
    constructor <;> simp [H₁]
    intro h₂
    use s.aPos + ⟨1, 0⟩
    simp [isSome_aMove_iff]
    have H₄ : (s.aPos + ⟨1, 0⟩).dist s.aPos = 1
    · cases s.aPos; simp [Point.dist]
    have H₅ : 1 ≤ s.pw; simpa [Nat.one_le_iff_ne_zero]
    constructor
    · intro h₃
      apply h₁'
      simpa [H₄]
    simpa [H₄]
  obtain ⟨hist, h₄⟩ := s₀.exi_hist_wf_of_wfCnd_and_not_aTurn h₃ # by simp [←h₂]
  have h₅ : sys.tr (s₀.setHist hist) p = some (s.setHist # p :: hist)
  · subst h₂; simp [sys, move, dMove, H₂, Set'.insert_erase_eq_of_mem hp]
    ext:1 <;> simp [ht]
  use p :: hist
  exact sys.wf_of_tr h₅

theorem State.exi_with_taken_of_wfCnd {s : State} {taken} (h : WFCnd {s with taken := taken}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧ s'.taken = taken := by
  obtain ⟨hist, h₁⟩ := {s with taken := taken}.exi_hist_wf_of_wfCnd h; refine ⟨_, h₁, ?_⟩; simp

theorem State.exi_erase_taken {s : State} {p} (h : WFCnd {s with taken := s.taken.erase p}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken.erase p := exi_with_taken_of_wfCnd h

theorem State.exi_taken_diff {s : State} {ps} (h : WFCnd {s with taken := s.taken \ ps}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken \ ps := exi_with_taken_of_wfCnd h