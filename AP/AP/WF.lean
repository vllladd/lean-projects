import AP.AP.FSP

namespace AP

structure WFCnd (s : State) : Prop where
  aPos_not_mem_taken : s.aPos ∉ s.taken
  taken_ne_empty_of_aTurn : s.aTurn → s.taken ≠ ∅
  exi_aMove_of_not_aTurn_and_taken_ne_empty : s.aTurn = false → s.taken ≠ ∅ →
    ∃ p, s.aMove p |>.isSome

theorem State.wfCnd_of_wf {s} [hs : sys.WF s] : WFCnd s where
  aPos_not_mem_taken := by simp
  taken_ne_empty_of_aTurn ht := AState.mk hs ht |>.taken_ne_empty
  exi_aMove_of_not_aTurn_and_taken_ne_empty ht h :=
    DState.mk hs ht |>.exi_aMove_of_taken_ne_empty h

theorem State.exi_hist_wf_of_wfCnd_and_not_aTurn {s} (h : WFCnd s)
(ht : s.aTurn = false) : ∃ hist, sys.WF # s.setHist hist := by
  sorry

-- #check 0 #exit

theorem State.exi_hist_wf_of_wfCnd {s} (h : WFCnd s) : ∃ hist, sys.WF # s.setHist hist := by
  cases ht : s.aTurn
  · exact exi_hist_wf_of_wfCnd_and_not_aTurn h ht
  
  -- obtain ⟨p, hp⟩ := Set'.exi_mem_of_ne_empty # h.taken_ne_empty_of_aTurn ht
  -- generalize h₁ : {s with aTurn := false, taken := s.taken.erase p} = sd
  -- obtain ⟨hist, h₂⟩ : ∃ hist, sys.WF # sd.setHist hist
  -- · subst h₁
  --   rcases h with ⟨h₁, h₂, -⟩
  --   specialize h₂ ht
  --   apply exi_hist_wf_of_wfCnd_and_not_aTurn _ rfl
  --   constructor <;> simp; simp [h₁]
  --   intro h₃
  --   simp [isSome_aMove_iff]
  
  sorry

-- #check 0 #exit

theorem State.exi_with_taken_of_wfCnd {s : State} {taken} (h : WFCnd {s with taken := taken}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧ s'.taken = taken := by
  obtain ⟨hist, h₁⟩ := {s with taken := taken}.exi_hist_wf_of_wfCnd h; refine ⟨_, h₁, ?_⟩; simp

theorem State.exi_erase_taken {s : State} {p} (h : WFCnd {s with taken := s.taken.erase p}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken.erase p := exi_with_taken_of_wfCnd h

theorem State.exi_taken_diff {s : State} {ps} (h : WFCnd {s with taken := s.taken \ ps}) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken \ ps := exi_with_taken_of_wfCnd h