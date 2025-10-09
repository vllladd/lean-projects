import AP.AP.FSP

namespace AP

theorem State.size_taken_eq_ite_of_tr {s s' p} [hs : sys.WF s] (h : sys.tr s p = some s') :
s'.taken.size = s.taken.size + if s.aTurn then 0 else 1 := by
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · simp [hs.taken_eq_of_tr h]
  simp; simp [hs.tr_eq_some_iff] at h
  rcases h with ⟨⟨h₁, h₂⟩, rfl⟩
  simp [Set'.size_insert h₂]

theorem State.length_hist_eq_size_taken_mul_two_add_ite {s} [hs : sys.WF s] :
s.hist.length = s.taken.size * 2 + if s.aTurn then 0 else 1 := by
  obtain ⟨ps, h₁⟩ := wf_iff.mp hs
  induction ps using List.reverseRecOn generalizing s
  · simp at h₁; rw [←h₁]; simp
  nm ps p ih
  simp at h₁
  obtain ⟨s', h₁, h₂⟩ := h₁
  have h₃ := sys.reachable_of_trs h₁
  dsimp at h₃
  have hs' := sys.wf_of_reachable h₃
  specialize @ih s' _
  simp [pw_eq_of_reachable h₃, aPos₀_eq_of_reachable h₃] at ih
  specialize ih h₁
  simp [hist_eq_of_tr h₂, ih]; clear ih
  rw [size_taken_eq_ite_of_tr h₂, aTurn_eq_of_tr h₂]
  simp; split_ifs <;> ring_nf

theorem State.length_hist_le_size_taken_mul_two_add_one {s} [hs : sys.WF s] :
s.hist.length ≤ s.taken.size * 2 + 1 := by
  simp [length_hist_eq_size_taken_mul_two_add_ite]

theorem State.size_taken_mul_two_le_length_hist {s} [hs : sys.WF s] :
s.taken.size * 2 ≤ s.hist.length := by
  simp [length_hist_eq_size_taken_mul_two_add_ite]

theorem State.length_hist_le_two_of_pw_eq_zero {s} [hs : sys.WF s]
(h : s.pw = 0) : s.hist.length ≤ 2 := by
  obtain ⟨ps, h₁⟩ := wf_iff.mp hs
  cases ps; simp at h₁; rw [←h₁]; simp
  nm p₁ ps; simp at h₁; split at h₁; simp at h₁; nm x s₁ h₂; clear x
  cases ps; simp at h₁; subst h₁; simp [hist_eq_of_tr h₂]
  nm p₂ ps; simp at h₁; split at h₁; simp at h₁; nm x s₂ h₃; clear x
  have hs₁ : AState s₁; use sys.wf_of_tr h₂; simp [aTurn_eq_of_tr h₂]
  simp [hs₁.tr_eq_some_iff] at h₃
  rcases h₃ with ⟨⟨h₃, h₄, h₅⟩, rfl⟩
  simp [pw_eq_of_tr h₂, h, ne_symm' h₃] at h₅

theorem State.size_taken_le_one_of_pw_eq_zero {s} [hs : sys.WF s]
(h : s.pw = 0) : s.taken.size ≤ 1 := by
  by_contra! h₁; replace h₂ := s.size_taken_mul_two_le_length_hist
  replace h₂ : 3 ≤ s.hist.length; linarith
  linarith [length_hist_le_two_of_pw_eq_zero h]

def exiWFCndMove (pw : ℕ) (aTurn : Bool) (aPos : PointZ) (taken : Set' PointZ) : Prop :=
  aTurn = false → ∃ p, aPos ≠ p ∧ p ∉ taken ∧ p.dist aPos ≤ pw

structure ExiWFCnd (pw : ℕ) (aTurn : Bool) (aPos : PointZ) (taken : Set' PointZ) : Prop where
  pw_ne_zero : pw ≠ 0
  taken_ne_empty : taken ≠ ∅
  aPos_not_mem_taken : aPos ∉ taken
  exi_move_of : exiWFCndMove pw aTurn aPos taken

theorem State.exiWFCndMove_of_pw_ne_zero {s} [hs : sys.WF s] (h : s.pw ≠ 0) :
exiWFCndMove s.pw s.aTurn s.aPos s.taken := by
  intro ht; replace hs : DState s; use hs; clear ht
  sorry

-- #check 0 #exit

theorem State.exi_wf pw aTurn aPos taken (h : ExiWFCnd pw aTurn aPos taken) :
∃ s, sys.WF s ∧ s.pw = pw ∧ s.aTurn = aTurn ∧ s.aPos = aPos ∧ s.taken = taken := by
  sorry

-- #check 0 #exit

theorem State.exi_erase_taken {s p} [hs : sys.WF s] (h₀ : s.taken.erase p ≠ ∅)
(h : exiWFCndMove s.pw s.aTurn s.aPos (s.taken.erase p)) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken.erase p := by
  by_cases hp : p ∉ s.taken
  · rw [Set'.erase_eq_of_not_mem hp]; use s
  push_neg at hp
  replace h₀ : 2 ≤ s.taken.size
  · simp [Set'.erase_eq_empty_iff] at h₀
    obtain ⟨p₁, hp₁, h₀⟩ := h₀
    by_contra! h₁
    rw [Nat.lt_succ] at h₁
    replace h₁ := Set'.size_eq_one_of_size_le_one_and_mem h₁ hp
    exact h₀ # Set'.eq_of_size_eq_one_and_mem h₁ hp₁ hp
  by_cases h₁ : s.pw = 0; linarith [size_taken_le_one_of_pw_eq_zero h₁]
  apply exi_wf; constructor
  · simp [h₁]
  · apply ne_of_congr (·.size)
    rw [Set'.size_erase hp]
    obtain ⟨n, h₂⟩ := Nat.exists_eq_add_of_le h₀
    simp [h₂]
  · simp
  · exact h

-- #check 0 #exit

theorem State.exi_taken_diff {s ps} [hs : sys.WF s] (h₀ : s.taken \ ps ≠ ∅)
(h : exiWFCndMove s.pw s.aTurn s.aPos (s.taken \ ps)) :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken \ ps := by
  revert s; apply ps.ind;
  · intro s hs h₀ h; simp; use s
  clear ps; intro ps p hp ih s hs h₀
  specialize @ih s _ _ _
  · contrapose! h₀; simp [Set'.diff_insert, h₀]
  · intro ht
    replace hs : DState s; use hs
    sorry
  obtain ⟨s₁, hs₁, hpw, ht, hpa, ih⟩ := ih
  have h₁ : s.taken \ ps.insert p = s₁.taken.erase p
  · ext p₁; rw [ih]; simp; tauto
  rw [←hpw, ←ht, ←hpa, h₁]
  apply exi_erase_taken; rwa [←h₁]