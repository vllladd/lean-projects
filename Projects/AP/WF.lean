import Projects.AP.FSP

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
  rw [wf_iff']
  use []
  simp
  ext:1 <;> simp [ht, h₁]

theorem State.exi_hist_wf_of_exi_p2_aux {s : State} {p₁ p₂ : PointZ} {taken : Set' PointZ}
(h₁ : p₁ ≠ p₂)
(h₃ : p₁ ∉ taken)
(h₄ : p₂ ∉ taken)
(h₂ : Point.dist p₁ p₂ ≤ ↑s.pw)
(hn : (s.taken.size * 2 - if s.aTurn = true then 1 else 0) = 0)
(h₆ : s.aPos = if Odd (s.taken.size + if s.aTurn = true then 0 else 1) then p₁ else p₂)
(h₅ : s.taken ⊆ taken)
(H : s.aTurn = true → s.taken ≠ ∅) :
∃ hist, sys.WF (s.setHist hist) := by
  by_cases H₁ : s.taken = ∅
  · simp [H₁] at H; exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty H H₁
  clear H
  rw [Nat.sub_eq_zero_iff_le] at hn
  replace hn : s.taken.size * 2 ≤ 1; apply hn.trans; simp
  replace hn : s.taken.size / 2 ≤ 1 / 2; omega
  simp [Nat.lt_succ_iff, Nat.le_one_iff, H₁] at hn
  simp [hn, Nat.one_add] at h₆
  have H₃ : s.aPos ∉ s.taken
  · split_ifs at h₆ <;> subst h₆ <;> apply Set'.not_mem_of_subset h₅ <;> assumption
  obtain ⟨p, hp⟩ := Set'.exi_mem_of_ne_empty H₁
  have H₂ : s.aPos ≠ p; rintro rfl; contradiction
  replace hn := Set'.eq_insert_empty_of_size_eq_one hn hp
  by_cases ht : s.aTurn <;> simp at ht <;> simp [ht] at h₆ <;> subst h₆
  · use [p, s.aPos]
    rw [wf_iff']
    use [p]
    simp [sys, move, dMove]
    simp [H₂]
    ext:1 <;> simp [hn, ht]
  · have H₄ : p₁ ≠ p
    · rintro rfl; exact h₃ # h₅ p₁ hp
    use [s.aPos, p, p₁]
    rw [wf_iff']
    use [p, s.aPos]
    simp [sys, move, aMove, dMove]
    rw [Point.dist_comm] at h₂
    simp [h₁, H₄, H₂, h₂]
    ext:1 <;> simp [hn, ht]

theorem State.exi_hist_wf_of_exi_p2 {s : State} {p₁ p₂ : PointZ}
(hpw : s.pw ≠ 0)
(h₁ : p₁ ≠ p₂)
(h₂ : p₁.dist p₂ ≤ s.pw)
(h₃ : p₁ ∉ s.taken)
(h₄ : p₂ ∉ s.taken)
(ha : s.aPos = p₁)
(ht : s.aTurn = false)
(h₇ : Even s.taken.size) :
∃ hist, sys.WF # s.setHist hist := by
  by_cases H : s.taken = ∅
  · exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty ht H
  generalize h₅ : s.taken = taken at h₃ h₄
  generalize hn : (s.taken.size * 2 - ite s.aTurn 1 0) = n
  have h₆ : s.aPos = if Odd # s.taken.size + ite s.aTurn 0 1 then p₁ else p₂
  · simp [ha, ht]
    intro h
    rw [←Nat.not_even_iff_odd] at h
    contradiction
  replace h₅ : s.taken ⊆ taken; simp [←h₅]
  replace H : s.aTurn = true → s.taken ≠ ∅; tauto
  clear ha ht h₇
  induction n generalizing s
  · exact s.exi_hist_wf_of_exi_p2_aux h₁ h₃ h₄ h₂ hn h₆ h₅ H
  nm n ih
  have H₃ : s.aPos ∉ s.taken
  · rw [h₆]; split_ifs <;> apply Set'.not_mem_of_subset h₅ <;> assumption
  by_cases ht : s.aTurn
  · simp [ht] at hn h₆; specialize H ht
    cases H₁ : s.taken.size; simp [H] at H₁; nm k
    obtain ⟨p, hp⟩ := Set'.exi_mem_of_ne_empty H
    generalize hs₁ : {s with taken := s.taken.erase p, aTurn := false} = s₁
    specialize @ih s₁
    simp [H₁, Nat.succ_mul] at hn h₆
    simp [←hs₁, Set'.size_erase hp, H₁] at ih
    specialize ih hpw h₂ hn h₆ _
    · apply Set'.subset_trans _ h₅; simp
    obtain ⟨hist, ih⟩ := ih
    replace ih : sys.WF # s₁.setHist hist
    · convert ih using 1; simp [←hs₁]
    have H₂ : sys.tr (s₁.setHist hist) p = some (s.setHist # p :: hist)
    · simp [←hs₁, sys, move, dMove]
      constructor
      · rintro rfl; contradiction
      ext:1 <;> simp [ht, Set'.insert_eq_of_mem hp]
    exact ⟨_, sys.wf_of_tr H₂⟩
  · simp at ht; simp [ht] at hn h₆
    clear H
    by_cases H : s.taken = ∅
    · exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty ht H
    cases H₁ : s.taken.size; simp [H] at H₁; nm k
    generalize hs₁ :
      {s with
        aPos := if Even s.taken.size then p₂ else p₁
      , aTurn := true} = s₁
    specialize @ih s₁
    simp [H₁, Nat.succ_mul] at hn h₆
    simp [←hs₁, H₁, Nat.succ_mul] at ih
    specialize ih hpw h₂ hn _ _ H
    · simp [Nat.ite_odd]
    · apply Set'.subset_trans _ h₅; simp
    obtain ⟨hist, ih⟩ := ih
    replace ih : sys.WF # s₁.setHist hist
    · convert ih using 1; simp [←hs₁, H₁]
    have H₂ : sys.tr (s₁.setHist hist) s.aPos = some (s.setHist # s.aPos :: hist)
    · simp [←hs₁, sys, move, aMove, H₁]
      symm; constructor
      · ext:1 <;> simp [ht]
      split_ifs at h₆ ⊢ with H₄ <;> subst h₆
      · use ne_symm' h₁
      · rw [Point.dist_comm]; use h₁
    exact ⟨_, sys.wf_of_tr H₂⟩

theorem State.exi_hist_wf_of_wfCnd_and_not_aTurn {s} (h : WFCnd s)
(ht : s.aTurn = false) : ∃ hist, sys.WF # s.setHist hist := by
  classical
  by_cases h₂ : s.taken = ∅
  · exact exi_hist_wf_of_not_aTurn_and_taken_eq_empty ht h₂
  obtain ⟨p₂, h₃⟩ := h.exi_aMove_of_not_aTurn_and_taken_ne_empty ht h₂
  simp [isSome_aMove_iff] at h₃
  by_cases h₁ : s.pw = 0; simp [h₁] at h₃; tauto
  rcases h₃ with ⟨h₃, h₄, h₅⟩
  have h₀ := h.aPos_not_mem_taken
  have h₅' := h₅; rw [Point.dist_comm] at h₅'
  rcases s.taken.size.odd_or_even₁.symm with h₆ | h₆
  · exact @s.exi_hist_wf_of_exi_p2 s.aPos p₂ h₁ h₃ h₅' h₀ h₄ rfl ht h₆
  generalize hs₁ : {s with aPos := p₂, aTurn := true, hist := []} = s₁
  have H₁ : sys.tr s₁ s.aPos = some (s.setHist [s.aPos])
  · simp [←hs₁, sys, move, aMove, ne_symm' h₃, h₀, h₅']
    ext:1 <;> simp [ht]
  obtain ⟨p, hp⟩ := Set'.exi_mem_of_ne_empty h₂
  generalize hs₂ :
    { s with
      aPos := p₂
    , taken := s.taken.erase p
    , aTurn := false
    , hist := []} = s₂
  have G₁ : p ≠ p₂
  · rintro rfl; contradiction
  have H₂ : sys.tr s₂ p = some (s₁.setHist [p])
  · simp [←hs₁, ←hs₂, sys, move, dMove, ne_symm' G₁]
    ext:1 <;> simp; exact Set'.insert_eq_of_mem hp
  cases H₃ : s.taken.size; simp [h₂] at H₃; nm k
  simp [H₃] at h₆
  have G₂ : Even s₂.taken.size
  · simpa [←hs₂, Set'.size_erase hp, H₃]
  have G₃ := @s₂.exi_hist_wf_of_exi_p2 p₂ s.aPos
  simp [←hs₂] at G₃
  specialize G₃ h₁ (ne_symm' h₃) h₅ (λ _ => h₄) (λ _ => h₀) _
  · simpa [Set'.size_erase hp, H₃]
  obtain ⟨hist, G₃⟩ := G₃
  use s.aPos :: p :: hist
  have H₄ : sys.tr (s₂.setHist hist) p = some (s₁.setHist (p :: hist))
  · simp; use s₁.setHist [p]; simpa
  have H₅ : sys.tr (s₁.setHist (p :: hist)) s.aPos =
    some (s.setHist (s.aPos :: p :: hist))
  · simp; use s.setHist [s.aPos]; simpa
  replace G₃ : sys.WF # s₂.setHist hist
  · convert G₃ using 1; simp [←hs₂]
  have H₆ := sys.wf_of_tr H₄
  exact sys.wf_of_tr H₅

theorem State.exi_hist_wf_of_wfCnd {s} (h : WFCnd s) : ∃ hist, sys.WF # s.setHist hist := by
  cases ht : s.aTurn
  · exact exi_hist_wf_of_wfCnd_and_not_aTurn h ht
  by_cases hpw : s.pw = 0
  · have h₁ := h.size_taken_eq_one_of_aTurn_and_pw_eq_zero ht hpw
    have h₃ := h₁
    rw [Set'.size_eq_one_iff] at h₁
    obtain ⟨p, hp, h₁⟩ := h₁
    use [p, s.aPos]
    rw [wf_iff']
    use [p]
    simp [sys, move, dMove, guard]
    split_ands
    · rintro rfl; exact h.aPos_not_mem_taken hp
    ext:1 <;> simp [ht]
    simp [Set'.eq_insert_empty_of_size_eq_one h₃ hp]
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