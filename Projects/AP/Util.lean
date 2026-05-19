import Projects.AP.FreshA

namespace AP

@[simp]
theorem init_initState {pw p} : (initState pw p).init = initState pw p := rfl

theorem DState.of_taken_eq_empty {s} [hs : sys.WF s] (h : s.taken = ∅) : DState s := by
  use hs; by_contra h₁; simp at h₁
  have h₂ := s.length_hist_eq_size_taken_mul_two_add_ite
  simp [h, h₁] at h₂

theorem State.hist_eq_aPos_of {s} [hs : sys.WF s]
(h₁ : s.taken = ∅) : s.hist = [s.aPos] := by
  replace hs := DState.of_taken_eq_empty h₁
  have h₃ := s.length_hist_eq_size_taken_mul_two_add_ite
  simp [h₁] at h₃
  have h₄ : s.aPos₀ = s.aPos
  · rw [←h₃]; simp
  rw [←h₄, ←h₃]; simp

theorem State.aPos₀_eq_aPos_of {s} [hs : sys.WF s] (h₁ : s.taken = ∅) : s.aPos₀ = s.aPos := by
  simp [aPos₀, hist_eq_aPos_of h₁]

@[simp]
theorem State.wfCnd_setHist {s : State} {hist} : WFCnd (s.setHist hist) ↔ WFCnd s := by
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> constructor <;> simp_all

@[simp] theorem State.pw_init {s : State} : s.init.pw = s.pw := rfl

theorem State.taken_eq_empty_of_dState_and_pw_eq_zero {s} [hs : DState s]
(h : s.pw = 0) : s.taken = ∅ := by
  have h₁ := size_taken_le_one_of_pw_eq_zero h
  have h₂ := s.length_hist_eq_size_taken_mul_two_add_ite
  simp at h₂
  obtain ⟨ps, h₃⟩ := wf_iff.mp hs.wf
  replace h₂ : s.hist.length ≤ 3; omega
  clear h₁
  rw [length_hist_eq_of_trs_eq h₃] at h₂
  simp at h₂
  replace h₂ : ps.length ≤ 2; omega
  cases ps <;> simp at h₃
  · rw [←h₃]; simp
  nm p₁ ps
  choose s₁ h₄ h₃ using h₃
  cases ps <;> simp at h₃
  · subst h₃
    have h₅ : DState s₁.init; simp
    have h₆ := AState.of_tr h₄
    cases s₁.false_of_aState_and_dState
  nm p₂ ps
  cases ps
  rotate_left; grind
  clear h₂
  choose s₂ h₅ h₃ using h₃
  simp at h₃
  subst h₃
  have hs₀ : DState s₂.init; simp
  have hs₁ := AState.of_tr h₄
  simp [AState.tr_eq_some_iff] at h₅
  obtain ⟨⟨h₅, h₆, h₇⟩, h₈⟩ := h₅
  contrapose! h₇; clear h₇
  simp [pw_eq_of_tr h₄, h]
  rw [DState.aPos_eq_of_tr h₄]
  simp [←h₈, aPos₀]
  rw [hist_eq_of_tr h₄]
  simp
  contrapose! h₅; subst h₅
  rw [←h₈]
  simp [aPos₀, hist_eq_of_tr h₄, DState.aPos_eq_of_tr h₄]

theorem State.pw_ne_zero_of_dState_and_taken_ne_empty {s} [hs : DState s]
(h : s.taken ≠ ∅) : s.pw ≠ 0 := by
  contrapose! h; exact taken_eq_empty_of_dState_and_pw_eq_zero h