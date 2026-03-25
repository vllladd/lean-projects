import Projects.AP.FreshA

namespace AP

@[simp]
theorem init_initState {pw p} : (initState pw p).init = initState pw p := rfl

theorem State.hist_eq_aPos_of {s} [hs : sys.WF s]
(h₁ : s.taken = ∅) (h₂ : s.aTurn = false) : s.hist = [s.aPos] := by
  have h₃ := s.length_hist_eq_size_taken_mul_two_add_ite
  simp [h₁, h₂] at h₃
  have h₄ : s.aPos₀ = s.aPos
  · rw [←h₃]; simp
  rw [←h₄, ←h₃]; simp

theorem State.aPos₀_eq_aPos_of {s} [hs : sys.WF s]
(h₁ : s.taken = ∅) (h₂ : s.aTurn = false) : s.aPos₀ = s.aPos := by
  simp [aPos₀, hist_eq_aPos_of h₁ h₂]