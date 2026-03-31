import Projects.System.Symmetry

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem exi_tr_of_pred_diff {p : S → Prop} {s s'}
(h₁ : sys.Reachable s s') (h₂ : ¬p s) (h₃ : p s') :
∃ s₁ s₂ t, sys.Reachable s s₁ ∧ sys.tr s₁ t = some s₂ ∧
sys.Reachable s₂ s' ∧ ¬p s₁ ∧ p s₂ := by
  simp [reachable_iff_exi_trs] at h₁
  choose ts h₁ using h₁
  induction ts generalizing s
  · simp at h₁; grind
  nm t ts ih; simp at h₁
  choose sx h₁ h₄ using h₁
  by_cases h₅ : p sx
  · use s, sx, t; simp [h₁, h₂, h₅, reachable_of_trs h₄]
  specialize ih h₅ h₄
  choose s₁ s₂ t' H₁ H₂ H₃ H₄ H₅ using ih
  use s₁, s₂, t'; grind