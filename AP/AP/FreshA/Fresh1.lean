import AP.AP.FreshA.Tile
import AP.AP.Moves

namespace AP

def AStrat.Fresh1 (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁

-----

theorem AStrat.Fresh1.wf {a : AStrat} {s fsp} (h : a.Fresh1 s fsp) : a.WF := h.1

theorem AState.fresh1_of_aHwsDisj_aVisited {s fsp} {a : AStrat} [hs : AState s] [ha : a.WF]
(h : ∀ (d : DStrat) [d.WF], ∀ n, ∃ s₁, sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧
s₁.aHwsDisj (fsp.offset (n * 2) |>.insertSet 0 # s.aVisited s₁ |>.toSet)) : a.Fresh1 s fsp := by
  use ha
  split_ands
  ·
    intro d hd n
    specialize h d
    
    -- have H₁ : ∀ n, ∃ s₁, sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧
    --   ¬fsp.hasLe (n * 2) s₁.aPos
    -- · clear n; intro n
    
    induction n using Nat.mod_2_ind <;> nm n
    ·
      specialize h n
      choose s₁ h₁ h₂ using h
      use s₁, h₁
      choose a₁ ha₁ h₂ using h₂
      specialize h₂ default inferInstance 0
      simp at h₂
      simp [FSP.hasLe]
      exact h₂.2
    
    choose s₁ h₁ h₂ using h n
    
    have hs₁ := AState.of_simulate_mul_two_eq' h₁
    
    obtain ⟨s₂, h₃⟩ : sys.validTr s₁ (a.f s₁)
    ·
      specialize h (n + 1)
      choose s₃ h₃ h₄ using h
      rw [Nat.add_one_mul] at h₃
      simp [h₁] at h₃
      choose s₂ h₃ h₅ using h₃
      exact sys.validTr_of_eq_some h₃
    
    use s₂
    simp [h₁, h₃]
    
    sorry
  
  ·
    sorry