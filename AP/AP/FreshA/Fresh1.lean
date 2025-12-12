import AP.AP.FreshA.Tile
import AP.AP.Moves

namespace AP

def AStrat.Fresh1 (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁

-----

theorem AStrat.Fresh1.wf {a : AStrat} {s fsp} (h : a.Fresh1 s fsp) : a.WF := h.1

theorem State.false_of_aState_and_dState s [hs₁ : AState s] [hs₂ : DState s] : False := by
  have h₁ := hs₁.2; rw [hs₂.2] at h₁; simp at h₁

theorem AState.even_of_simulate {s s₁ f n} [hs : AState s] [hs₁ : AState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Even n := by
  by_contra h₁; simp at h₁
  obtain ⟨n, rfl⟩ := h₁
  rw [mul_comm] at h
  have h₁ := DState.of_simulate_mul_two_add_one_eq_full h
  exact s₁.false_of_aState_and_dState

theorem AState.fresh1_of_aHwsDisj_aVisited {s fsp} {a : AStrat} [hs : AState s] [ha : a.WF]
(h : ∀ (d : DStrat) [d.WF], ∀ n, ∃ s₁, sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧
s₁.aHwsDisj (fsp.offset (n * 2) |>.insertSet 0 # s.aVisited s₁ |>.toSet)) : a.Fresh1 s fsp := by
  use ha
  split_ands
  · intro d hd n
    specialize h d
    induction n using Nat.mod_2_ind <;> nm n
    · specialize h n
      choose s₁ h₁ h₂ using h
      use s₁, h₁
      choose a₁ ha₁ h₂ using h₂
      specialize h₂ default inferInstance 0
      simp at h₂
      simp [FSP.hasLe]
      exact h₂.2
    specialize h (n + 1)
    choose s₃ h₃ h₄ using h
    rw [Nat.add_one_mul] at h₃
    simp at h₃
    obtain ⟨s₂, ⟨s₁, h₁, h₂⟩, h₃⟩ := h₃
    have hs₁ := AState.of_simulate_mul_two_eq' h₁
    have hs₂ := DState.of_tr h₂
    simp at h₂ h₃
    use s₂
    simp [h₁, h₂]
    rw [←DState.aPos_eq_of_tr h₃]
    choose a₁ ha₁ h₄ using h₄
    specialize h₄ default inferInstance 0
    simp at h₄
    simp [FSP.hasLe]
    grind
  intro d hd s₁ p h₁
  specialize h d
  rw [State.mem_aPtsSimAt_iff_simulate_tr] at h₁
  choose hs₁ n h₁ s₂ h₂ h₃ using h₁
  dsimp at h₃; subst h₃
  simp at h₂
  have h₃ := even_of_simulate h₁
  rw [Nat.even_iff_exi] at h₃
  obtain ⟨n, rfl⟩ := h₃
  specialize h (n + 1)
  simp [Nat.add_one_mul, h₁] at h
  obtain ⟨s₃, ⟨s₂', h₄, h₅⟩, h⟩ := h
  choose a₁ ha₁ h using h
  specialize h default inferInstance 0
  simp at h
  simp [h₂] at h₄; subst h₄
  replace h := h.1
  have hs₂ := DState.of_tr h₂
  rw [←AState.aPos_eq_of_tr h₂, ←DState.aPos_eq_of_tr h₅]
  simp at h₅
  apply Set'.not_mem_of_subset _ h
  exact State.aVisited_subset_of_simulate_le ⟨a, d⟩ (n * 2) (n * 2 + 2)
    (by omega) h₁ # by simpa [h₁, h₂]

-- #check 0 #exit