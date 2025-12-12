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
s₁.aHwsDisj (fsp.insert 1 s.aPos |>.offset (n * 2) |>.insertSet 0 #
s.aVisited s₁ |>.toSet.erase s.aPos)) : a.Fresh1 s fsp := by
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
      replace h₂ := h₂.2
      intro k hk
      specialize h₂ k hk
      simp [FSP.insert, FSP.insertSet] at h₂
      grind
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
    replace h₄ := h₄.2
    intro k hk
    specialize h₄ k (by omega)
    simp [FSP.insert, FSP.insertSet] at h₄
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
  have h₆ : s₃.aPos ≠ s.aPos
  · replace h := h.2
    specialize h 1 (by omega)
    simp [FSP.insert, FSP.insertSet] at h
    exact h.1
  replace h := h.1 h₆
  have hs₂ := DState.of_tr h₂
  rw [←AState.aPos_eq_of_tr h₂, ←DState.aPos_eq_of_tr h₅]
  simp at h₅
  apply Set'.not_mem_of_subset _ h
  exact State.aVisited_subset_of_simulate_le ⟨a, d⟩ (n * 2) (n * 2 + 2)
    (by omega) h₁ # by simpa [h₁, h₂]

def aFreshCnd (s : State) (fsp : FSP) (s₁ : State) : Prop :=
  s₁.aHwsDisj # fsp.offset (s₁.diff s) |>.insertSet 0 # s.aVisited s₁ |>.toSet

noncomputable
def aFresh (s : State) (fsp : FSP) : AStrat :=
  aSeek # aFreshCnd s fsp

@[simp]
instance {s fsp} : aFresh s fsp |>.WF := by
  unfold aFresh; infer_instance

theorem AState.exi_aSeek_tr {s P} [hs : AState s]
(h : ∃ p s₁, sys.tr s p = some s₁ ∧ P s₁) :
∃ s₁, sys.tr s (aSeek P |>.f s) = some s₁ ∧ P s₁ := by
  simp [aSeek]
  rw [choose?_eq_of_exi]
  rotate_left; exact h
  simp
  have h₁ := Classical.epsilon_spec h
  generalize hp : Classical.epsilon (λ p => ∃ s₁, sys.tr s p = some s₁ ∧ P s₁) = p at h₁ ⊢
  choose s₁ h₁ h₂ using h₁
  simpa [sys.validTr_of_eq_some h₁, h₁]

theorem AState.aPos_ne_of_tr {s s₁ p} [hs : AState s]
(h : sys.tr s p = some s₁) : s₁.aPos ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

-- #check 0 #exit

theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
(h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
  use aFresh s fsp
  apply fresh1_of_aHwsDisj_aVisited
  intro d hd n
  replace h := AState.aHwsDisj_insert_one_aPos h
  induction n; simpa
  nm n ih
  
  choose s₁ h₁ h₂ using ih
  simp [Nat.add_one_mul, h₁]
  
  have hs₁ := AState.of_simulate_mul_two_eq' h₁
  
  generalize h₃ : (fsp.insert 1 s.aPos |>.offset (n * 2) |>.insertSet 0 #
    s.aVisited s₁ |>.toSet.erase s.aPos) = fsp₁ at h₂
  
  replace h₂ := AState.aHwsDisj_insert_one_aPos h₂
  choose a ha h₂ using h₂
  
  obtain ⟨s₂, h₄, h₅⟩ : ∃ s₂, sys.tr s₁ (aFresh s fsp |>.f s₁) = some s₂ ∧ aFreshCnd s fsp s₂
  ·
    unfold aFresh
    apply exi_aSeek_tr
    
    -- choose s₂ h₄ h₅ using h₂ default inferInstance 1
    -- 
    -- simp at h₄
    -- use a.f s₁, s₂, h₄
    -- 
    -- -- specialize h₂ d₁ hd₁ (k + 1)
    -- -- simp_rw [sys.simulate_succ_full'] at h₂
    -- -- simp [h₄] at h₂
    -- -- choose s₃ h₂ h₆ using h₂
    -- -- use s₃, h₂
    -- -- 
    -- -- -- cases k
    -- -- -- ·
    -- -- --   simp at h₆
    -- -- --   simp [FSP.hasLe, FSP.insertSet]
    -- -- --   split
    -- -- 
    -- -- -- simp [h₄] at h₂
    -- -- -- simp [FSP.hasLe, FSP.insert, FSP.insertSet] at h₂ h₅
    -- -- -- specialize h₂ 1
    -- -- -- simp [←h₃, FSP.insert, FSP.insertSet] at h₂
    -- -- 
    -- -- simp [FSP.hasLe]
    -- -- intro c hc
    -- -- simp [FSP.insertSet]
    -- -- 
    -- -- have h₇ : s₃.aPos ∉ (fsp.offset # s₂.diff s).get c
    -- 
    -- unfold aFreshCnd
    -- rw [State.diff, length_hist_eq_of_tr h₄, State.length_hist_eq_of_simulate_eq h₁]
    -- dsimp
    -- rw [show s.hist.length + n * 2 + 1 - s.hist.length = n * 2 + 1 by omega]
    -- rw [AState.aVisited_eq_of_tr h₄ # sys.reachable_of_simulate_eq h₁]
    -- 
    -- use a, ha
    -- intro d₁ hd₁ k
    -- specialize h₂ d₁ hd₁ (k + 1)
    -- simp only [sys.simulate_succ_full'] at h₂
    -- obtain ⟨s₃, ⟨s₂', H₁, H₂⟩, H₃⟩ := h₂
    -- simp at H₁
    -- 
    -- simp [h₄] at H₁; subst H₁
    -- use s₃, H₂
    -- 
    -- rw [←AState.aPos_eq_of_tr h₄]
    -- rw [FSP.offset_succ']
    -- 
    -- clear h₅
    -- 
    -- cases n
    -- ·
    --   simp at h₁
    --   subst h₁
    --   simp at h₃ H₃ ⊢
    --   subst h₃
    --   simp at H₃
    -- 
    -- #check 0 #exit
    -- 
    -- simp [FSP.hasLe] at H₃ ⊢
    -- 
    -- rw [FSP.offset_succ']
    -- 
    -- simp [FSP.hasLe, FSP.insert, FSP.insertSet] at H₃ h₅ ⊢
    -- intro c hc
    -- specialize H₃ (c + 1) (by omega)
    -- simp at H₃
    -- split_ifs at H₃ ⊢ with H₄
    -- ·
    --   subst H₄
    --   simp at H₃ ⊢
    --   rcases H₃ with ⟨H₃, H₄⟩
    --   split_ands
    --   ·
    --     by_contra! H₅
    --     sorry
    --   ·
    --     sorry
    --   ·
    --     sorry
    -- ·
    --   sorry
    
    sorry
  
  simp [h₄]
  unfold aFreshCnd at h₅
  
  -- rw [State.diff, length_hist_eq_of_tr h₄, State.length_hist_eq_of_simulate_eq h₁] at h₅
  -- dsimp at h₅
  -- rw [show s.hist.length + n * 2 + 1 - s.hist.length = n * 2 + 1 by omega] at h₅
  -- rw [AState.aVisited_eq_of_tr h₄ # sys.reachable_of_simulate_eq h₁] at h₅
  
  sorry