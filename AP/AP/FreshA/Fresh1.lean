import AP.AP.FreshA.Tile
import AP.AP.Moves

namespace AP

def AStrat.Fresh1 (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁

def AStrat.Fresh1Alt (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aPos ∉ fsp.get 0 ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁ s₂,
  sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧ sys.tr s₁ (a.f s₁) = some s₂ ∧
  s₂.aHwsDisj (fsp.offset (n * 2 + 1) |>.insertSet 0 (s.aVisited s₁).toSet)

def aFreshCnd (s : State) (fsp : FSP) (s₁ : State) : Prop :=
  s₁.aHwsDisj # fsp.offset (s₁.diff s) |>.insertSet 0 # s.aVisited s₁ |>.toSet

noncomputable
def aFresh (s : State) (fsp : FSP) : AStrat :=
  aSeek # aFreshCnd s fsp

-- #check 0 #exit

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
(h : sys.tr s p = some s₁) : p ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

theorem State.aPos_notMem_of_aWinsDisj {s : State} {fsp a d}
(h : s.aWinsDisj fsp ⟨a, d⟩) : s.aPos ∉ fsp.get 0 := by
  specialize h 0; simp at h; exact h

theorem State.aPos_notMem_of_aForallWinsDisj {s : State} {fsp a}
(h : s.aForallWinsDisj fsp a) : s.aPos ∉ fsp.get 0 :=
  aPos_notMem_of_aWinsDisj # h default inferInstance

theorem State.aPos_notMem_of_aHwsDisj {s : State} {fsp}
(h : s.aHwsDisj fsp) : s.aPos ∉ fsp.get 0 := by
  choose a ha h using h; exact aPos_notMem_of_aForallWinsDisj h

theorem State.hasTr_of_aWinsDisj {s fsp a d} [hs : sys.WF s]
(h : s.aWinsDisj fsp ⟨a, d⟩) : sys.hasTr s := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  rotate_left; simp
  specialize h 1
  choose s₁ h₁ h₂ using h
  simp at h₁
  use a.f s, s₁

theorem State.hasTr_of_aForallWinsDisj {s fsp a} [hs : sys.WF s]
(h : s.aForallWinsDisj fsp a) : sys.hasTr s :=
  hasTr_of_aWinsDisj # h default inferInstance

theorem State.hasTr_of_aHwsDisj {s fsp} [hs : sys.WF s]
(h : s.aHwsDisj fsp) : sys.hasTr s := by
  choose a ha h using h; exact hasTr_of_aForallWinsDisj h

@[simp]
instance {s fsp} : aFresh s fsp |>.WF := by
  unfold aFresh; infer_instance

theorem AState.aForallWinsDisj_of_fresh1Alt {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Alt s fsp) : s.aForallWinsDisj fsp a := by
  choose ha h₀ h using h
  intro d hd n
  specialize h d hd
  induction n using Nat.mod_2_ind <;> nm n
  · cases n; simpa; nm n
    specialize h n
    simp at h
    choose s₁ h₁ s₂ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    have hs₂ := DState.of_tr h₂
    simp [Nat.add_mul, h₁, h₂]
    choose a₁ ha₁ h₃ using h₃
    specialize h₃ d hd 1
    simp at h₃
    choose s₃ h₃ h₄ using h₃
    use s₃, h₃
    simp [FSP.hasLe, FSP.insertSet] at h₄ ⊢
    intro k hk
    have h₅ := h₄ 0
    specialize h₄ 1
    simp at h₄ h₅
    choose h₅ h₆ using h₅
    rw [Nat.le_add_one_iff] at hk
    rcases hk with hk | rfl
    · exact h₆ k hk
    · exact h₄
  · specialize h n
    choose s₁ s₂ h₁ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    simp [h₁, h₂]
    replace h₃ := State.aPos_notMem_of_aHwsDisj h₃
    simp at h₃
    simp [FSP.hasLe]
    exact h₃.2

theorem AState.fresh1_of_alt {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Alt s fsp) : a.Fresh1 s fsp := by
  have H₀ := h
  choose ha h₀ h using h
  use ha, aForallWinsDisj_of_fresh1Alt H₀
  intro d hd s₁ p h₁
  rw [State.mem_aPtsSimAt_iff_simulate_tr] at h₁
  choose hs₁ n h₁ s₂ h₂ h₃ using h₁
  simp at h₂ h₃; subst h₃
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
  specialize h d hd n
  simp [h₁, h₂] at h
  rw [←AState.aPos_eq_of_tr h₂]
  choose a₁ ha₁ h using h
  specialize h d hd 0
  simp at h
  exact h.1

-- #check 0 #exit

theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
(h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
  use aFresh s fsp
  
  -- apply State.fresh1_of_alt
  -- use inferInstance
  -- intro d hd n
  -- 
  -- replace h := AState.aHwsDisj_insert_one_aPos h
  -- 
  -- induction n
  -- ·
  --   simp
  -- nm n ih
  -- 
  -- choose s₁ h₁ h₂ using ih
  -- simp [Nat.add_one_mul, h₁]
  -- 
  -- have hs₁ := AState.of_simulate_mul_two_eq' h₁
  -- 
  -- generalize h₃ : (fsp.insert 1 s.aPos |>.offset (n * 2) |>.insertSet 0 #
  --   s.aVisited s₁ |>.toSet.erase s.aPos) = fsp₁ at h₂
  -- 
  -- replace h₂ := AState.aHwsDisj_insert_one_aPos h₂
  -- choose a ha h₂ using h₂
  -- 
  -- obtain ⟨s₂, h₄, h₅⟩ : ∃ s₂, sys.tr s₁ (aFresh s fsp |>.f s₁) = some s₂ ∧ aFreshCnd s fsp s₂
  -- ·
  --   unfold aFresh
  --   apply exi_aSeek_tr
  --   
  --   -- choose s₂ h₄ h₅ using h₂ default inferInstance 1
  --   -- 
  --   -- simp at h₄
  --   -- use a.f s₁, s₂, h₄
  --   -- 
  --   -- -- specialize h₂ d₁ hd₁ (k + 1)
  --   -- -- simp_rw [sys.simulate_succ_full'] at h₂
  --   -- -- simp [h₄] at h₂
  --   -- -- choose s₃ h₂ h₆ using h₂
  --   -- -- use s₃, h₂
  --   -- -- 
  --   -- -- -- cases k
  --   -- -- -- ·
  --   -- -- --   simp at h₆
  --   -- -- --   simp [FSP.hasLe, FSP.insertSet]
  --   -- -- --   split
  --   -- -- 
  --   -- -- -- simp [h₄] at h₂
  --   -- -- -- simp [FSP.hasLe, FSP.insert, FSP.insertSet] at h₂ h₅
  --   -- -- -- specialize h₂ 1
  --   -- -- -- simp [←h₃, FSP.insert, FSP.insertSet] at h₂
  --   -- -- 
  --   -- -- simp [FSP.hasLe]
  --   -- -- intro c hc
  --   -- -- simp [FSP.insertSet]
  --   -- -- 
  --   -- -- have h₇ : s₃.aPos ∉ (fsp.offset # s₂.diff s).get c
  --   -- 
  --   -- unfold aFreshCnd
  --   -- rw [State.diff, length_hist_eq_of_tr h₄, State.length_hist_eq_of_simulate_eq h₁]
  --   -- dsimp
  --   -- rw [show s.hist.length + n * 2 + 1 - s.hist.length = n * 2 + 1 by omega]
  --   -- rw [AState.aVisited_eq_of_tr h₄ # sys.reachable_of_simulate_eq h₁]
  --   -- 
  --   -- use a, ha
  --   -- intro d₁ hd₁ k
  --   -- specialize h₂ d₁ hd₁ (k + 1)
  --   -- simp only [sys.simulate_succ_full'] at h₂
  --   -- obtain ⟨s₃, ⟨s₂', H₁, H₂⟩, H₃⟩ := h₂
  --   -- simp at H₁
  --   -- 
  --   -- simp [h₄] at H₁; subst H₁
  --   -- use s₃, H₂
  --   -- 
  --   -- rw [←AState.aPos_eq_of_tr h₄]
  --   -- rw [FSP.offset_succ']
  --   -- 
  --   -- clear h₅
  --   -- 
  --   -- cases n
  --   -- ·
  --   --   simp at h₁
  --   --   subst h₁
  --   --   simp at h₃ H₃ ⊢
  --   --   subst h₃
  --   --   simp at H₃
  --   -- 
  --   -- #check 0 #exit
  --   -- 
  --   -- simp [FSP.hasLe] at H₃ ⊢
  --   -- 
  --   -- rw [FSP.offset_succ']
  --   -- 
  --   -- simp [FSP.hasLe, FSP.insert, FSP.insertSet] at H₃ h₅ ⊢
  --   -- intro c hc
  --   -- specialize H₃ (c + 1) (by omega)
  --   -- simp at H₃
  --   -- split_ifs at H₃ ⊢ with H₄
  --   -- ·
  --   --   subst H₄
  --   --   simp at H₃ ⊢
  --   --   rcases H₃ with ⟨H₃, H₄⟩
  --   --   split_ands
  --   --   ·
  --   --     by_contra! H₅
  --   --     sorry
  --   --   ·
  --   --     sorry
  --   --   ·
  --   --     sorry
  --   -- ·
  --   --   sorry
  --   
  --   sorry
  -- 
  -- simp [h₄]
  -- unfold aFreshCnd at h₅
  -- 
  -- -- rw [State.diff, length_hist_eq_of_tr h₄, State.length_hist_eq_of_simulate_eq h₁] at h₅
  -- -- dsimp at h₅
  -- -- rw [show s.hist.length + n * 2 + 1 - s.hist.length = n * 2 + 1 by omega] at h₅
  -- -- rw [AState.aVisited_eq_of_tr h₄ # sys.reachable_of_simulate_eq h₁] at h₅
  -- 
  -- sorry
  
  sorry