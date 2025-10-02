import AP.AP.FSP

namespace AP

def State.aWinsDisj (s : State) (fsp : FSP) (st : Strat) : Prop :=
  ∀ n, ∃ s₁, sys.simulate st.f s n = (s₁, 0) ∧ fsp.hasLe n s₁.aPos

def State.aHwsDisj (s : State) (fsp : FSP) : Prop :=
  ∃ (a : AStrat), a.WF ∧ ∀ (d : DStrat), d.WF → s.aWinsDisj fsp ⟨a, d⟩

theorem AState.tr_of_aHwsDisj {s fsp} [hs : AState s] (h : s.aHwsDisj fsp) :
∃ p s', sys.tr s p = some s' ∧ s'.aHwsDisj fsp.next := by
  obtain ⟨a, Ha, h₁⟩ := h
  use a.f s
  obtain ⟨s', h₂⟩ : ∃ s', sys.tr s (a.f s) = some s'
  · specialize h₁ default inferInstance
    specialize h₁ 1
    simp at h₁
    obtain ⟨s', h₁, -⟩ := h₁
    split at h₁; simp at h₁
    nm x s₁ h₂; use s₁
  use s', h₂
  use a, Ha
  intro d Hd
  intro n
  specialize h₁ d Hd (n + 1)
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  simp [h₂] at h₁; simp; use s₁

theorem DState.tr_of_aHwsDisj {s s' p fsp} [hs : DState s] (h₁ : s.aHwsDisj fsp)
(h₂ : sys.tr s p = some s') : s'.aHwsDisj fsp.next := by
  obtain ⟨a, Ha, h₁⟩ := h₁
  use a, Ha
  intro d Hd n
  specialize h₁ (d.set s p) (d.wf_set_of_tr h₂) (n + 1)
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  use s₁
  simp [h₃]
  clear h₃
  simp [h₂] at h₁
  convert h₁ using 1; symm
  have hs' := sys.wf_of_tr h₂
  apply simulate_set_d_eq_of_length_hist_lt ⟨_, h₂⟩
  exact State.length_hist_lt_of_tr h₂