import AP.AP.FSP

namespace AP

def State.aWinsDisj (s : State) (fsp : FSP) (st : Strat) : Prop :=
  ∀ n, ∃ s₁, sys.simulate st.f s n = (s₁, 0) ∧ ¬fsp.hasLe n s₁.aPos

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

theorem State.aWinsDisj_iff {s : State} {fsp} {st : Strat} :
s.aWinsDisj fsp st ↔ s.aWins st ∧ ∀ n, ¬fsp.hasLe n (sys.simulate st.f s n).1.aPos := by
  constructor
  · intro h
    constructor
    · intro n
      specialize h n
      aesop
    intro n
    specialize h n
    aesop
  rintro ⟨h₁, h₂⟩
  intro n
  simp [Prod.ext_iff]
  specialize h₁ n
  aesop

-- #check 0 #exit

theorem State.aHwsDisj_insert {s fsp p} [hs : sys.WF s]
(h₁ : s.aHwsDisj fsp) : ∃ n, s.aHwsDisj (fsp.insert n p) := by
  unfold aHwsDisj aWinsDisj at h₁ ⊢
  by_contra! h₃
  replace h₃ : ∀ (a : AStrat) [a.WF] n, ∃ (d : DStrat), d.WF ∧ ∃ k, n ≤ k ∧
    ∀ s₁ r, sys.simulate (Strat.f ⟨a, d⟩) s k = ⟨s₁, r⟩ →
    r ≠ 0 ∨ ¬(fsp.insert n p).hasLe k s₁.aPos
  · intro a Ha n
    sorry
  sorry

-- #check 0 #exit

theorem State.aHwsDosj_insertSet_of_le {s : State} {fsp : FSP} {m n ps}
(h₁ : s.aHwsDisj (fsp.insertSet m ps)) (h₂ : m ≤ n) : s.aHwsDisj (fsp.insertSet n ps) := by
  obtain ⟨a, Ha, h₁⟩ := h₁
  use a, Ha
  intro d Hd
  specialize h₁ d Hd
  rw [aWinsDisj_iff] at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  use h₁; clear h₁
  intro k
  specialize h₃ k
  generalize (sys.simulate (Strat.f ⟨a, d⟩) s k).1 = s₁ at h₃ ⊢
  contrapose! h₃
  exact fsp.hasLe_insertSet_of_le_and_le h₃ h₂

theorem State.aHwsDosj_insert_of_le {s : State} {fsp : FSP} {m n p}
(h₁ : s.aHwsDisj (fsp.insert m p)) (h₂ : m ≤ n) : s.aHwsDisj (fsp.insert n p) :=
  aHwsDosj_insertSet_of_le h₁ h₂

theorem State.aHwsDisj_insertSet' {s fsp}  {ps : Set' PointZ} [hs : sys.WF s]
(h₁ : s.aHwsDisj fsp) : ∃ n, s.aHwsDisj (fsp.insertSet n ps.toSet) := by
  induction ps using Set'.ind; simpa; clear h₁
  nm ps p hp ih
  obtain ⟨n, ih⟩ := ih
  obtain ⟨m, h₂⟩ := s.aHwsDisj_insert ih (p := p)
  use max n m; simp
  rw [fsp.insertSet_set_insert]
  apply aHwsDosj_insert_of_le _ # Nat.le_max_right n m
  rw [fsp.insertSet_insert_comm] at h₂ ⊢
  exact aHwsDosj_insertSet_of_le h₂ # Nat.le_max_left n m

theorem State.aHwsDisj_insertSet_of_finite {s fsp ps} [hs : sys.WF s]
(h₁ : s.aHwsDisj fsp) (h₂ : ps.Finite) : ∃ n, s.aHwsDisj (fsp.insertSet n ps) := by
  have h₃ := s.aHwsDisj_insertSet' (ps := Set'.ofSet ps) h₁
  rwa [Set'.toSet_ofSet h₂] at h₃