import AP.AP.King

namespace AP

variable {α : Type*}

@[simp]
def AStrat.mkFold' (s : State) (z : α) (fa : State → α → PointZ × α)
(fd : State → PointZ → α → α) : List PointZ → Option PointZ
| [] => some # fa s z |>.1
| p :: ps => do
  let z₁ := if s.aTurn then fa s z |>.2 else fd s p z
  let s₁ ← sys.tr s p
  mkFold' s₁ z₁ fa fd ps

def AStrat.mkFold (s₀ : State) (z : α) (fa : State → α → PointZ × α)
(fd : State → PointZ → α → α) : AStrat := mk # λ s =>
  AStrat.mkFold' s₀ z fa fd # s.hist.reverse.drop s₀.hist.length

@[simp]
def DStrat.mkFold' (s : State) (z : α) (fa : State → PointZ → α → α)
(fd : State → α → PointZ × α) : List PointZ → Option PointZ
| [] => some # fd s z |>.1
| p :: ps => do
  let z₁ := if s.aTurn then fa s p z else fd s z |>.2
  let s₁ ← sys.tr s p
  mkFold' s₁ z₁ fa fd ps

def DStrat.mkFold (s₀ : State) (z : α) (fa : State → PointZ → α → α)
(fd : State → α → PointZ × α) : DStrat := mk # λ s =>
  DStrat.mkFold' s₀ z fa fd # s.hist.reverse.drop s₀.hist.length

-----

@[simp]
instance {z : α} {s₀ fa fd} : AStrat.mkFold s₀ z fa fd |>.WF := by
  unfold AStrat.mkFold; infer_instance

@[simp]
instance {z : α} {s₀ fa fd} : DStrat.mkFold s₀ z fa fd |>.WF := by
  unfold DStrat.mkFold; infer_instance

theorem aStrat_mkFold_apply_a {s} {z : α} {fa fd} (h : sys.validTr s (fa s z).1) :
(AStrat.mkFold s z fa fd).f s = (fa s z).1 := by
  simp [AStrat.mkFold, AStrat.mkFold', h]

theorem AState.aStrat_mkFold_eq_of_tr {s s' s₁} {z : α} {fa fd} [hs : AState s]
(h₁ : sys.tr s (fa s z).1 = some s') (h₂ : sys.Reachable s' s₁) :
(AStrat.mkFold s' (fa s z).2 fa fd).f s₁ = (AStrat.mkFold s z fa fd).f s₁ := by
  simp [AStrat.mkFold, hist_eq_of_tr h₁]
  congr 1; ext p :1; simp; intro h₃
  rw [sys.reachable_iff_exi_trs] at h₂
  obtain ⟨ps, h₂⟩ := h₂
  have h₄ : s₁.hist = ps.reverse ++ (fa s z).1 :: s.hist
  · simp [hist_eq_of_trs h₂, hist_eq_of_tr h₁]
  simp [h₄]; simp_all only [Option.some.injEq, exists_eq_left']

theorem DState.aStrat_mkFold_eq_of_tr {s s' s₁ p} {z : α} {fa fd} [hs : DState s]
(h₁ : sys.tr s p = some s') (h₂ : sys.Reachable s' s₁) :
(AStrat.mkFold s' (fd s p z) fa fd).f s₁ = (AStrat.mkFold s z fa fd).f s₁ := by
  simp [AStrat.mkFold, hist_eq_of_tr h₁]
  congr 1; ext p₁ :1; simp; intro h₃
  rw [sys.reachable_iff_exi_trs] at h₂
  obtain ⟨ps, h₂⟩ := h₂
  have h₄ : s₁.hist = ps.reverse ++ p :: s.hist
  · simp [hist_eq_of_trs h₂, hist_eq_of_tr h₁]
  simp [h₄]; simp_all only [Option.some.injEq, exists_eq_left']

theorem AStrat.mkFold_ind {s z fa fd n} {d : DStrat} {p : State → α → Prop}
[hs : sys.WF s] [hd : d.WF] (h₀ : p s z) (h₁ : ∀ sa [AState sa] acc, p sa acc →
∃ sd, sys.tr sa (fa sa acc).1 = some sd ∧ p sd (fa sa acc).2)
(h₂ : ∀ sd [DState sd] sa [AState sa] p₁ acc, sys.tr sd p₁ = some sa → p sd acc → 
p sa (fd sd p₁ acc)) : ∃ s₁ acc, sys.simulate (Strat.f ⟨AStrat.mkFold s z fa fd, d⟩)
s n = (s₁, 0) ∧ p s₁ acc := by
  induction n generalizing s z; simp; use z; nm n ih
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · specialize h₁ s z h₀
    obtain ⟨s', h₁, h₃⟩ := h₁
    have hs' := sys.wf_of_tr h₁
    specialize ih h₃
    obtain ⟨s₁, acc, H₁, H₂⟩ := ih
    use s₁, acc
    refine ⟨?_, H₂⟩
    simp [aStrat_mkFold_apply_a # sys.validTr_of_eq_some h₁, h₁]
    convert H₁ using 1; symm; clear H₁ H₂
    apply simulate_congr _ (by simp)
    intro k hk b hb h₄ h₅ h₆
    apply hs.aStrat_mkFold_eq_of_tr h₁
    exact sys.reachable_of_simulate_full h₄
  · obtain ⟨s', h₃⟩ := d.validTr s
    have hs' := AState.of_tr h₃
    specialize h₂ s s' (d.f s) z h₃ h₀
    specialize ih h₂
    obtain ⟨s₁, acc, H₁, H₂⟩ := ih
    use s₁, acc
    refine ⟨?_, H₂⟩
    simp [h₃]
    convert H₁ using 1; symm; clear H₁ H₂
    apply simulate_congr _ (by simp)
    intro k hk b hb h₄ h₅ h₆
    apply hs.aStrat_mkFold_eq_of_tr h₃
    exact sys.reachable_of_simulate_full h₄

theorem State.size_taken_eq_ite_of_tr {s s' p} [hs : sys.WF s] (h : sys.tr s p = some s') :
s'.taken.size = s.taken.size + if s.aTurn then 0 else 1 := by
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · simp [hs.taken_eq_of_tr h]
  simp; simp [hs.tr_eq_some_iff] at h
  rcases h with ⟨⟨h₁, h₂⟩, rfl⟩
  simp [Set'.size_insert h₂]

theorem State.length_hist_eq_size_taken_mul_two_add_ite {s} [hs : sys.WF s] :
s.hist.length = s.taken.size * 2 + if s.aTurn then 0 else 1 := by
  obtain ⟨ps, h₁⟩ := wf_iff.mp hs
  induction ps using List.reverseRecOn generalizing s
  · simp at h₁; rw [←h₁]; simp
  nm ps p ih
  simp at h₁
  obtain ⟨s', h₁, h₂⟩ := h₁
  have h₃ := sys.reachable_of_trs h₁
  dsimp at h₃
  have hs' := sys.wf_of_reachable h₃
  specialize @ih s' _
  simp [pw_eq_of_reachable h₃, aPos₀_eq_of_reachable h₃] at ih
  specialize ih h₁
  simp [hist_eq_of_tr h₂, ih]; clear ih
  rw [size_taken_eq_ite_of_tr h₂, aTurn_eq_of_tr h₂]
  simp; split_ifs <;> ring_nf

theorem State.length_hist_le_size_taken_mul_two_add_one {s} [hs : sys.WF s] :
s.hist.length ≤ s.taken.size * 2 + 1 := by
  simp [length_hist_eq_size_taken_mul_two_add_ite]

theorem State.size_taken_mul_two_le_length_hist {s} [hs : sys.WF s] :
s.taken.size * 2 ≤ s.hist.length := by
  simp [length_hist_eq_size_taken_mul_two_add_ite]

theorem State.length_hist_le_two_of_pw_eq_zero {s} [hs : sys.WF s]
(h : s.pw = 0) : s.hist.length ≤ 2 := by
  obtain ⟨ps, h₁⟩ := wf_iff.mp hs
  cases ps; simp at h₁; rw [←h₁]; simp
  nm p₁ ps; simp at h₁; split at h₁; simp at h₁; nm x s₁ h₂; clear x
  cases ps; simp at h₁; subst h₁; simp [hist_eq_of_tr h₂]
  nm p₂ ps; simp at h₁; split at h₁; simp at h₁; nm x s₂ h₃; clear x
  have hs₁ : AState s₁; use sys.wf_of_tr h₂; simp [aTurn_eq_of_tr h₂]
  simp [hs₁.tr_eq_some_iff] at h₃
  rcases h₃ with ⟨⟨h₃, h₄, h₅⟩, rfl⟩
  simp [pw_eq_of_tr h₂, h, ne_symm' h₃] at h₅

theorem State.size_taken_le_one_of_pw_eq_zero {s} [hs : sys.WF s]
(h : s.pw = 0) : s.taken.size ≤ 1 := by
  by_contra! h₁; replace h₂ := s.size_taken_mul_two_le_length_hist
  replace h₂ : 3 ≤ s.hist.length; linarith
  linarith [length_hist_le_two_of_pw_eq_zero h]

-- #check 0 #exit

theorem State.exi_wf (pw : ℕ) (aTurn : Bool) (aPos : PointZ) (taken : Set' PointZ)
(h₀ : taken = ∅ → aTurn = false) (h : pw = 0 → taken.size ≤ 1) (ha : aPos ∉ taken) :
∃ s, sys.WF s ∧ s.pw = pw ∧ s.aTurn = aTurn ∧ s.aPos = aPos ∧ s.taken = taken := by
  rw [imp_iff_or_not] at h
  rcases h with h | h
  · rw [Nat.le_one_iff] at h
    rcases h with h | h
    · simp at h
      subst h
      specialize h₀ rfl
      subst h₀
      use initState pw aPos
      simp
    obtain ⟨p, hp⟩ : ∃ p, p ∈ taken
    · by_contra! h₁
      rw [←Set'.eq_empty_iff] at h₁
      simp [h₁] at h
    sorry
  --   obtain ⟨s, h₁⟩ : ∃ s, sys.tr (initState pw aPos) p = some s
  --   · simp [DState.tr_eq_some_iff]; rintro rfl; contradiction
  --   use s, sys.wf_of_tr h₁, pw_eq_of_tr h₁
  -- sorry
  sorry

-- #check 0 #exit

theorem State.exi_erase_taken {s p} [hs : sys.WF s] :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken.erase p := by
  -- by_cases hp : p ∉ s.taken
  -- · rw [Set'.erase_eq_of_not_mem hp]; use s
  -- push_neg at hp
  -- by_cases h : s.pw = 0
  -- · have h₁ := size_taken_le_one_of_pw_eq_zero h
  --   apply exi_wf; rintro -; rw [Set'.size_erase hp]; omega
  -- apply exi_wf; simp [h]
  sorry

theorem State.exi_taken_diff {s ps} [hs : sys.WF s] :
∃ s', sys.WF s' ∧ s'.pw = s.pw ∧ s'.aTurn = s.aTurn ∧ s'.aPos = s.aPos ∧
s'.taken = s.taken \ ps := by
  -- revert s; apply ps.ind;
  -- · intro s hs; simp; use s
  -- clear ps; intro ps p hp ih s hs
  -- specialize @ih s _; obtain ⟨s₁, hs₁, hpw, ht, hpa, ih⟩ := ih
  -- have h₁ : s.taken \ ps.insert p = s₁.taken.erase p
  -- · ext p₁; rw [ih]; simp; tauto
  -- rw [←hpw, ←ht, ←hpa, h₁]; apply exi_erase_taken
  sorry