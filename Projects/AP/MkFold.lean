import Projects.Dir
import Projects.AP.King
import Projects.AP.Symmetry
import Projects.AP.Defense.Basic

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
[hs : sys.WF s] [hd : d.WF] (h₀ : p s z)
(h₁ : ∀ sa [AState sa] acc, sys.Reachable s sa → p sa acc →
∃ sd, sys.tr sa (fa sa acc).1 = some sd ∧ p sd (fa sa acc).2)
(h₂ : ∀ sd [DState sd] sa [AState sa] p₁ acc, sys.Reachable s sd →
sys.tr sd p₁ = some sa → p sd acc →  p sa (fd sd p₁ acc)) :
∃ s₁ acc, sys.simulate (Strat.f ⟨AStrat.mkFold s z fa fd, d⟩) s n =
(s₁, 0) ∧ p s₁ acc := by
  induction n generalizing s z; simp; use z; nm n ih
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · have h₁' := h₁
    specialize h₁ s z (by rfl) h₀
    obtain ⟨s', h₁, h₃⟩ := h₁
    have hs' := sys.wf_of_tr h₁
    specialize ih h₃ _ _
    · intro sa hsa acc H H₁; apply h₁'
      · exact System.Reachable.step h₁ H
      · exact H₁
    · intro sd hsd sa hsa p₁ acc H H₁ H₂; apply h₂
      · exact System.Reachable.step h₁ H
      · exact H₁
      · exact H₂
    obtain ⟨s₁, acc, H₁, H₂⟩ := ih
    use s₁, acc
    refine ⟨?_, H₂⟩
    simp only [System.simulate_succ_full']
    simp [aStrat_mkFold_apply_a # sys.validTr_of_eq_some h₁, h₁]
    convert H₁ using 1; symm; clear H₁ H₂
    apply simulate_congr _ (by simp)
    intro k hk b hb h₄ h₅ h₆
    apply hs.aStrat_mkFold_eq_of_tr h₁; grind
  · obtain ⟨s', h₃⟩ := d.validTr s
    have hs' := AState.of_tr h₃
    have h₂' := h₂
    specialize h₂ s s' (d.f s) z (by rfl) h₃ h₀
    specialize ih h₂ _ _
    · intro sa hsa acc H H₁; apply h₁
      · exact System.Reachable.step h₃ H
      · exact H₁
    · intro sd hsd sa hsa p₁ acc H H₁ H₂; apply h₂'
      · exact System.Reachable.step h₃ H
      · exact H₁
      · exact H₂
    obtain ⟨s₁, acc, H₁, H₂⟩ := ih
    use s₁, acc
    refine ⟨?_, H₂⟩
    simp only [System.simulate_succ_full']
    simp [h₃]
    convert H₁ using 1; symm; clear H₁ H₂
    apply simulate_congr _ (by simp)
    intro k hk b hb h₄ h₅ h₆
    apply hs.aStrat_mkFold_eq_of_tr h₃; grind