import Projects.AP.Moves

namespace AP

open Classical in noncomputable
def State.aProx (s s₁ : State) : Set' PointZ :=
  Set'.ofSet # Set.ofPred λ p => sys.WF s ∧ sys.Reachable s s₁ ∧
  (∃ ps s₂, ps <+: s₁.diffTrs s ∧ sys.trs s ps = (s₂, []) ∧ s₂.aPos = p) ∧
  ∃ ps p₁ s₂, AState s₂ ∧ ps ++ [p₁] <+: s₁.diffTrs s ∧ sys.trs s ps = (s₂, []) ∧
    sys.validTr s₂ p ∧ p ≠ p₁

def State.aProx' (s s₁ : State) : Set' PointZ :=
  s.aNbhdsIcoPrev s₁

-----

-- theorem State.aux₁ {s s₁ : State} [hs : sys.WF s] {p} :
-- p ∈ s.aNbhdsIcoPrev s₁ ↔ sys.WF s ∧ sys.Reachable s s₁ ∧
-- (∃ ps, ps <+: s₁.diffTrs s ∧ ∃ x, sys.trs s ps = (x, []) ∧ x.aPos = p) ∧
-- ∃ ps p₁ s₂, AState s₂ ∧ ps ++ [p₁] <+: s₁.diffTrs s ∧ sys.trs s ps = (s₂, []) ∧
-- sys.validTr s₂ p ∧ ¬p = p₁ := by
--   simp [aNbhdsIcoPrev, hs]
--   constructor
--   ·
--     rintro ⟨p₁, h₁, h₂⟩
--     rw [mem_aVisitedIcoPrev_iff_exi_aSimStatesIco] at h₁
-- 
-- -- #check 0 #exit
-- 
-- theorem State.aPox_eq_aPox' {s s₁ : State} [hs : sys.WF s] : s.aProx s₁ = s.aProx' s₁ := by
--   unfold aProx aProx'
--   ext p
--   rw [Set'.mem_ofSet]
--   rotate_left
--   ·
--     rw [Set.finite_iff_exi_finset]
--     use s.aNbhdsIcoPrev s₁ |>.toFinset
--     clear p
--     ext p
--     simp
--     exact aux₁
--   simp
--   exact aux₁.symm