import AP.AP.Defense.Defs

namespace AP.Defense

variable {dse : Defense}
variable [wf : dse.WF]
omit wf

theorem wf_def : dse.WF ↔
∀ s [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF], ∀ (d : DStrat) [d.WF] n,
(sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps := ⟨(·.1), (⟨·⟩)⟩

instance : Inhabited Defense :=
  ⟨{cnd := λ _ => True, ps := ∅, f := λ _ => none}⟩

@[simp]
theorem default_def : (default : Defense) =
{cnd := λ _ => True, ps := ∅, f := λ _ => none} := rfl

@[simp] instance : WF default := ⟨by simp⟩
@[simp] instance {d} : (dse.st d).WF := by unfold st; infer_instance