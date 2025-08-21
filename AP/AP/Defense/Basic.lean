import AP.AP.Defense.Defs

namespace AP.Defense

theorem wf_def {dse : Defense} :
dse.WF ↔ ∀ s [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF], ∀ (d : DStrat) [d.WF] n,
(sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

instance : Inhabited Defense :=
  ⟨{cnd := λ _ => True, ps := ∅, f := λ _ => none}⟩

@[simp]
theorem default_eq : (default : Defense) =
{cnd := λ _ => True, ps := ∅, f := λ _ => none} := rfl

instance : WF default := ⟨by simp⟩