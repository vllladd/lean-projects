import AP.AP.Determinacy

namespace AP

@[ext]
structure Defense : Type where
  cnd : State → Prop
  ps : Set PointZ
  f : State → Option PointZ

def Defense.st (dse : Defense) (d : DStrat) : DStrat :=
  .mk # λ s => dse.f s |>.getD (d.f s)

class Defense.WF (dse : Defense) : Prop where
  h : ∀ s [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF], ∀ (d : DStrat) [d.WF] n,
    (sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps

-----

theorem Defense.wf_def {dse : Defense} :
dse.WF ↔ ∀ s [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF], ∀ (d : DStrat) [d.WF] n,
(sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

instance : Inhabited Defense :=
  ⟨{cnd := λ _ => True, ps := ∅, f := λ _ => none}⟩

@[simp]
theorem Defense.default_eq : (default : Defense) =
{cnd := λ _ => True, ps := ∅, f := λ _ => none} := rfl

instance : Defense.WF default := ⟨by simp⟩