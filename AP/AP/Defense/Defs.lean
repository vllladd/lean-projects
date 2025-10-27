import AP.AP.HistBlind

namespace AP

@[ext]
structure Defense : Type where
  cnd : State → Prop
  ps : Set PointZ
  f : State → Option PointZ

namespace Defense

def st (dse : Defense) (d : DStrat) : DStrat :=
  .mk' # λ s => dse.f s |>.getD (d.f s)

-- class ValidTr (dse : Defense) : Prop where
--   valid_tr : ∀ {s} [DState s] {p}, dse.f s = some p → sys.validTr s p
-- 
-- class WF (dse : Defense) extends dse.ValidTr where
--   not_mem_ps : ∀ {s} [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF],
--     ∀ (d : DStrat) [d.WF] n, (sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps

def ValidTr (dse : Defense) : Prop :=
  ∀ {s} [DState s] {p}, dse.f s = some p → sys.validTr s p

class WF (dse : Defense) where
  valid_tr : dse.ValidTr
  not_mem_ps : ∀ {s} [sys.WF s], dse.cnd s → ∀ (a : AStrat) [a.WF],
    ∀ (d : DStrat) [d.WF] n, (sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps

def sym (dse : Defense) (sym : sys.Symmetry) : Defense where
  cnd := λ s => dse.cnd # sym.fs' s
  ps := sym.ft '' dse.ps
  f := λ s => dse.f (sym.fs' s) |>.map sym.ft