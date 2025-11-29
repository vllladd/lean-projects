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

def empty : Defense where
  cnd := λ _ => True
  ps := ∅
  f := λ _ => none

instance : EmptyCollection Defense := ⟨empty⟩
instance : Inhabited Defense := ⟨∅⟩

def merge (dse₁ dse₂ : Defense) : Defense where
  cnd := λ s => dse₁.cnd s ∧ dse₂.cnd s
  ps := dse₁.ps ∪ dse₂.ps
  f := λ s => dse₁.f s <|> dse₂.f s

def ofList (ds : List Defense) : Defense :=
  ds.foldr merge ∅

def Compatible' (p : State → Prop) (dse₁ dse₂ : Defense) : Prop :=
  ∀ {s₀} [sys.WF s₀] {s p₁ p₂}, p s₀ → dse₁.cnd s₀ → dse₂.cnd s₀ → sys.Reachable s₀ s →
  dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂

def Compatible (dse₁ dse₂ : Defense) : Prop :=
  Compatible' (λ _ => True) dse₁ dse₂

def CompatibleList' (p : State → Prop) (ds : List Defense) : Prop :=
  ∀ {s₀} [sys.WF s₀] {s p₁ p₂ d₁ d₂}, p s₀ → (∀ d ∈ ds, d.cnd s₀) → sys.Reachable s₀ s →
  d₁ ∈ ds → d₂ ∈ ds → d₁.f s = some p₁ → d₂.f s = some p₂ → p₁ = p₂

def CompatibleList (ds : List Defense) : Prop :=
  CompatibleList' (λ _ => True) ds

def WF' (p : State → Prop) (dse : Defense) : Prop :=
  ∀ {s} [sys.WF s], p s → dse.cnd s → ∀ (a : AStrat) [a.WF],
  ∀ (d : DStrat) [d.WF] n, (sys.simulate (Strat.f ⟨a, dse.st d⟩) s n).1.aPos ∉ dse.ps

-- def setCnd (d : Defense) (cnd : State → Prop) : Defense :=
--   {d with cnd := cnd}
-- 
-- def accCndList (d : Defense) (ds : List Defense) : List Defense :=
--   d.setCnd (∀ d₁, d₁ = d ∨ d₁ ∈ ds → d₁.cnd ·) :: ds.map (·.setCnd λ _ => True)