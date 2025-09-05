import AP.AP.Determinacy

namespace AP

def aMimic (st : Strat) (s₀ : State) : AStrat := .mk' # λ s => some #
  let n := s.hist.length - s₀.hist.length
  let r := sys.simulate st.f s₀ n
  st.a.f r.1

def dMimic (st : Strat) (s₀ : State) : DStrat := .mk' # λ s => some #
  let n := s.hist.length - s₀.hist.length
  let r := sys.simulate st.f s₀ n
  st.d.f r.1

instance {st s₀} : (aMimic st s₀).WF := by unfold aMimic; infer_instance
instance {st s₀} : (dMimic st s₀).WF := by unfold dMimic; infer_instance

theorem aMimic_apply_eq_of {st st' : Strat} {s₀ s₁ s₂ n} [hs₀ : sys.WF s₀]
(h₁ : sys.simulate st.f s₀ n = (s₁, 0)) (h₂ : sys.simulate st'.f s₀ n = (s₂, 0))
(h₃ : sys.validTr s₂ (st.a.f s₁)) : (aMimic st s₀).f s₂ = st.a.f s₁ := by
  simp [aMimic, mk_strat_fn, guard, h₁, h₃, length_hist_sub_eq_of_simulate h₂]

theorem dMimic_apply_eq_of {st st' : Strat} {s₀ s₁ s₂ n} [hs₀ : sys.WF s₀]
(h₁ : sys.simulate st.f s₀ n = (s₁, 0)) (h₂ : sys.simulate st'.f s₀ n = (s₂, 0))
(h₃ : sys.validTr s₂ (st.d.f s₁)) : (dMimic st s₀).f s₂ = st.d.f s₁ := by
  simp [dMimic, mk_strat_fn, guard, h₁, h₃, length_hist_sub_eq_of_simulate h₂]