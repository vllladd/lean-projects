import AP.AP.Determinacy

namespace AP

def aMimic (st : Strat) (s s' : State) : AStrat := .mk # λ sa => some #
  let n := sa.hist.length - s'.hist.length
  let r := sys.simulate st.f s n
  st.a.f r.1

def dMimic (st : Strat) (s s' : State) : DStrat := .mk # λ sd => some #
  let n := sd.hist.length - s'.hist.length
  let r := sys.simulate st.f s n
  st.d.f r.1

instance {st s s'} : (aMimic st s s').WF := by unfold aMimic; infer_instance
instance {st s s'} : (dMimic st s s').WF := by unfold dMimic; infer_instance

theorem aMimic_apply_eq_of {st st' : Strat} {s₀ s₁ s₂ n} [hs₀ : sys.WF s₀]
(h₁ : sys.simulate st.f s₀ n = (s₁, 0)) (h₂ : sys.simulate st'.f s₀ n = (s₂, 0))
(h₃ : sys.validTr s₂ (st.a.f s₁)) : (aMimic st s₀ s₀).f s₂ = st.a.f s₁ := by
  simp [aMimic, mk_strat_fn, guard, h₁, h₃, length_hist_sub_eq_of_simulate h₂]

theorem dMimic_apply_eq_of {st st' : Strat} {s₀ s₁ s₂ n} [hs₀ : sys.WF s₀]
(h₁ : sys.simulate st.f s₀ n = (s₁, 0)) (h₂ : sys.simulate st'.f s₀ n = (s₂, 0))
(h₃ : sys.validTr s₂ (st.d.f s₁)) : (dMimic st s₀ s₀).f s₂ = st.d.f s₁ := by
  simp [dMimic, mk_strat_fn, guard, h₁, h₃, length_hist_sub_eq_of_simulate h₂]

theorem State.aHws_of_rel {s s'} {r : State → State → Prop}
[hs : sys.WF s] [hs' : sys.WF s'] (h₁ : s.aHws) (ht : s.aTurn = s'.aTurn) (h₂ : r s s')
(h₃ : ∀ {sa sa' sd p} [AState sa] [AState sa'] [DState sd], r sa sa' →
sys.tr sa p = some sd → ∃ sd', sys.tr sa' p = some sd' ∧ r sd sd')
(h₄ : ∀ {sd sd' sa' p} [DState sd] [DState sd'] [AState sa'], r sd sd' →
sys.tr sd' p = some sa' → ∃ sa, sys.tr sd p = some sa ∧ r sa sa') : s'.aHws := by
  apply aHws_of_ind (p := (λ s' => ∃ s,
    sys.WF s ∧ s.aHws ∧ s.aTurn = s'.aTurn ∧ r s s'))
  · use s
  · clear! s s'
    rintro sa hsa ⟨s, hs, H, H₁, H₃⟩
    simp at H₁
    replace hs : AState s; use hs
    obtain ⟨p, sd, H₂, Hs⟩ := hs.aHws_iff_tr.mp H
    have H₄ := DState.of_tr H₂
    specialize h₃ H₃ H₂
    obtain ⟨sd', H₅, H₆⟩ := h₃
    use p, sd', H₅
    have H₇ := DState.of_tr H₅
    use sd
    simp [Hs, H₆]
  · clear! s s'
    rintro sd' hsd' pd sa' ⟨sd, h₁, h₂, h₅, h₆⟩ h₇
    have hsa' := AState.of_tr h₇
    simp at h₅ ⊢
    replace h₁ : DState sd; use h₁
    specialize h₄ h₆ h₇
    obtain ⟨sa, H₁, H₂⟩ := h₄
    have H₃ := AState.of_tr H₁
    use sa
    rw [h₁.aHws_iff_tr] at h₂
    specialize h₂ _ _ H₁
    simpa [-AState.hasTr_iff, H₂]

theorem State.aHws_of_fn' {s} {f : State → State}
[hs : sys.WF s] [hs' : sys.WF (f s)] (h₁ : s.aHws) (ht : s.aTurn = (f s).aTurn)
(h₂ : ∀ {sa sa' sd p} [AState sa] [AState sa'] [DState sd], f sa = sa' →
sys.tr sa p = some sd → ∃ sd', sys.tr sa' p = some sd' ∧ f sd = sd')
(h₃ : ∀ {sd sd' sa' p} [DState sd] [DState sd'] [AState sa'], f sd = sd' →
sys.tr sd' p = some sa' → ∃ sa, sys.tr sd p = some sa ∧ f sa = sa') : (f s).aHws :=
  aHws_of_rel (r := (f · = ·)) h₁ ht rfl h₂ h₃

theorem State.aHws_of_fn {s} {f : State → State}
[hs : sys.WF s] [hs' : sys.WF (f s)] (h₁ : s.aHws) (ht : s.aTurn = (f s).aTurn)
(h₂ : ∀ {sa sd p} [AState sa] [AState (f sa)] [DState sd],
sys.tr sa p = some sd → sys.tr (f sa) p = some (f sd))
(h₃ : ∀ {sd sa' p} [DState sd] [DState (f sd)] [AState sa'],
sys.tr (f sd) p = some sa' → ∃ sa, sys.tr sd p = some sa ∧ f sa = sa') : (f s).aHws := by
  apply s.aHws_of_fn' h₁ ht
  · rintro sa sa' sd p hsa hsa' hsd rfl h₄; simp [-AState.tr_eq_some_iff]; exact h₂ h₄
  · rintro sd sd' sa' p hsd hsd' hsa' rfl h₄; exact h₃ h₄