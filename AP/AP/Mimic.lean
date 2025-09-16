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

theorem State.aHws_of_mimic {s s'} {r : State → State → Prop}
[hs : sys.WF s] [hs' : sys.WF s'] (h₁ : s.aHws) (ht : s.aTurn = s'.aTurn) (h₂ : r s s')
(h₃ : ∀ {s s' s₁ p} [AState s] [AState s'] [DState s₁], r s s' →
sys.tr s p = some s₁ → ∃ s₁', sys.tr s' p = some s₁' ∧ r s₁ s₁')
(h₄ : ∀ {s s' s₁ p} [DState s] [DState s'] [AState s₁], r s s' →
sys.tr s p = some s₁ → ∃ s₁', sys.tr s' p = some s₁' ∧ r s₁ s₁') : s'.aHws := by
  -- apply aHws_of_ind (p := (λ s' => ∃ s, sys.WF s ∧ s.aTurn = s'.aTurn ∧ sys.hasTr s ∧ r s s'))
  -- · use s, hs, ht, hasTr_of_aHws h₁
  -- · clear! s s'
  --   rintro sa hsa ⟨s, hs, H₁, H₂, H₃⟩
  --   simp at H₁
  --   replace hs : AState s; use hs
  --   obtain ⟨p, sd, H₂⟩ := H₂
  --   have H₄ := DState.of_tr H₂
  --   specialize h₃ H₃ H₂
  --   obtain ⟨sd', H₅, H₆⟩ := h₃
  --   use p, sd', H₅
  --   have H₇ := DState.of_tr H₅
  --   use sd; simpa
  -- · clear! s s'
  --   rintro sd' hsd pd sa' ⟨sd, hs, H₁, H₂, H₃⟩ H₄
  --   simp at H₁
  --   replace hs : DState sd; use hs
  --   have H₅ := AState.of_tr H₄
  --   obtain ⟨p, sa, H₂⟩ := H₂
  --   have H₆ := AState.of_tr H₂
  --   simp
  --   specialize h₄ H₃ H₂
  --   specialize @h₄ s sd s' p _ _ _ H₃ H₂
  --   obtain ⟨s₂', H₇, H₈⟩ := h₄
  --   have H₉ := AState.of_tr H₇
  --   -- simp at H₁
  --   -- replace hs : AState s; use hs
  --   -- obtain ⟨p, sd, H₂⟩ := H₂
  --   -- have H₄ := DState.of_tr H₂
  --   -- specialize h₃ H₃ H₂
  --   -- obtain ⟨sd', H₅, H₆⟩ := h₃
  --   -- use p, sd', H₅
  --   -- have H₇ := DState.of_tr H₅
  --   -- use sd; simpa
  
  -- obtain ⟨a, Ha, h₁⟩ := h₁
  -- rw [←not_dHws_iff, dHws]; push_neg; simp
  -- intro d Hd
  -- specialize h₁ (dMimic ⟨a, d⟩ s s') inferInstance
  -- use aMimic ⟨a, d⟩ s s', inferInstance
  -- intro n
  -- specialize h₁ n
  -- apply sys.simulate_congr_rel' (f := Strat.f ⟨a, d⟩)
  --   (g := Strat.f ⟨aMimic ⟨a, d⟩ s s', dMimic ⟨a, d⟩ s s'⟩)
  --   (r := λ s s' => s.aTurn = s'.aTurn ∧ r s s') h₁ ⟨ht, h₂⟩
  -- · rintro k hk b₁ b₂ c₁ hb₁ hb₂ ⟨H₁, H₂⟩ H₃
  --   have Hb₁ := sys.wf_of_simulate_eq hb₁
  --   have Hb₂ := sys.wf_of_simulate_eq hb₂
  --   dsimp at Hb₁ Hb₂
  --   
  --   have h₅ : b₂.hist.length - s'.hist.length = k
  --   · sorry
  --   
  --   replace Hb₁ := b₁.aState_or_dState
  --   rcases Hb₁ with Hb₁ | Hb₁
  --   · replace Hb₂ : AState b₂
  --     · use Hb₂; simp [←H₁]
  --     have Hc₁ := DState.of_tr H₃
  --     specialize h₃ H₂ H₃
  --     obtain ⟨c₂, H₄, H₅⟩ := h₃
  --     use c₂
  --     simp [-AState.tr_eq_some_iff] at H₄
  --     have Hc₂ := DState.of_tr H₄
  --     simpa [-AState.tr_eq_some_iff, aMimic, h₅, hb₁, sys.validTr_of_eq_some H₄, H₄]
  --   · replace Hb₂ : DState b₂
  --     · use Hb₂; simp [←H₁]
  --     have Hc₁ := AState.of_tr H₃
  --     simp [-DState.tr_eq_some_iff] at H₃ ⊢
  --     specialize h₄ H₂ H₃
  --     obtain ⟨c₂, H₄, H₅⟩ := h₄
  --     use c₂
  --     simp [-DState.tr_eq_some_iff]
  --     have Hc₂ := AState.of_tr H₄
  
  obtain ⟨a, Ha, h₁⟩ := h₁
  rw [←not_dHws_iff, dHws]; push_neg; simp
  intro d Hd
  sorry