import AP.System.Defs

noncomputable section
open scoped Classical

@[simp]
theorem mk_system_s₀ {S T : Type} {f : SystemFn S T} {s₀ : S} :
(mk_system f s₀).s₀ = s₀ := rfl

@[simp]
theorem mk_system_f {S T : Type} {f : SystemFn S T} {s₀ : S} :
(mk_system f s₀).f = mk_system_fn f s₀ := rfl

@[simp]
theorem mk_system_fn_eq_some_iff {S T : Type} {f : SystemFn S T} {s₀ : S} {s t s₁} :
mk_system_fn f s₀ s t = some s₁ ↔
Reachable f s₀ s ∧ Reachable f s₀ s₁ ∧ f s t = some s₁ := by
  unfold mk_system_fn guard
  split_ifs with h₁ <;> simp [h₁]
  by_cases h₂ : f s t = none; simp [h₂]
  obtain ⟨s₁, hs₁⟩ := Option.exists_eq_some_of_ne_none h₂
  simp [hs₁]
  split_ifs with h₃ <;> simp [h₃]
  · rintro rfl
    exact h₃
  rintro h₄ rfl
  contradiction

@[simp]
theorem mk_system_fn_eq_none_iff {S T : Type} {f : SystemFn S T} {s₀ : S} {s t} :
mk_system_fn f s₀ s t = none ↔ ¬Reachable f s₀ s ∨ f s t = none := by
  simp [Option.eq_none_iff_forall_ne_some]
  by_cases h₁ : f s t = none; simp [h₁]
  obtain ⟨s₁, h₂⟩ := Option.exists_eq_some_of_ne_none h₁
  simp [h₂]
  by_cases h₃ : Reachable f s₀ s <;> simp [h₃]
  exact Reachable.h₁ s t s₁ h₃ h₂

@[simp]
theorem reachable_mk_system_fn_iff {S T : Type} {f : SystemFn S T} {s₀ : S} {s} :
Reachable (mk_system_fn f s₀) s₀ s ↔ Reachable f s₀ s := by
  constructor <;> intro h
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s₁ h₁ h₂ ih
    simp at h₂
    exact h₂.2.1
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s₁ h₁ h₂ ih
    apply Reachable.h₁ s t s₁ ih
    simp [h₁, h₂]
    exact Reachable.h₁ s t s₁ h₁ h₂

@[simp]
theorem mk_system_fn_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ : S} :
mk_system_fn (mk_system_fn f s₀) s₀ = mk_system_fn f s₀ := by
  ext s t s₁; simp; tauto

@[simp]
theorem mk_system_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ : S} :
mk_system (mk_system_fn f s₀) s₀ = mk_system f s₀ := by
  ext1; rfl; simp

@[simp]
theorem system_init_state_toSystem {S T : Type} {sys : System S T} :
sys.init_state.toSystem = sys := rfl

@[simp]
theorem system_init_state_state {S T : Type} {sys : System S T} :
sys.init_state.s = sys.s₀ := rfl

@[simp, refl]
theorem Reachable.refl {S T : Type} {f : SystemFn S T} {a} :
Reachable f a a := Reachable.h₀

@[simp, trans]
theorem Reachable.trans {S T : Type} {f : SystemFn S T} {a b c}
(hab : Reachable f a b) (hbc : Reachable f b c) : Reachable f a c := by
  induction hbc; exact hab; apply Reachable.h₁ <;> assumption

theorem system_state_state_mk_system_tr_eq {S T : Type}
{st : SystemState S T} {f s₀ t s₁}
(h₁ : st.toSystem = mk_system f s₀)
(h₂ : st.tr t = some s₁) :
f st.s t = some s₁.s := by
  unfold SystemState.tr at h₂
  split at h₂ <;> simp at h₂
  nm s₂ h₃
  subst h₂
  generalize_proofs
  simp [h₁] at h₃
  convert h₃.2.2