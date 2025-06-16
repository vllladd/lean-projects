import AP.System.Defs

noncomputable section
open scoped Classical

@[simp]
theorem mk_system_s₀ {S T : Type} {s₀ : S} {f : SystemFn S T} :
(mk_system s₀ f).s₀ = s₀ := rfl

@[simp]
theorem mk_system_f {S T : Type} {s₀ : S} {f : SystemFn S T} :
(mk_system s₀ f).f = mk_system_fn s₀ f := rfl

@[simp]
theorem mk_system_fn_eq_some_iff {S T : Type} {s₀ : S} {f : SystemFn S T} {s t s'} :
mk_system_fn s₀ f s t = some s' ↔
Reachable s₀ f s ∧ Reachable s₀ f s' ∧ f s t = some s' := by
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
theorem mk_system_fn_eq_none_iff {S T : Type} {s₀ : S} {f : SystemFn S T} {s t} :
mk_system_fn s₀ f s t = none ↔ ¬Reachable s₀ f s ∨ f s t = none := by
  simp [Option.eq_none_iff_forall_ne_some]
  by_cases h₁ : f s t = none; simp [h₁]
  obtain ⟨s₁, h₂⟩ := Option.exists_eq_some_of_ne_none h₁
  simp [h₂]
  by_cases h₃ : Reachable s₀ f s <;> simp [h₃]
  exact Reachable.h₁ s t s₁ h₃ h₂

@[simp]
theorem reachable_mk_system_fn_iff {S T : Type} {s₀ : S} {f : SystemFn S T} {s} :
Reachable s₀ (mk_system_fn s₀ f) s ↔ Reachable s₀ f s := by
  constructor <;> intro h
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s' h₁ h₂ ih
    simp at h₂
    exact h₂.2.1
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s' h₁ h₂ ih
    apply Reachable.h₁ s t s' ih
    simp [h₁, h₂]
    exact Reachable.h₁ s t s' h₁ h₂

@[simp]
theorem mk_system_fn_mk_system_fn {S T : Type} {s₀ : S} {f : SystemFn S T} :
mk_system_fn s₀ (mk_system_fn s₀ f) = mk_system_fn s₀ f := by
  ext s t s'; simp; tauto

@[simp]
theorem mk_system_mk_system_fn {S T : Type} {s₀ : S} {f : SystemFn S T} :
mk_system s₀ (mk_system_fn s₀ f) = mk_system s₀ f := by
  ext1; rfl; simp

@[simp]
theorem system_init_state_toSystem {S T : Type} {sys : System S T} :
sys.init_state.toSystem = sys := rfl

@[simp]
theorem system_init_state_state {S T : Type} {sys : System S T} :
sys.init_state.s = sys.s₀ := rfl