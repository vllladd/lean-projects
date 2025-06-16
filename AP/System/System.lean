import AP.System.PreSystem

def System (S T : Type) : Type := Quotient # @PreSystem.setoid S T

def mk_system {S T : Type} (f : SystemFn S T) (s₀ : S) : System S T :=
  Quotient.mk PreSystem.setoid ⟨s₀, f⟩

def system_cnd {S T : Type} (f : SystemFn S T) (s₀ : S) : Prop :=
  ∀ s, ¬Reachable f s₀ s →
  (∀ t, f s t = none) ∧
  (∀ s₁ t, f s₁ t ≠ some s)

@[simp]
theorem system_cnd_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀}
[∀ s, Decidable # Reachable f s₀ s] : system_cnd (mk_system_fn f s₀) s₀ := by
  unfold mk_system_fn
  intro s hs
  constructor
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_none_iff,
    Option.guard_eq_some', reduceCtorEq, imp_false, forall_const, ne_eq]
    intro t h₁ s₁ h₂
    contrapose! hs
    clear h₂ hs s₁
    induction h₁
    · exact Reachable.h₀
    clear s t
    nm s t s₁ h₁ h₂ ih
    apply Reachable.h₁ s t s₁ ih
    have h₃ := Reachable.h₁ _ _ _ h₁ h₂
    simp [h₁, h₂, h₃]
  · intro s₁ t
    contrapose! hs
    have h₁ : Reachable f s₀ s₁ :=
      by
        by_contra h₁
        simp [h₁] at hs
    obtain ⟨s₁, h₂⟩ : ∃ s₂, f s₁ t = some s₂ :=
      by
        by_contra! h₂
        rw [←Option.eq_none_iff_forall_ne_some] at h₂
        simp [h₂] at hs
    simp [h₁, h₂] at hs
    have h₃ : Reachable f s₀ s₁ :=
      by
        by_contra h₃
        simp [h₃] at hs
    simp [h₃] at hs
    symm at hs; subst hs
    clear h₂ h₁ s₁ t
    induction h₃
    · exact Reachable.h₀
    clear s
    nm s t s₁ h₁ h₂ ih
    apply Reachable.h₁ s t s₁ ih
    have h₃ := Reachable.h₁ _ _ _ h₁ h₂
    simp [h₁, h₂, h₃]

def System.s₀ {S T : Type} (sys : System S T) : S := by
  apply sys.lift (·.s₀)
  intro a b h
  exact h.1

@[simp]
theorem mk_system_s₀ {S T : Type} {f : SystemFn S T} {s₀ : S} :
(mk_system f s₀).s₀ = s₀ := rfl

noncomputable section open scoped Classical

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

end section

def System.Reachable {S T : Type} (sys : System S T) (s : S) : Prop := by
  apply sys.lift # λ psys => _root_.Reachable psys.f psys.s₀ s
  clear sys
  rintro a b ⟨h₁, h₂⟩
  dsimp; ext
  rw [←reachable_mk_system_fn_iff]
  nth_rewrite 2 [←reachable_mk_system_fn_iff]
  rw [h₂]
  rw [←h₁]

noncomputable section open scoped Classical

@[simp]
theorem mk_system_fn_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ : S} :
mk_system_fn (mk_system_fn f s₀) s₀ = mk_system_fn f s₀ := by
  ext s t s₁; simp; tauto

@[simp]
theorem mk_system_eq_iff {S T : Type} {f₁ f₂ : SystemFn S T} {s₁ s₂} :
mk_system f₁ s₁ = mk_system f₂ s₂ ↔ PreSystem.equiv ⟨s₁, f₁⟩ ⟨s₂, f₂⟩ := by
  unfold mk_system
  rw [Quotient.eq]
  rfl

@[simp]
theorem mk_system_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ : S} :
mk_system (mk_system_fn f s₀) s₀ = mk_system f s₀ := by
  simp [PreSystem.equiv]

#check 0 #exit

@[simp]
theorem system_init_state_toSystem {S T : Type} {sys : System S T} :
sys.init_state.toSystem = sys := rfl

@[simp]
theorem system_init_state_state {S T : Type} {sys : System S T} :
sys.init_state.s = sys.s₀ := rfl

end section

#check 0 #exit

-- structure SystemState (S T : Type) extends System S T where
--   s : S
--   h_st : toSystem.Reachable s

-- @[simp]
-- def SystemState.Reachable {S T : Type} (st : SystemState S T) (s : S) : Prop :=
--   _root_.Reachable st.f st.s s

-- def System.init_state {S T : Type} (sys : System S T) : SystemState S T :=
--   { toSystem := sys
--   , s := sys.s₀
--   , h_st := Reachable.h₀
--   }

-- def SystemState.tr {S T : Type} (st : SystemState S T) (t : T) :
-- Option (SystemState S T) := match h : st.f st.s t with
-- | none => none
-- | some s₁ => some
--   { st with
--     s := s₁
--   , h_st := Reachable.h₁ st.s t s₁ st.h_st h
--   }

-- def SystemState.trs {S T : Type} (st : SystemState S T) (ts : List T) :
-- Option (SystemState S T) := match ts with
-- | [] => st
-- | (t :: ts) => do
--   let st ← st.tr t
--   st.trs ts