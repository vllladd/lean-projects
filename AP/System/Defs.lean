import AP.Util

abbrev SystemFn (S T : Type) : Type :=
  S → T → Option S

inductive Reachable {S T : Type} (f : SystemFn S T) (s₀ : S) : S → Prop where
| h₀ : Reachable f s₀ s₀
| h₁ : ∀ (s t s₁), Reachable f s₀ s → f s t = some s₁ → Reachable f s₀ s₁

def system_cnd {S T : Type} (f : SystemFn S T) (s₀ : S) : Prop :=
  ∀ s, ¬Reachable f s₀ s →
  (∀ t, f s t = none) ∧
  (∀ s₁ t, f s₁ t ≠ some s)

@[ext]
structure System (S T : Type) : Type where
  s₀ : S
  f : SystemFn S T
  h_sys : system_cnd f s₀

def mk_system_fn {S T : Type} (f : SystemFn S T) (s₀ : S)
[∀ s, Decidable # Reachable f s₀ s] : SystemFn S T :=
  λ s t => do
  guard # Reachable f s₀ s
  let s₁ ← f s t
  guard # Reachable f s₀ s₁
  return s₁

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

def mk_system {S T : Type} (f : SystemFn S T) (s₀ : S)
[∀ s, Decidable # Reachable f s₀ s] : System S T :=
  { s₀ := s₀
  , f := mk_system_fn f s₀
  , h_sys := system_cnd_mk_system_fn
  }

@[simp]
def System.Reachable {S T : Type} (sys : System S T) (s : S) : Prop :=
  _root_.Reachable sys.f sys.s₀ s

structure SystemState (S T : Type) extends System S T where
  s : S
  h_st : toSystem.Reachable s

@[simp]
def SystemState.Reachable {S T : Type} (st : SystemState S T) (s : S) : Prop :=
  _root_.Reachable st.f st.s s

def System.init_state {S T : Type} (sys : System S T) : SystemState S T :=
  { toSystem := sys
  , s := sys.s₀
  , h_st := Reachable.h₀
  }

def SystemState.tr {S T : Type} (st : SystemState S T) (t : T) :
Option (SystemState S T) := match h : st.f st.s t with
| none => none
| some s₁ => some
  { st with
    s := s₁
  , h_st := Reachable.h₁ st.s t s₁ st.h_st h
  }

def SystemState.trs {S T : Type} (st : SystemState S T) (ts : List T) :
Option (SystemState S T) := match ts with
| [] => st
| (t :: ts) => do
  let st ← st.tr t
  st.trs ts