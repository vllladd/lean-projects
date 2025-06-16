import AP.Util

inductive Reachable {State Transition : Type} (s₀ : State)
(f : State → Transition → Option State) : State → Prop where
| h₀ : Reachable s₀ f s₀
| h₁ : ∀ {s t s'}, Reachable s₀ f s → f s t = some s' → Reachable s₀ f s'

structure System (State Transition : Type) : Type where
  s₀ : State
  f : State → Transition → Option State
  h : ∀ s, Reachable s₀ f s

structure System.VState {State Transition : Type} (s₀ : State)
(f : State → Transition → Option State) : Type where
  s : State
  h : Reachable s₀ f s

@[simp]
def mk_system_fn {State Transition : Type} (s₀ : State)
(f : State → Transition → Option State) :
System.VState s₀ f → Transition → Option (System.VState s₀ f) := λ ⟨s, hs⟩ t =>
  match h : f s t with
  | none => none
  | some s' => some ⟨s', Reachable.h₁ hs h⟩

def mk_system {State Transition : Type} (s₀ : State)
(f : State → Transition → Option State) : System (System.VState s₀ f) Transition :=
  { s₀ := ⟨s₀, Reachable.h₀⟩
  , f := mk_system_fn s₀ f
  , h := by
      rintro ⟨s, h⟩
      induction h
      · exact Reachable.h₀
      nm s t s' h₁ h₂ ih
      have h₃ := @Reachable.h₁ (System.VState s₀ f) Transition ⟨_, Reachable.h₀⟩
        (mk_system_fn s₀ f)
        ⟨s, h₁⟩ t ⟨s', Reachable.h₁ h₁ h₂⟩
      specialize h₃ ih
      dsimp at h₃ ih ⊢
      split at h₃
      · nm h₄; simp [h₂] at h₄
      nm s₁ hs₁
      simp [hs₁] at h₂
      subst h₂
      simp at h₃
      exact h₃
  }