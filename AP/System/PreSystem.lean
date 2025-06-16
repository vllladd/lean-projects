import AP.Util

abbrev SystemFn (S T : Type) : Type :=
  S → T → Option S

inductive Reachable {S T : Type} (f : SystemFn S T) (s₀ : S) : S → Prop where
| h₀ : Reachable f s₀ s₀
| h₁ : ∀ (s t s₁), Reachable f s₀ s → f s t = some s₁ → Reachable f s₀ s₁

def mk_system_fn {S T : Type} (f : SystemFn S T) (s₀ : S)
[∀ s, Decidable # Reachable f s₀ s] : SystemFn S T :=
  λ s t => do
  guard # Reachable f s₀ s
  let s₁ ← f s t
  guard # Reachable f s₀ s₁
  return s₁

@[ext]
structure PreSystem (S T : Type) : Type where
  s₀ : S
  f : SystemFn S T

noncomputable section open scoped Classical

def PreSystem.equiv {S T : Type} (sys₁ sys₂ : PreSystem S T) : Prop :=
  sys₁.s₀ = sys₂.s₀ ∧ mk_system_fn sys₁.f sys₁.s₀ = mk_system_fn sys₂.f sys₂.s₀

end section

theorem pre_system_equivalence_equiv {S T : Type} :
Equivalence # @PreSystem.equiv S T := by
  unfold PreSystem.equiv
  constructor
  · simp
  · rintro a b ⟨h₁, h₂⟩
    exact ⟨h₁.symm, h₂.symm⟩
  · rintro a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    simpa [h₁, h₃, h₂]

def PreSystem.setoid {S T : Type} : Setoid (PreSystem S T) := by
  exact ⟨_, pre_system_equivalence_equiv⟩