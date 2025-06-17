import AP.Util

abbrev SystemFn (S T : Type) : Type :=
  S → T → Option S

inductive Reachable {S T : Type} (f : SystemFn S T) (s₀ : S) : S → Prop where
| h₀ : Reachable f s₀ s₀
| h₁ : ∀ {s t s₁}, f s t = some s₁ → Reachable f s₀ s → Reachable f s₀ s₁

@[refl]
theorem Reachable.refl {S T : Type} {f : SystemFn S T} {s₀ : S} :
Reachable f s₀ s₀ := Reachable.h₀

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

@[simp]
def system_equiv_f {S T : Type} (s₀ : S) (f g : SystemFn S T) : Prop :=
  mk_system_fn f s₀ = mk_system_fn g s₀

@[simp]
def PreSystem.equiv_f {S T : Type}
(sys : PreSystem S T) (f : SystemFn S T) : Prop :=
  system_equiv_f sys.s₀ sys.f f

def PreSystem.equiv {S T : Type} (sys₁ sys₂ : PreSystem S T) : Prop :=
  sys₁.s₀ = sys₂.s₀ ∧ sys₁.equiv_f sys₂.f

end section

@[simp, refl]
theorem PreSystem.equiv.refl {S T : Type} {a : PreSystem S T} :
a.equiv a := by simp [PreSystem.equiv]

@[symm]
theorem PreSystem.equiv.symm {S T : Type} {a b : PreSystem S T}
(h : a.equiv b) : b.equiv a := by
  simp [PreSystem.equiv]
  rcases h with ⟨h₁, h₂⟩
  simp at h₂
  rw [h₁] at h₂
  exact ⟨h₁.symm, h₂.symm⟩

theorem PreSystem.equiv.comm {S T : Type} {a b : PreSystem S T} :
a.equiv b ↔ b.equiv a := by
  constructor <;> exact PreSystem.equiv.symm

@[trans]
theorem PreSystem.equiv.trans {S T : Type} {a b c : PreSystem S T}
(hab : a.equiv b) (hbc : b.equiv c) : a.equiv c := by
  simp [PreSystem.equiv] at hab hbc ⊢
  rcases hab with ⟨h₁, h₂⟩
  rcases hbc with ⟨h₃, h₄⟩
  simp [h₁, h₂, h₃]
  rwa [h₁]

theorem pre_system_equivalence_equiv {S T : Type} :
Equivalence # @PreSystem.equiv S T := by
  constructor
  · simp
  · intro x y h
    exact h.symm
  · rintro a b c h₁ h₂
    exact h₁.trans h₂

def PreSystem.setoid {S T : Type} : Setoid (PreSystem S T) := by
  exact ⟨_, pre_system_equivalence_equiv⟩