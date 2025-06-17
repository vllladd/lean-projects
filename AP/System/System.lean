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
    apply Reachable.h₁ (t := t) _ ih
    have h₃ := Reachable.h₁ h₁ h₂
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
    apply Reachable.h₁ (t := t) _ ih
    have h₃ := Reachable.h₁ h₁ h₂
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
  exact Reachable.h₁ h₂ h₃

@[simp]
theorem reachable_mk_system_fn_iff {S T : Type} {f : SystemFn S T} {s₀ : S} {s} :
Reachable (mk_system_fn f s₀) s₀ s ↔ Reachable f s₀ s := by
  constructor <;> intro h
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s₁ h₁ h₂ ih
    simp at h₁
    exact h₁.2.1
  · induction h
    · exact Reachable.h₀
    clear s
    nm s t s₁ h₁ h₂ ih
    apply Reachable.h₁ (t := t) _ ih
    simp [h₁, h₂]
    exact Reachable.h₁ h₁ h₂

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
mk_system f₁ s₁ = mk_system f₂ s₂ ↔ s₁ = s₂ ∧ system_congr_f s₁ f₁ f₂:= by
  unfold mk_system
  rw [Quotient.eq]
  rfl

@[simp]
theorem mk_system_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ : S} :
mk_system (mk_system_fn f s₀) s₀ = mk_system f s₀ := by
  simp [PreSystem.equiv]

end section

structure SystemState (S T : Type) where
  to_system : System S T
  s : S
  h_st : to_system.Reachable s

@[simp]
def SystemState.Reachable {S T : Type} (st : SystemState S T) (s : S) : Prop :=
  st.to_system.Reachable s

def System.init_state {S T : Type} (sys : System S T) : SystemState S T :=
  { to_system := sys
  , s := sys.s₀
  , h_st := by apply sys.ind # λ p => Reachable.h₀
  }

@[simp]
theorem system_init_state_to_system {S T : Type} {sys : System S T} :
sys.init_state.to_system = sys := rfl

@[simp]
theorem system_init_state_state {S T : Type} {sys : System S T} :
sys.init_state.s = sys.s₀ := rfl

def System.congr_f {S T : Type}
(sys : System S T) (f : SystemFn S T) : Prop := by
  apply sys.lift (·.congr_f f)
  rintro a b ⟨h₁, h₂⟩
  simp at h₂ ⊢
  rw [h₂, h₁]

def PreSystem.to_system {S T : Type} (p : PreSystem S T) : System S T :=
  Quot.mk _ p

def System.equiv_pre {S T : Type} (s : System S T) (p : PreSystem S T) : Prop := by
  apply s.lift (·.equiv p)
  intro a b h
  simp
  change a.equiv b at h
  exact ⟨λ h₁ => h.symm.trans h₁, λ h₁ => h.trans h₁⟩

@[simp]
theorem pre_system_to_system_equiv {S T : Type} {p : PreSystem S T} :
p.to_system.equiv_pre p := PreSystem.equiv.refl

noncomputable section open scoped Classical

theorem reachable_of_mk_system_fn_eq {S T : Type} {f g : SystemFn S T} {s₀ s}
(h₁ : mk_system_fn f s₀ = mk_system_fn g s₀) (h₂ : Reachable f s₀ s) :
Reachable g s₀ s := by
  induction h₂; constructor
  clear s
  nm s t s₁ h₃ h₄ ih
  replace h₁ := congrArg (· s t) h₁
  have h₅ := Reachable.h₁ h₃ h₄
  simp [mk_system_fn, h₃, h₄, h₅] at h₁
  symm at h₁
  simp at h₁
  apply Reachable.h₁ (t := t) _ ih
  rcases h₁ with ⟨h₁, h₆⟩
  rw [←h₆]
  generalize hx : g s t = x
  cases x <;> simp
  nm x
  symm
  simp
  simp [hx] at h₆
  exact h₆.1

theorem reachable_of_reachable_mk_system_fn {S T : Type} {f : SystemFn S T} {s₀ s}
(h : Reachable (mk_system_fn f s₀) s₀ s) : Reachable f s₀ s := by
  induction h; rfl
  clear s
  nm s t s₁ h₁ h₂ ih
  simp at h₁
  rcases h₁ with ⟨h₁, h₃, h₄⟩
  exact Reachable.h₁ h₄ ih

end section

def SystemState.tr_aux {S T : Type} (st : SystemState S T) (t : T)
(f : SystemFn S T) (h : st.to_system.congr_f f) : Option (SystemState S T) :=
match h₁ : f st.s t with
| none => none
| some s₁ => some
  { st with
    s := s₁
  , h_st :=
    by
      classical
      rcases st with ⟨sys, s, h₂⟩
      dsimp at h h₁ ⊢
      revert h₂ h
      apply sys.ind
      clear sys
      intro p h₂ h₃
      simp [System.Reachable, System.congr_f] at h₂ h₃ ⊢
      replace h₁ : mk_system_fn f p.s₀ s t = some s₁ := by
        simp
        have h₄ := reachable_of_mk_system_fn_eq h₃ h₂
        exact ⟨h₄, Reachable.h₁ h₁ h₄, h₁⟩
      apply reachable_of_mk_system_fn_eq h₃.symm
      simp at h₁
      rcases h₁ with ⟨h₁, h₄, h₅⟩
      exact Reachable.h₁ h₅ h₁
  }

-- #check 0 #exit

-- noncomputable
-- def SystemState.tr {S T : Type} (st : SystemState S T) (t : T) :
-- Option (SystemState S T) := by
--   classical
--   apply st.to_system.lift λ p => if h : _ then st.tr_aux t p.f h else none
--   intro a b ⟨h₁, h₂⟩
--   simp at h₂
--   rcases st with ⟨sys, s, hs⟩
--   simp
--   revert sys
--   apply Quot.ind
--   intro p hs
--   split_ifs with h₃ h₄ h₄ <;> simp [tr_aux] <;> split <;>
--     (try split) <;> simp <;> change _root_.Reachable _ _ _ at hs <;>
--     (try change system_congr_f _ _ _ at h₃ h₄) <;>
--     simp at h₃ h₄

-- def SystemState.trs {S T : Type} (st : SystemState S T) (ts : List T) :
-- Option (SystemState S T) := match ts with
-- | [] => st
-- | (t :: ts) => do
--   let st ← st.tr t
--   st.trs ts