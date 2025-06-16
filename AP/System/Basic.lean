import AP.System.System

noncomputable section
open scoped Classical

#check 0 #exit

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