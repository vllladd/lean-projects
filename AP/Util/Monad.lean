import AP.Util.List

variable {α β γ : Type}

@[simp]
theorem Id_pure : (pure : α → Id α) = (λ a => a) := rfl

@[simp]
theorem Id_bind {m : Id α} {f : α → Id β} : m >>= f = f m := rfl

section MonadState

variable {σ : Type} {M : Type → Type}
variable [hσ : MonadState σ M] [hM : Monad M]

@[always_inline, inline]
def gets (f : σ → α) : M α := do pure # f (←get)

theorem run_run_snd {m₁ : StateM σ α} {m₂ : StateM σ β} {x : σ} :
m₂.run (m₁.run x).2 = (do (λ _ => ()) <$> m₁; m₂).run x := rfl

end MonadState