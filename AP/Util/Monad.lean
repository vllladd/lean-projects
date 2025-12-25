import AP.Util.List

section MonadState

variable {σ : Type} {M : Type → Type}
variable [hσ : MonadState σ M] [hM : Monad M]
variable {α β γ : Type}

@[always_inline, inline]
def gets (f : σ → α) : M α := do pure # f (←get)

theorem run_run_snd {m₁ : StateM σ α} {m₂ : StateM σ β} {x : σ} :
m₂.run (m₁.run x).2 = (do (λ _ => ()) <$> m₁; m₂).run x := rfl

end MonadState