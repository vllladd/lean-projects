import Projects.Util.List

variable {α β γ : Type}
variable {M : Type → Type} [hM : Monad M]

def sequence_ (ms : List (M α)) : M Unit := do
  _ ← sequence ms

def replicateM (n : ℕ) (m : M α) : M (List α) := do
  sequence # .replicate n m

def replicateM_ (n : ℕ) (m : M α) : M Unit := do
  sequence_ # .replicate n m

-----

@[simp]
theorem Id_pure : (pure : α → Id α) = (λ a => a) := rfl

@[simp]
theorem Id_bind {m : Id α} {f : α → Id β} : m >>= f = f m := rfl

section MonadState

variable {σ : Type}
variable [hσ : MonadState σ M]

@[always_inline, inline]
def gets (f : σ → α) : M α := do pure # f (←get)

theorem run_run_snd {m₁ : StateM σ α} {m₂ : StateM σ β} {x : σ} :
m₂.run (m₁.run x).2 = (do (λ _ => ()) <$> m₁; m₂).run x := rfl

omit hσ in @[simp]
theorem run_gets {f : σ → α} :
StateT.run (@gets α (StateT σ M) _ σ _ f) =
StateT.run (@get _ (StateT σ M) _ >>= λ x => pure (f x)) := rfl

omit hσ in @[simp]
theorem run_set {s : σ} : StateT.run (@set σ (StateT σ M) _ s) = λ _ => pure ((), s) := rfl

omit hσ in @[simp]
theorem run_set' {s : σ} : StateT.run (StateT.set s : StateT σ M Unit) = λ _ => pure ((), s) := rfl

end MonadState