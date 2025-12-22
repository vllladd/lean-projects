import AP.Util.List

section MonadState

universe u v

@[always_inline, inline]
def gets {σ : Type u} {m : Type u → Type v} {α : Type u} [MonadState σ m] [Monad m]
(f : σ → α) : m α := do pure # f (←get)

end MonadState