import Projects.Util.Monad

namespace Sum

variable {α β γ : Type}

@[simp]
theorem pure_eq {x : β} : (pure x : α ⊕ β) = .inr x := rfl

@[simp]
theorem bind_eq_inl_iff {m : α ⊕ β} {f : β → α ⊕ γ} {x : α} :
(m >>= f) = .inl x ↔ m = .inl x ∨ ∃ y, m = .inr y ∧ f y = .inl x := by
  simp [bind, Sum.bind]; grind

@[simp]
theorem bind_eq_inr_iff {m : α ⊕ β} {f : β → α ⊕ γ} {x : γ} :
(m >>= f) = .inr x ↔ ∃ y, m = .inr y ∧ f y = .inr x := by
  simp [bind, Sum.bind]; grind

@[simp]
theorem fmap_eq_inl_iff {m : α ⊕ β} {f : β → γ} {x : α} :
(f <$> m) = .inl x ↔ m = .inl x := by
  simp [Functor.map, Sum.bind]; grind

@[simp]
theorem fmap_eq_inr_iff {m : α ⊕ β} {f : β → γ} {x : γ} :
(f <$> m) = .inr x ↔ ∃ y, m = .inr y ∧ f y = x := by
  simp [Functor.map, Sum.bind]; grind