import Projects.Util.List

variable {α β γ : Type}
variable {M : Type → Type} [hM : Monad M] [hM₂ : LawfulMonad M]

def sequence' (ms : List (M α)) : M Unit := do
  _ ← sequence ms

def replicateM (n : ℕ) (m : M α) : M (List α) := do
  sequence # .replicate n m

def replicateM' (n : ℕ) (m : M α) : M Unit := do
  sequence' # .replicate n m

class MonadCnd (p : {α : Type} → M α → Prop) : Prop where
  pure {α : Type} {x : α} : p (pure x)
  bind {α β : Type} {m : M α} {f : α → M β} : p m → (∀ x, p (f x)) → p (m >>= f)

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

omit hM₂ hσ in @[simp]
theorem run_gets {f : σ → α} :
StateT.run (@gets α (StateT σ M) _ σ _ f) =
StateT.run (@get _ (StateT σ M) _ >>= λ x => pure (f x)) := rfl

omit hM₂ hσ in @[simp]
theorem run_set {s : σ} : StateT.run (@set σ (StateT σ M) _ s) = λ _ => pure ((), s) := rfl

omit hM₂ hσ in @[simp]
theorem run_set' {s : σ} : StateT.run (StateT.set s : StateT σ M Unit) = λ _ => pure ((), s) := rfl

end MonadState

omit hM₂ in @[simp]
theorem sequence_nil : sequence ([] : List (M α)) = pure [] := rfl

@[simp]
theorem sequence_cons {m : M α} {ms} :
sequence (m :: ms) = m >>= λ x => sequence ms >>= λ xs => pure (x :: xs) := by
  unfold sequence; simp [traverse, List.traverse]; rw [←hM₂.bind_map]; simp

@[simp]
theorem sequence'_nil : sequence' ([] : List (M α)) = pure () := by
  simp [sequence']

@[simp]
theorem sequence'_cons {m : M α} {ms} : sequence' (m :: ms) = m >>= λ _ => sequence' ms := by
  simp [sequence']

theorem MonadCnd.map {p} [H : MonadCnd p] {f : α → β} {m : M α} (h₁ : p m) : p (f <$> m) := by
  rw [map_eq_pure_bind]; exact H.bind h₁ λ _ => H.pure

theorem MonadCnd.sequence {p} [H : MonadCnd p] {ms : List (M α)}
(h₁ : ∀ m ∈ ms, p m) : p (sequence ms) := by
  induction ms <;> simp
  · exact H.pure
  nm m ms ih
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  exact H.bind h₁ λ _ => H.map # ih h₂

theorem MonadCnd.sequence' {p} [H : MonadCnd p] {ms : List (M α)}
(h₁ : ∀ m ∈ ms, p m) : p (sequence' ms) := by
  unfold _root_.sequence'; simp; apply H.map # H.sequence h₁

theorem MonadCnd.replicateM {p} [H : MonadCnd p] {m : M α} {n}
(h₁ : p m) : p (replicateM n m) := by
  apply H.sequence; simp [h₁]

theorem MonadCnd.replicateM' {p} [H : MonadCnd p] {m : M α} {n}
(h₁ : p m) : p (replicateM' n m) := by
  apply H.sequence'; simp [h₁]

namespace List

variable {xs ys zs : List α}

theorem mapM_eq_sequence {f : α → M β} : xs.mapM f = sequence (xs.map f) := by
  induction xs <;> simp_all

theorem forM_eq_sequence' {f : α → M Unit} : xs.forM f = sequence' (xs.map f) := by
  induction xs <;> simp_all

end List