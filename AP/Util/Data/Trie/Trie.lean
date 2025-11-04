import AP.Util.Data.Trie.Equiv

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

structure Trie (α β : Type*) [DecidableEq α] [Hashable α] where
  inner : Quotient # Trie.Raw.Setoid (α := α) (β := β)

namespace Trie

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t₁ t₂ t₃ : Trie α β}

def empty : Trie α β :=
  ⟨Quotient.mk _ ∅⟩

instance : EmptyCollection # Trie α β := ⟨empty⟩
theorem empty_def : (∅ : Trie α β) = empty := rfl

-- def depth (t : Trie α β) : ℕ :=
--   t.inner.lift Raw.depth # λ _ _ => Raw.Equiv.depth_eq