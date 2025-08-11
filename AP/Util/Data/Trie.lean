import AP.Util.Data.Set

namespace Trie

open Std

inductive Raw (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → DHashMap.Raw α (λ _ => Raw α β) → Raw α β

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

-- def Raw.rec' {γ : Sort*}
-- (motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw α β)),
-- (∀ i x, mp.get? i = some x → γ) → γ) : (raw : Raw α β) → γ
-- | .mk val mp => motive val mp # λ g => mp.foldlWith _ _ _

-- def TrieRaw.depth : TrieRaw α β → ℕ
-- | mk _ mp => mp.fold (λ acc _ trie => max acc # 1 + trie.depth) 0