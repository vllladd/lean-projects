import AP.Util.Data.Set

open Std

inductive TrieRaw (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → DHashMap.Raw α (λ _ => TrieRaw α β) → TrieRaw α β

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

-- def TrieRaw.depth : TrieRaw α β → ℕ
-- | mk _ mp => mp.fold (λ acc _ trie => max acc # 1 + trie.depth) 0