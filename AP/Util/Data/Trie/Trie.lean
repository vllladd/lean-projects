import AP.Util.Data.Trie.Raw

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

-- structure Trie (α β : Type*) [DecidableEq α] [Hashable α] where
--   inner : Unit

namespace Trie