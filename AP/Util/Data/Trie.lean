import AP.Util.Data.Set

namespace Trie

open Std

inductive Raw (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → DHashMap.Raw α (λ _ => Raw α β) → Raw α β
deriving Repr

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

def Raw.rec' {γ : Raw α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw α β)),
(∀ i x, mp.get? i = some x → γ x) → γ (mk val mp)) : (raw : Raw α β) → γ raw
| .mk val mp => motive val mp # λ i raw h => raw.rec' motive
decreasing_by
  nm val mp
  sorry

def Raw.depth : Raw α β → ℕ :=
  Raw.rec' # λ val mp f => (mp.foldlWith sorry · 0) # by
  intro acc i x h
  exact max acc # 1 + f i x sorry

end Trie