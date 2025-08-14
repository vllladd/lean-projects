import AP.Util.Data.Trie.Raw0

namespace Trie

open Std

structure Raw (α β : Type*) [DecidableEq α] [Hashable α] where
  inner : Raw₀ α β
  wf : inner.WF

namespace Raw

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

set_option linter.unusedVariables false in
def rec' {γ : Raw α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) wf,
(∀ i t, mp.get? i = some t → (wf : t.WF) → γ ⟨t, wf⟩) → γ ⟨Raw₀.mk val mp, wf⟩) :
(t : Raw α β) → γ t
| .mk (Raw₀.mk val mp) wf => motive val mp wf # λ i t h₁ wf₁ => (mk t wf₁).rec' motive
termination_by t => t.1.depthAux
decreasing_by exact Raw₀.depthAux_le wf h₁