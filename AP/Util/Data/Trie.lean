import AP.Util.Data.Set

namespace Trie

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

inductive Raw₀ (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) → Raw₀ α β

namespace Raw₀

def val : Raw₀ α β → Option β
| .mk val _ => val

def mp : Raw₀ α β → DHashMap.Raw α (λ _ => Raw₀ α β)
| .mk _ mp => mp

@[simp]
theorem val_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)} :
(mk val mp).val = val := rfl

@[simp]
theorem mp_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)} :
(mk val mp).mp = mp := rfl

noncomputable
def depthAux (t : Raw₀ α β) : ℕ :=
  let f := @t.recOn
  @f (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
    (λ _ _ n => n)
    (λ _ _ n => n)
    (λ _ n => n)
    0 (λ _ _ n m => max n m)
    0 (λ _ _ _ n m => max (n + 1) m)

-- example : Raw.depthAux (α := ℕ) (β := ℕ) (Raw.mk none (.ofList [])) = 0 := by
--   simp only [Raw.depthAux, DHashMap.Raw.ofList_nil]
--   generalize hx : (∅ : DHashMap.Raw _ _).2.toList = xs
--   replace hx : ∀ b ∈ xs, b.toList = []
--   · intro b hb
--     rw [List.eq_nil_iff_forall_not_mem]
--     rintro ⟨k, t⟩
--     subst hx
--     simp at hb
--     sorry
--   induction xs; rfl
--   nm b bs ih
--   simp only [Nat.max_eq_zero_iff]
--   simp at hx
--   rcases hx with ⟨h₁, h₂⟩
--   specialize ih h₂
--   simp [ih]
--   cases b; rfl
--   nm k t b
--   simp at h₁

-- #check 0 #exit

theorem depthAux_le {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)}
{k : α} {t : Raw₀ α β} (h : mp.get? k = t) : t.depthAux < (mk val mp).depthAux := by
  sorry

-- #check 0 #exit

set_option linter.unusedVariables false in
def rec' {γ : Raw₀ α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
(∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : (t : Raw₀ α β) → γ t
| .mk val mp => motive val mp # λ i t h => t.rec' motive
termination_by t => t.depthAux
decreasing_by exact depthAux_le h

inductive WF : Raw₀ α β → Prop where
| mk : ∀ {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)},
  (∀ {k t}, mp.get? k = some t → t.WF) → (mk val mp).WF

end Raw₀

structure Raw (α β : Type*) [DecidableEq α] [Hashable α] where
  inner : Raw₀ α β
  wf : inner.WF

namespace Raw

set_option linter.unusedVariables false in
def rec' {γ : Raw α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) wf,
(∀ i t, mp.get? i = some t → (wf : t.WF) → γ ⟨t, wf⟩) → γ ⟨Raw₀.mk val mp, wf⟩) :
(t : Raw α β) → γ t
| .mk (Raw₀.mk val mp) wf => motive val mp wf # λ i t h₁ wf₁ => (mk t wf₁).rec' motive
termination_by t => t.1.depthAux
decreasing_by exact Raw₀.depthAux_le h₁

#check 0 #exit

-- def Raw.depth : Raw α β → ℕ :=
--   Raw.rec' # λ val mp f => (mp.foldlWith sorry · 0) # by
--   intro acc i x h
--   exact max acc # 1 + f i x sorry

end Raw

end Trie