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

inductive WF : Raw₀ α β → Prop where
| mk : ∀ {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)}, mp.WF →
  (∀ {k t}, mp.get? k = some t → t.WF) → (mk val mp).WF

theorem WF.mp {t : Raw₀ α β} (wf : t.WF) : t.mp.WF := by
  cases wf; assumption

theorem WF.get? {t : Raw₀ α β} (wf : t.WF) {k t'} (h : t.mp.get? k = some t') : t'.WF := by
  cases wf; nm val mp h₁ h₂; exact h₂ h

theorem rec_2_eq {arr : Array (DHashMap.Internal.AssocList α (λ _ => Raw₀ α β))}
{M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
@rec_2 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ arr =
(H₃ arr.toList # @rec_3 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ arr.toList) := rfl

theorem rec_3_eq {xs : List (DHashMap.Internal.AssocList α (λ _ => Raw₀ α β))}
{M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
@rec_3 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ xs =
@List.rec _ _ H₄ (λ x xs acc => H₅ x xs
(@rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ x) acc) xs := by
  induction xs; rfl; nm x xs ih; dsimp; rw [ih]

theorem rec_4_eq {xs : DHashMap.Internal.AssocList α (λ _ => Raw₀ α β)}
{M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
@rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ xs =
@List.rec _ _ H₆ (λ (x : (_ : α) × Raw₀ α β) xs acc => H₇ x.1 x.2 (.ofList xs)
(@rec α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ x.2) acc) xs.toList := by
  induction xs; rfl; nm i x xs ih; simp [ih]; rw [DHashMap.Internal.AssocList.ofList_toList]

-- #check 0 #exit

noncomputable
def depthAux (t : Raw₀ α β) : ℕ :=
  let f := @t.recOn
  @f (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
    (λ _ _ n => n)
    (λ _ _ n => n)
    (λ _ n => n)
    0 (λ _ _ n m => max n m)
    0 (λ _ _ _ n m => max (n + 1) m)

-- #check 0 #exit

theorem depthAux_le {t : Raw₀ α β} (wf : t.WF) {k t'}
(h : t.mp.get? k = some t') : t'.depthAux < t.depthAux := by
  rcases t with ⟨val, mp⟩
  nth_rw 2 [depthAux]
  simp only [rec_3_eq, rec_4_eq, List.rec_eq_foldr]
  sorry

-- #check 0 #exit

theorem depthAux_le_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)}
(wf : (mk val mp).WF) {k : α} {t : Raw₀ α β} (h : mp.get? k = some t) :
t.depthAux < (mk val mp).depthAux := depthAux_le wf h

set_option linter.unusedVariables false in
def rec' {γ : Raw₀ α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
(∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : (t : Raw₀ α β) → t.WF → γ t
| .mk val mp, wf => motive val mp # λ i t h => t.rec' motive # wf.get? h
termination_by t => t.depthAux
decreasing_by exact depthAux_le wf h

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
decreasing_by exact Raw₀.depthAux_le wf h₁

-- def Raw.depth : Raw α β → ℕ :=
--   Raw.rec' # λ val mp f => (mp.foldlWith sorry · 0) # by
--   intro acc i x h
--   exact max acc # 1 + f i x sorry

end Raw

end Trie