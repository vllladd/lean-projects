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
  have h₁ : ⟨k, t'⟩ ∈ t.mp.toList
  · change ⟨k, t'⟩ ∈ (DHashMap.mk t.mp wf.mp).toList
    simp [DHashMap.get?]
    rw [DHashMap.Raw.get?] at h
    split_ifs at h
    exact h
  rw [DHashMap.Internal.toList_eq_flat_buckets] at h₁
  simp at h₁
  obtain ⟨b, h₁, h₂⟩ := h₁
  rcases t with ⟨val, mp⟩
  nth_rw 2 [depthAux]
  dsimp at h₁ h ⊢
  replace h₁ : b ∈ mp.buckets.toList := by simpa
  generalize hb : mp.buckets.toList = bs at h₁ ⊢
  clear wf
  induction bs generalizing mp
  · simp at h₁
  nm b₁ bs ih
  specialize ih ⟨mp.size, ⟨b :: bs⟩⟩
  sorry

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