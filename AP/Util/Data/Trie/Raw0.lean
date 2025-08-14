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

noncomputable
def depthAux (t : Raw₀ α β) : ℕ :=
  let f := @t.recOn
  @f (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
    (λ _ _ n => n)
    (λ _ _ n => n)
    (λ _ n => n)
    0 (λ _ _ n m => max n m)
    0 (λ _ _ _ n m => max (n + 1) m)

theorem depthAux_le {t : Raw₀ α β} (wf : t.WF) {k t'}
(h : t.mp.get? k = some t') : t'.depthAux < t.depthAux := by
  classical
  rcases t with ⟨val, mp⟩
  nth_rw 2 [depthAux]
  simp only [rec_3_eq, rec_4_eq, List.rec_eq_foldr, List.foldr_max_eq_max!_map]
  generalize hb : mp.2.toList = bs
  change _ < (0 :: bs.map (λ x => (0 :: x.toList.map
    (λ x => x.snd.depthAux + 1)).max?.getD 0)).max?.getD 0
  simp
  generalize hf : (λ (x : DHashMap.Internal.AssocList α # λ _ => Raw₀ α β) =>
    (x.toList.map (λ x => x.snd.depthAux + 1)).max?.elim 0 (max 0)) = f
  obtain ⟨b, h₁, h₂⟩ := wf.mp.mem_bucket_of_get?_eq_some h
  replace h₁ : b ∈ bs; simpa [←hb]
  generalize hb' : b :: bs.erase b = bs'
  have h₃ : bs.Perm bs'; simpa [←hb']
  rw [List.max?_eq_max?_of_perm (ys := bs'.map f) # h₃.map f]
  simp [←hb']
  suffices h₄ : t'.depthAux < f b
  · cases ((bs.erase b).map f).max? <;> simp [h₄]
  subst hf
  dsimp
  clear! val h wf bs bs'
  generalize hx : b.toList.map (λ x => x.2.depthAux + 1) = xs
  replace h₂ : (t'.depthAux + 1) ∈ xs
  · rw [←hx, List.mem_map]; use ⟨k, t'⟩
  clear k
  cases h₃ : xs.max?
  · simp at h₃; simp [h₃] at h₂
  simp; linarith [List.le_max? h₂ h₃]

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