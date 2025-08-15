import AP.Util.Data.Set

namespace Trie

open Std

inductive Raw₀ (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → (mp : DHashMap.Raw α (λ _ => Raw₀ α β)) → Raw₀ α β

namespace Raw₀

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
  {t t₁ t₂ : Raw₀ α β}

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

def isEmpty (t : Raw₀ α β) : Prop :=
  t.val = none ∧ t.mp.isEmpty

instance : Decidable t.isEmpty :=
  match h : t.val.isNone && t.mp.isEmpty with
  | true => .isTrue # by simp at h; simpa [isEmpty]
  | false => .isFalse # by simp at h; simpa [isEmpty]

@[class]
inductive WF : Raw₀ α β → Prop where
| mk : ∀ {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)},
  mp.WF → (∀ {k t}, mp.get? k = some t → ¬t.isEmpty) →
  (∀ {k t}, mp.get? k = some t → t.WF) → (mk val mp).WF

theorem WF.mp {t : Raw₀ α β} (wf : t.WF) : t.mp.WF := by
  cases wf; assumption

theorem WF.wf_get? {t : Raw₀ α β} (wf : t.WF)
{k t'} (h : t.mp.get? k = some t') : t'.WF := by
  cases wf; nm val mp h₁ h₂ h₃; exact h₃ h

theorem WF.not_empty_get? {t : Raw₀ α β} (wf : t.WF)
{k t'} (h : t.mp.get? k = some t') : ¬t'.isEmpty := by
  cases wf; nm val mp h₁ h₂ h₃; exact h₂ h

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
  simp only [rec_3_eq, rec_4_eq, List.rec_eq_foldr, List.foldr_max_eq_max?_map']
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
def recAux {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) (wf : t.WF)
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : γ t :=
  match t with
  | .mk val mp => motive val mp wf.mp #
    λ i t h => t.recAux (wf.wf_get? h) motive
termination_by t.depthAux
decreasing_by exact depthAux_le wf h

def rec' {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) [wf : t.WF]
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : γ t :=
  t.recAux wf motive

def depth (t : Raw₀ α β) [wf : t.WF] : ℕ :=
  t.rec' # λ _ mp h₁ f => (mp.foldWith h₁ · 0) # λ acc i x h₂ =>
  max acc # 1 + f i x h₂

def empty : Raw₀ α β := ⟨none, ∅⟩

instance : EmptyCollection (Raw₀ α β) := ⟨empty⟩

theorem empty_def : (∅ : Raw₀ α β) = ⟨none, ∅⟩ := rfl

instance : (∅ : Raw₀ α β).WF := by
  constructor <;> simp

@[simp]
theorem rec'_mk {γ : Raw₀ α β → Sort*} {val mp} [wf : (⟨val, mp⟩ : Raw₀ α β).WF]
{motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)} :
(⟨val, mp⟩ : Raw₀ α β).rec' motive =
motive val mp wf.mp (λ _ t h => t.rec' (wf := wf.wf_get? h) motive) := by
  simp_rw [rec', recAux]

@[simp]
theorem depth_mk {val mp} [wf : (⟨val, mp⟩ : Raw₀ α β).WF] :
(⟨val, mp⟩ : Raw₀ α β).depth = mp.foldWith wf.mp
(λ acc _ (t' : Raw₀ α β) h => max acc # 1 + t'.depth (wf := wf.wf_get? h)) 0 := by
  unfold depth; simp

@[simp]
theorem depth_empty : (∅ : Raw₀ α β).depth = 0 := by
  simp [empty_def]

theorem depth_le {t : Raw₀ α β} (wf : t.WF) {k t'}
(h : t.mp.get? k = some t') : t'.depth (wf := wf.wf_get? h) < t.depth := by
  classical
  rcases t with ⟨val, mp⟩
  simp at h ⊢
  have h₁ := DHashMap.Raw.mem_toList_iff_get?_eq_some wf.mp |>.mpr h
  dsimp at h₁
  have h₂ := wf.wf_get? h
  rw [DHashMap.Raw.foldWith_eq_foldlWith_toList, List.foldlWith_max_eq_max?_mapWith]
  apply Nat.lt_of_succ_le
  change (⟨k, t'⟩ : Σ _, _).snd.depth + 1 ≤ _
  apply List.le_elim_max_max?_of_mem
  simp
  use k, t', h₁
  rw [add_comm]