import AP.Util.Data.Set

namespace LeafTrie

open Std

inductive Raw₀ (α β : Type*) [DecidableEq α] [Hashable α] where
| leaf : β → Raw₀ α β
| node : DHashMap.Raw α (λ _ => Raw₀ α β) → Raw₀ α β

namespace Raw₀

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t' t₁ t₂ t₃ : Raw₀ α β}

@[simp]
def IsLeaf (t : Raw₀ α β) : Prop := match t with
| .leaf _ => True
| _ => False

@[simp]
def IsNode (t : Raw₀ α β) : Prop := match t with
| .node _ => True
| _ => False

instance : Decidable t.IsLeaf := match t with
| .leaf _ => by dsimp; infer_instance
| .node _ => by dsimp; infer_instance

@[class]
inductive WF : Raw₀ α β → Prop where
| leaf {x} : WF # .leaf x
| node {t} : DHashMap.Raw.WF t → (∀ k t₁, t.get? k = some t₁ → WF t₁) → WF (.node t)

-- #check 0 #exit

-- theorem rec_2_eq {arr : Array (DHashMap.Internal.AssocList α (λ _ => Raw₀ α β))}
-- {M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
-- @rec_2 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ arr =
-- (H₃ arr.toList # @rec_3 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ arr.toList) :=

-- theorem rec_3_eq {xs : List (DHashMap.Internal.AssocList α (λ _ => Raw₀ α β))}
-- {M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
-- @rec_3 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ xs =
-- @List.rec _ _ H₄ (λ x xs acc => H₅ x xs
-- (@rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ x) acc) xs := by
--   induction xs; rfl; nm x xs ih; dsimp; rw [ih]

-- theorem rec_4_eq {xs : DHashMap.Internal.AssocList α (λ _ => Raw₀ α β)}
-- {M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇} :
-- @rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ xs =
-- @List.rec _ _ H₆ (λ (x : (_ : α) × Raw₀ α β) xs acc => H₇ x.1 x.2 (.ofList xs)
-- (@rec α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ x.2) acc) xs.toList := by
--   induction xs; rfl; nm i x xs ih; simp [ih]; rw [DHashMap.Internal.AssocList.ofList_toList]

-- noncomputable
-- def depthAux (t : Raw₀ α β) : ℕ :=
--   let f := @t.recOn
--   @f (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
--     (λ _ => 0)
--     (λ _ n => n)
--     (λ n _ m => max n m)
--     (λ _ n => n)
--     0 (λ _ _ n m => max n m)
--     0 (λ _ _ _ n m => max (n + 1) m)

-- theorem depthAux_le {mp : DHashMap.Raw α (λ _ => Raw₀ α β)} {k}
-- (wf : mp.WF) (h : mp.get? k = some t) : t.depthAux < (node mp).depthAux := by
--   classical
--   nth_rw 2 [depthAux]
--   simp
--   simp only [rec_3_eq, rec_4_eq, List.rec_eq_foldr, List.foldr_max_eq_max?_map']
--   generalize hb : mp.2.toList = bs
--   change _ < (0 :: bs.map (λ x => (0 :: x.toList.map
--     (λ x => x.snd.depthAux + 1)).max?.getD 0)).max?.getD 0
--   simp
--   generalize hf : (λ (x : DHashMap.Internal.AssocList α # λ _ => Raw₀ α β) =>
--     (x.toList.map (λ x => x.snd.depthAux + 1)).max?.elim 0 (max 0)) = f
--   obtain ⟨b, h₁, h₂⟩ := wf.mp.mem_bucket_of_get?_eq_some h
--   replace h₁ : b ∈ bs; simpa [←hb]
--   generalize hb' : b :: bs.erase b = bs'
--   have h₃ : bs.Perm bs'; simpa [←hb']
--   rw [List.max?_eq_max?_of_perm (ys := bs'.map f) # h₃.map f]
--   simp [←hb']
--   suffices h₄ : t'.depthAux < f b
--   · cases ((bs.erase b).map f).max? <;> simp [h₄]
--   subst hf
--   dsimp
--   clear! val h wf bs bs'
--   generalize hx : b.toList.map (λ x => x.2.depthAux + 1) = xs
--   replace h₂ : (t'.depthAux + 1) ∈ xs
--   · rw [←hx, List.mem_map]; use ⟨k, t'⟩
--   clear k
--   cases h₃ : xs.max?
--   · simp at h₃; simp [h₃] at h₂
--   simp; linarith [List.le_max? h₂ h₃]

-- #check 0 #exit

-- theorem depthAux_le_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw₀ α β)}
-- (wf : (mk val mp).WF) {k : α} {t : Raw₀ α β} (h : mp.get? k = some t) :
-- t.depthAux < (mk val mp).depthAux := depthAux_le h
-- 
-- set_option linter.unusedVariables false in
-- def recAux {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) (wf : t.WF)
-- (motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
-- mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : γ t :=
--   match t with
--   | .mk val mp => motive val mp wf.mp #
--     λ i t h => t.recAux (wf.get1? h) motive
-- termination_by t.depthAux
-- decreasing_by exact depthAux_le h
-- 
-- def rec' {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) [wf : t.WF]
-- (motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
-- mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)) : γ t :=
--   t.recAux wf motive
-- 
-- def depth (t : Raw₀ α β) [wf : t.WF] : ℕ :=
--   t.rec' # λ _ mp h₁ f => (mp.foldWith h₁ · 0) # λ acc i x h₂ =>
--   max acc # 1 + f i x h₂
-- 
-- def empty : Raw₀ α β := ⟨none, ∅⟩
-- 
-- instance : EmptyCollection (Raw₀ α β) := ⟨empty⟩
-- theorem empty_def : (∅ : Raw₀ α β) = ⟨none, ∅⟩ := rfl
-- 
-- instance : (∅ : Raw₀ α β).WF := by
--   constructor <;> simp
-- 
-- @[simp]
-- theorem rec'_mk {γ : Raw₀ α β → Sort*} {val mp} [wf : (⟨val, mp⟩ : Raw₀ α β).WF]
-- {motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw₀ α β)),
-- mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (mk val mp)} :
-- (⟨val, mp⟩ : Raw₀ α β).rec' motive =
-- motive val mp wf.mp (λ _ t h => t.rec' (wf := wf.get1? h) motive) := by
--   simp_rw [rec', recAux]
-- 
-- @[simp]
-- theorem depth_mk {val mp} [wf : (⟨val, mp⟩ : Raw₀ α β).WF] :
-- (⟨val, mp⟩ : Raw₀ α β).depth = mp.foldWith wf.mp
-- (λ acc _ (t' : Raw₀ α β) h => max acc # 1 + t'.depth (wf := wf.get1? h)) 0 := by
--   unfold depth; simp
-- 
-- @[simp]
-- theorem depth_empty : (∅ : Raw₀ α β).depth = 0 := by
--   simp [empty_def]
-- 
-- theorem depth_lt [wf : t.WF] {k t'} (h : t.mp.get? k = some t') :
-- t'.depth (wf := wf.get1? h) < t.depth := by
--   classical
--   rcases t with ⟨val, mp⟩
--   simp at h ⊢
--   have h₁ := DHashMap.Raw.mem_toList_iff_get?_eq_some wf.mp |>.mpr h
--   dsimp at h₁
--   have h₂ := wf.get1? h
--   rw [DHashMap.Raw.foldWith_eq_foldlWith_toList, List.foldlWith_max_eq_max?_mapWith]
--   apply Nat.lt_of_succ_le
--   change (⟨k, t'⟩ : Σ _, _).snd.depth + 1 ≤ _
--   apply List.le_elim_max_max?_of_mem
--   simp
--   use k, t', h₁
--   rw [add_comm]
-- 
-- theorem WF.of_mem_toList {p} [wf : t.WF] (h : p ∈ t.mp.toList) : p.2.WF := by
--   rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wf.mp] at h; exact wf.get1? h
-- 
-- theorem wf_iff : t.WF ↔ t.mp.WF ∧ ∀ k t₁, t.mp.get? k = some t₁ → t₁.WF ∧ ¬t₁.isEmpty := by
--   rcases t with ⟨val, mp⟩; constructor
--   · rintro ⟨h₁, h₂, h₃⟩; tauto
--   · rintro ⟨h₁, h₂⟩; use h₁ <;> intro k t₁ h₃ <;> specialize h₂ k _ _ <;> tauto
-- 
-- def setVal (t : Raw₀ α β) (val : Option β) : Raw₀ α β :=
--   ⟨val, t.mp⟩
-- 
-- @[simp]
-- theorem setVal_mk {val val₁ mp} : (⟨val, mp⟩ : Raw₀ α β).setVal val₁ = ⟨val₁, mp⟩ := rfl
-- 
-- @[simp]
-- instance {x} [wf : t.WF] : WF # t.setVal x := by
--   rcases t with ⟨val, mp⟩
--   rcases wf with ⟨h₁, h₂, h₃⟩
--   dsimp; use h₁
-- 
-- @[simp] theorem val_setVal {val} : (t.setVal val).val = val := rfl
-- @[simp] theorem mp_setVal {val} : (t.setVal val).mp = t.mp := rfl
-- 
-- def erase1 (t : Raw₀ α β) (i : α) : Raw₀ α β :=
--   ⟨t.val, t.mp.erase i⟩
-- 
-- @[simp]
-- theorem erase1_mk {val mp i} : (⟨val, mp⟩ : Raw₀ α β).erase1 i = ⟨val, mp.erase i⟩ := rfl
-- 
-- @[simp] theorem val_erase1 {i} : (t.erase1 i).val = t.val := rfl
-- @[simp] theorem mp_erase1 {i} : (t.erase1 i).mp = t.mp.erase i := rfl
-- 
-- @[simp]
-- instance {i} [wf : t.WF] : WF # t.erase1 i := by
--   rcases t with ⟨val, mp⟩
--   rw [wf_iff] at wf ⊢
--   dsimp at wf ⊢
--   rcases wf with ⟨h₁, h₂⟩
--   use h₁.erase
--   intro k t₁ h₃
--   apply h₂ k t₁
--   rw [DHashMap.Raw.get?_erase h₁] at h₃
--   simp at h₃; exact h₃.2
-- 
-- def insert1 (t : Raw₀ α β) (i : α) (t₁ : Raw₀ α β) : Raw₀ α β :=
--   if t₁.isEmpty then t.erase1 i else ⟨t.val, t.mp.insert i t₁⟩
-- 
-- theorem insert1_mk {val mp i t₁} : (⟨val, mp⟩ : Raw₀ α β).insert1 i t₁ =
-- ⟨val, if t₁.isEmpty then mp.erase i else mp.insert i t₁⟩ := by
--   unfold insert1; split_ifs <;> rfl
-- 
-- @[simp]
-- theorem val_insert1 {i t₁} : (t.insert1 i t₁).val = t.val := by
--   cases t; simp [insert1_mk]
-- 
-- theorem mp_insert1 {i} : (t.insert1 i t₁).mp =
-- if t₁.isEmpty then t.mp.erase i else t.mp.insert i t₁ := by
--   cases t; simp [insert1_mk]
-- 
-- @[simp]
-- instance {i} [wf : t.WF] [wf₁ : t₁.WF] : WF # t.insert1 i t₁ := by
--   dsimp [insert1]
--   split_ifs with h
--   · infer_instance
--   rw [wf_iff] at wf ⊢
--   rcases wf with ⟨h₁, h₂⟩
--   dsimp
--   use h₁.insert
--   intro k t₂ h₃
--   rw [DHashMap.Raw.get?_insert h₁] at h₃
--   simp at h₃
--   split_ifs at h₃ with h₄
--   · simp at h₃
--     subst h₃
--     use wf₁
--   exact h₂ _ _ h₃
-- 
-- def get1? (t : Raw₀ α β) (i : α) : Option (Raw₀ α β) :=
--   t.mp.get? i
-- 
-- theorem get1?_erase1 {i j} [wf : t.WF] :
-- (t.erase1 i).get1? j = if i = j then none else t.get1? j := by
--   simp [get1?, DHashMap.Raw.get?_erase wf.mp]
-- 
-- theorem get1?_insert1 {i j} {t₁ : Raw₀ α β} [wf : t.WF] :
-- (t.insert1 i t₁).get1? j = if i = j then
-- if t₁.isEmpty then none else some t₁ else t.get1? j := by
--   unfold insert1
--   by_cases h : t₁.isEmpty <;> simp [h]
--   · rw [get1?_erase1]
--   · simp [get1?, DHashMap.Raw.get?_insert wf.mp]
-- 
-- @[simp]
-- theorem get1?_erase1_eq_some_iff {i j} [wf : t.WF] :
-- (t.erase1 i).get1? j = some t₁ ↔ i ≠ j ∧ t.get1? j = t₁ := by
--   rw [get1?_erase1]; split_ifs with h <;> simp [h]