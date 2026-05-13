import Projects.Util.Data.Set

namespace Nat

-- #check 0 #exit

end Nat

namespace Option

variable {α β γ : Type*}

-- #check 0 #exit

end Option

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

-- #check 0 #exit

end List

namespace Std.DHashMap

variable {α : Type*} {β : α → Type*} {γ : Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : DHashMap α β}

-- #check 0 #exit

end Std.DHashMap

namespace Std.DHashMap.Raw

variable {α : Type*} {β : α → Type*} {γ : Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Raw α β} {wf : mp.WF}
  {f : γ → (i : α) → (x : β i) → mp.get? i = some x → γ} {z : γ}

-- #check 0 #exit

end Std.DHashMap.Raw

namespace LeafTrie

open Std

inductive Raw₀ (α β : Type*) [DecidableEq α] [Hashable α] where
| leaf : β → Raw₀ α β
| node : DHashMap.Raw α (λ _ => Raw₀ α β) → Raw₀ α β

namespace Raw₀

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t' t₁ t₂ t₃ : Raw₀ α β}

@[simp]
def isLeaf (t : Raw₀ α β) : Bool := match t with
| .leaf _ => true
| _ => false

@[simp]
def isNode (t : Raw₀ α β) : Bool := match t with
| .node _ => true
| _ => false

@[class]
inductive WF : Raw₀ α β → Prop where
| leaf {x} : WF # .leaf x
| node {mp : _} : DHashMap.Raw.WF mp → (∀ k t₁, mp.get? k = some t₁ → WF t₁) → WF (.node mp)

attribute [simp, instance] WF.leaf

variable {val : β}
variable {mp₁ : DHashMap.Raw α λ _ => Raw₀ α β}

theorem rec_3_eq {xs : List (DHashMap.Internal.AssocList α (λ _ => Raw₀ α β))}
{M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈} :
@rec_3 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ xs =
@List.rec _ _ H₅ (λ x xs acc => H₆ x xs
(@rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ x) acc) xs := by
  induction xs; rfl; nm x xs ih; dsimp; rw [ih]

theorem rec_4_eq {xs : DHashMap.Internal.AssocList α (λ _ => Raw₀ α β)}
{M₁ M₂ M₃ M₄ M₅ H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈} :
@rec_4 α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ xs =
@List.rec _ _ H₇ (λ (x : (_ : α) × Raw₀ α β) xs acc => H₈ x.1 x.2 (.ofList xs)
(@rec α β ha₁ ha₂ M₁ M₂ M₃ M₄ (λ _ => M₅) H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ x.2) acc) xs.toList := by
  induction xs; rfl; nm i x xs ih; simp [ih]; rw [DHashMap.Internal.AssocList.ofList_toList]

noncomputable
def depthAux (t : Raw₀ α β) : ℕ :=
  let r := @t.rec; r (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
  (λ _ => 0)               -- leaf
  (λ _ n => n + 1)         -- node
  (λ _ _ n => n)           -- std raw
  (λ _ n => n)             -- array
  0                        -- list nil
  (λ _ _ n m => max n m)   -- list cons
  0                        -- assoc list nil
  (λ _ _ _ n m => max n m) -- assoc list cons

@[simp]
theorem depthAux_leaf {x} : (leaf x : Raw₀ α β).depthAux = 0 := by
  simp [depthAux]

theorem depthAux_lt_of_mem {mp i t} (h : mp.get? i = some t) :
t.depthAux < (node mp : Raw₀ α β).depthAux := by
  nth_rw 2 [depthAux]
  simp [rec_3_eq, rec_4_eq, Order.lt_add_one_iff]
  generalize hb : mp.2.toList = bs
  simp only [List.rec_eq_foldr, List.foldr_max_eq_max?_map]
  generalize hf : (λ (x : DHashMap.Internal.AssocList α # λ _ => Raw₀ α β) => _) = f
  change (λ x => (x.toList.map (λ x => x.snd.depthAux)).max?.elim 0 (max 0)) = f at hf
  simp at hf ⊢
  rw [List.max?_eq_some_max]
  rotate_left
  · simp
    rintro rfl
    simp at hb
    simp [DHashMap.Raw.get?] at h
    obtain ⟨h₁, h₂⟩ := h
    simp [hb] at h₁
  simp
  apply List.le_max_of_le_mem
  subst hf hb
  simp
  simp [DHashMap.Raw.get?] at h
  choose h₁ h₂ using h
  simp [DHashMap.Internal.Raw₀.get?] at h₂
  generalize hj : (DHashMap.Internal.mkIdx _ h₁ (hash i) : USize).toNat = j
  simp [hj] at h₂
  generalize_proofs hh₁ hh₂ at h₂
  generalize hb : mp.buckets[j] = b at h₂
  rw [Internal.List.getValueCast?_eq_some_iff] at h₂
  choose h₂ h₃ using h₂
  have h₄ := Internal.List.getValueCast_mem h₂
  rw [h₃] at h₄
  use b
  simp [←hb]
  rw [List.max?_eq_some_max]
  rotate_left
  · simp
    grind
  simp
  apply List.le_max_of_mem
  simp
  grind

def get? (t : Raw₀ α β) (k : α) : Option (Raw₀ α β) :=
  match t with
  | leaf _ => none
  | node mp => mp.get? k

theorem WF.mp [H : (Raw₀.node mp₁).WF] : mp₁.WF := by
  cases H; tauto

theorem WF.mp_get? {k t} [H : (Raw₀.node mp₁).WF] (h : mp₁.get? k = some t) : t.WF := by
  cases H; tauto

theorem WF.get? {k t} [H : (Raw₀.node mp₁).WF] (h : (Raw₀.node mp₁).get? k = some t) : t.WF := by
  cases H; tauto

def recAux {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) (wf : t.WF) (motive₁ : ∀ val, γ (leaf val))
(motive₂ : ∀ mp, mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (node mp)) : γ t :=
  match t with
  | leaf val => motive₁ val
  | node mp => motive₂ mp wf.mp # λ i t h => t.recAux (wf.mp_get? h) motive₁ motive₂
termination_by t.depthAux
decreasing_by exact depthAux_lt_of_mem h

def rec' {γ : Raw₀ α β → Sort*} (t : Raw₀ α β) [wf : t.WF] (motive₁ : ∀ val, γ (leaf val))
(motive₂ : ∀ mp, mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (node mp)) : γ t :=
  t.recAux wf motive₁ motive₂

def depth (t : Raw₀ α β) [wf : t.WF] : ℕ :=
  t.rec' (γ := λ _ => ℕ) (λ _ => 0) # λ mp wf f =>
  1 + mp.foldWith wf (z := 0) λ acc k t h => max acc # f k t h

def empty : Raw₀ α β := node ∅

instance : EmptyCollection (Raw₀ α β) := ⟨empty⟩
theorem empty_def : (∅ : Raw₀ α β) = node ∅ := rfl

@[instance]
theorem WF.empty : (∅ : Raw₀ α β).WF := by
  constructor <;> simp

@[simp]
theorem rec'_leaf {γ : Raw₀ α β → Sort*} {motive₁ : ∀ val, γ (leaf val)} {motive₂} :
(leaf val).rec' motive₁ motive₂ = motive₁ val := by
  simp [rec', recAux]

@[simp]
theorem rec'_node {γ : Raw₀ α β → Sort*} [wf : (node mp₁).WF] {motive₁}
{motive₂ : ∀ mp, mp.WF → (∀ i t, mp.get? i = some t → γ t) → γ (node mp)} :
(node mp₁).rec' motive₁ motive₂ = motive₂ mp₁ wf.mp λ _ t h =>
t.recAux (wf.mp_get? h) motive₁ motive₂ := by
  simp [rec', recAux]

@[simp]
theorem depth_leaf {val} : (leaf val : Raw₀ α β).depth = 0 := by
  simp [depth]

@[simp] theorem get?_leaf {x k} : (leaf x : Raw₀ α β).get? k = none := rfl
@[simp] theorem get?_node {mp k} : (node mp : Raw₀ α β).get? k = mp.get? k := rfl

theorem get?_eq_some_iff {k} : t.get? k = some t₁ ↔ ∃ mp, node mp = t ∧ mp.get? k = t₁ := by
  cases t <;> simp

theorem WF.of_mp_get? {k} [wf : (Raw₀.node mp₁).WF] (h : mp₁.get? k = some t) : t.WF := by
  cases wf; tauto

theorem WF.of_get? {k} [wf : t.WF] (h : t.get? k = some t₁) : t₁.WF := by
  cases wf <;> simp_all; tauto

theorem depth_node {mp} [wf : (node mp : Raw₀ α β).WF] :
(node mp).depth = 1 + mp.foldWith wf.mp (z := 0)
λ acc _ t h => max acc # t.depth (wf := wf.of_mp_get? h) := by
  simp [depth]; congr

@[simp]
theorem depth_empty : (∅ : Raw₀ α β).depth = 1 := by
  simp [empty_def, depth_node]

theorem depth_lt_of_mp_get? {k} [wf : (node mp₁).WF] (h : mp₁.get? k = some t) :
t.depth (wf := wf.of_mp_get? h) < (node mp₁).depth := by
  simp [depth_node]
  have h₁ := wf.mp
  have h₂ := mp₁.mem_toList_iff_get?_eq_some (h := h₁) |>.mpr h
  have h₃ := @mp₁.le_foldWith_max
  exact @h₃ ha₁ ha₂ ℕ _ k t 0 (λ i t h => t.depth (wf := wf.of_mp_get? h)) h₁ h

theorem depth_lt_of_get? {k} [wf : t.WF] (h : t.get? k = some t₁) :
t₁.depth (wf := wf.of_get? h) < t.depth := by
  obtain ⟨mp, rfl, h₁⟩ := get?_eq_some_iff.mp h
  exact depth_lt_of_mp_get? h

theorem WF.of_mem_toList {mp p} [wf : (.node mp : Raw₀ α β).WF] (h : p ∈ mp.toList) : p.2.WF := by
  rw [DHashMap.Raw.mem_toList_iff_get?_eq_some wf.mp] at h; exact wf.get? h

theorem wf_iff : t.WF ↔ (∃ x, leaf x = t) ∨
(∃ mp, node mp = t ∧ mp.WF ∧ ∀ k t₁, mp.get? k = some t₁ → t₁.WF) := by
  constructor
  · rintro (h | h) <;> tauto
  · rintro (⟨_, rfl, _⟩ | ⟨mp, rfl, h₁, h₂⟩) <;> constructor <;> assumption

theorem wf_node_iff {mp} : (node mp : Raw₀ α β).WF ↔
mp.WF ∧ ∀ k t₁, mp.get? k = some t₁ → t₁.WF := by
  rw [wf_iff]; simp

-- #check 0 #exit

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