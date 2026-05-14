import Projects.Util.Data.Set

section Logic

variable {α β γ : Type*}

theorem dite_true_eq! : @dite α True = λ _ f _ => f trivial := by
  funext; simp

theorem dite_false_eq! : @dite α False = λ _ _ g => g not_false := by
  funext; simp

-- #check 0 #exit

end Logic

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

theorem flatMap_eq_flatten_map {f : α → List β} : xs.flatMap f = (xs.map f).flatten := by
  exact flatMap_def

theorem foldr_fn_append_eq_flatMap {f : α → List β} {zs} :
xs.foldr (λ x acc => f x ++ acc) zs = xs.flatMap f ++ zs := by
  cases xs <;> simp; rfl

theorem map_eq_map_attach {f : α → β} : xs.map f = xs.attach.map (λ x => f x.1) := by
  simp

@[simp]
theorem getElem?_singleton_eq_some_iff {x y : α} {i} : [x][i]? = some y ↔ i = 0 ∧ x = y := by
  grind

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

omit hh₁ hh₂ in @[simp]
theorem assocList_foldr_nil {f : (x : α) → β x → γ → γ} {z} :
Internal.AssocList.nil.foldr f z = z := rfl

omit hh₁ hh₂ in @[simp]
theorem assocList_foldr_cons {f : (x : α) → β x → γ → γ} {k x z} {bs} :
(Internal.AssocList.cons k x bs).foldr f z =
f k x (bs.foldr f z) := rfl

omit hh₁ hh₂ in @[simp]
theorem assocList_foldr_eq_foldr_toList
{bs : Internal.AssocList α β} {f : (x : α) → β x → γ → γ} {z} :
bs.foldr f z = bs.toList.foldr (λ x => f x.1 x.2) z := by
  induction bs generalizing z <;> simp
  nm k x bs ih; grind

omit hh₁ hh₂ in
theorem foldr_foldr_eq_foldr_flatMap_buckets_list {bs : List (Internal.AssocList α β)} :
bs.foldr (λ x y => DHashMap.Internal.AssocList.foldr
(λ a b d => Sigma.mk a b :: d) y x) [] = bs.flatMap (·.toList) := by
  simp; rfl

omit hh₁ hh₂ in
theorem foldr_foldr_eq_foldr_flatMap_buckets_array {bs : Array (Internal.AssocList α β)} :
bs.foldr (λ x y => DHashMap.Internal.AssocList.foldr
(λ a b d => Sigma.mk a b :: d) y x) [] = bs.toList.flatMap (·.toList) := by
  rcases bs with ⟨bs⟩
  simp only [assocList_foldr_eq_foldr_toList, Sigma.eta, List.foldr_cons_eq_append',
    List.size_toArray, List.foldr_toArray', List.foldr_append_eq_append, List.append_nil,
    List.flatMap_eq_flatten_map]

omit hh₁ hh₂ in @[simp]
theorem assocList_foldrM_Id_eq_foldr_toList
{bs : Internal.AssocList α β} {f : (x : α) → β x → γ → γ} {z} :
bs.foldrM (m := Id) f z = bs.toList.foldr (λ x => f x.1 x.2) z :=
  assocList_foldr_eq_foldr_toList

omit hh₁ hh₂ in open Classical in
theorem assocList_foldrM_eq!.{u, v, w} : @Internal.AssocList.foldrM.{w, v, u, w} =
λ (α : Type u) (β : α → Type v) (γ : Type w) (m : Type w → Type w) [H : Monad m]
(f : (x : α) → β x → γ → m γ) (z : γ) (bs : Internal.AssocList α β) =>
if h : m = Id ∧ H ≍ Id.instMonad then by
  rcases h with ⟨rfl, h⟩
  exact bs.toList.foldr (λ x => f x.1 x.2) z
else bs.foldrM f z := by
  funext α β γ m H f z bs
  simp only [right_eq_dite_iff, forall_and_index]
  rintro rfl
  revert f
  simp only [Id]
  rintro f rfl
  simp [-Id.instMonad]
  generalize_proofs H
  cases H
  rfl

omit hh₁ hh₂ in
theorem toList_eq_flatMap_buckets : mp.toList = mp.buckets.toList.flatMap (·.toList) := by
  rw [toList, Internal.foldRev, Internal.foldRevM, ←Array.foldrM_toList]
  generalize mp.buckets.toList = xs; clear! mp
  simp only [Id.run, pure, assocList_foldrM_Id_eq_foldr_toList, Sigma.eta,
    List.foldr_cons_eq_append']
  rw [List.foldrM_eq_foldr]; unfold Id Id.instMonad
  simp only [pure, bind, List.foldr_append_eq_append, List.append_nil]; rfl

omit hh₂ in
theorem of_getCast?_eq_some {xs : Internal.AssocList α β} {k x}
(h : xs.getCast? k = some x) : ⟨k, x⟩ ∈ xs.toList := by
  induction xs generalizing k x <;> simp at h ⊢
  nm r y xs ih
  rw [Internal.List.getValueCast?_cons] at h
  simp at h
  split_ifs at h with h₁
  · subst h₁
    simp at h
    subst h
    simp
  right
  simp_rw [Internal.AssocList.getCast?_eq] at ih
  tauto

theorem distinct_keys_of_mem_buckets {xs} (wf : mp.WF) (h : xs ∈ mp.buckets) :
∀ k x y, ⟨k, x⟩ ∈ xs.toList → ⟨k, y⟩ ∈ xs.toList → x = y := by
  intro k x y h₁ h₂
  generalize h₃ : DHashMap.mk mp wf = mp₁
  have h₄ : ∀ ⦃z⦄, z ∈ xs.toList → z ∈ mp₁.toList
  · intro z hz
    rw [DHashMap.toList, toList_eq_flatMap_buckets]
    simp
    grind
  replace h₁ := h₄ h₁
  replace h₂ := h₄ h₂
  rw [DHashMap.mem_toList_iff_get?_eq_some] at h₁ h₂
  grind

theorem distinct_keys_of_mem_toList_buckets {xs} (wf : mp.WF) (h : xs ∈ mp.buckets.toList) :
∀ k x y, ⟨k, x⟩ ∈ xs.toList → ⟨k, y⟩ ∈ xs.toList → x = y := by
  simp at h; exact distinct_keys_of_mem_buckets wf h

omit hh₂ in
theorem getCast?_eq_some_iff {xs : Internal.AssocList α β} {k x}
(h : ∀ k x y, ⟨k, x⟩ ∈ xs.toList → ⟨k, y⟩ ∈ xs.toList → x = y) :
xs.getCast? k = some x ↔ ⟨k, x⟩ ∈ xs.toList := by
  constructor; use of_getCast?_eq_some
  rw [Internal.AssocList.getCast?_eq]
  intro h₁
  induction xs generalizing k x <;> simp at h₁
  nm r y xs ih
  rcases h₁ with ⟨rfl, h₁⟩ | h₁
  · simp at h₁
    simp [h₁]
  simp
  rw [Internal.List.getValueCast?_cons]
  simp
  split_ifs with h₂
  · subst h₂
    simp
    tauto
  apply ih _ h₁
  tauto

theorem getCast?_eq_some_iff_of_mem_buckets {xs k x} (wf : mp.WF)
(h : xs ∈ mp.buckets) : xs.getCast? k = some x ↔ ⟨k, x⟩ ∈ xs.toList :=
  getCast?_eq_some_iff # distinct_keys_of_mem_buckets wf h

theorem get?_eq_some_iff_mem_toList {k x} (wf : mp.WF) :
mp.get? k = some x ↔ ⟨k, x⟩ ∈ mp.toList := by
  generalize h₁ : DHashMap.mk mp wf = mp₁
  convert_to mp₁.get? k = some x ↔ ⟨k, x⟩ ∈ mp₁.toList
  · subst h₁
    rw [get?, DHashMap.get?]
    grind
  · subst h₁
    rfl
  simp

omit hh₁ hh₂ in @[simp]
theorem assocList_toList_eq_nil_iff {xs : Internal.AssocList α β} :
xs.toList = [] ↔ xs = .nil := by
  unfold Internal.AssocList.toList; split <;> simp

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
  · simp only [ne_eq, List.map_eq_nil_iff]; grind
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

-- theorem depthAux_eq_depth [wf : t.WF] : t.depthAux = t.depth := by
--   classical
--   suffices h : ∀ (wf : t.WF), t.depthAux = t.depth; tauto
--   apply @t.rec' (wf := wf) (γ := λ t => ∀ (wf : t.WF), t.depthAux = t.depth) <;> clear! t
--   ·
--     intro x wf
--     simp
--   intro mp wf₁ ih wf₂
--   unfold depthAux
--   simp [rec_3_eq, rec_4_eq]
--   generalize hb : mp.2.toList = bs
--   simp only [List.rec_eq_foldr, List.foldr_max_eq_max?_map]
--   generalize hf : (λ (x : DHashMap.Internal.AssocList α # λ _ => Raw₀ α β) => _) = f
--   change (λ x => (x.toList.map (λ x => x.snd.depthAux)).max?.elim 0 (max 0)) = f at hf
--   simp at hf ⊢
--   
--   rw [wf_node_iff] at wf₂
--   obtain ⟨wf₂, wf₃⟩ := wf₂
--   
--   -- by_cases h₁ : mp.isEmpty
--   -- ·
--   --   rw [←DHashMap.Raw.toList_eq_nil_iff_isEmpty wf₂] at h₁
--   -- 
--   -- rw [List.max?_eq_some_max]
--   -- rotate_left
--   -- · simp
--   --   rintro rfl
--   --   simp at hb
--   --   simp [DHashMap.Raw.get?] at h
--   --   obtain ⟨h₁, h₂⟩ := h
--   --   simp [hb] at h₁
--   -- simp
--   -- apply List.le_max_of_le_mem
--   -- subst hf hb
--   
--   rw [depth_node, Nat.add_comm 1]
--   simp
--   
--   rw [DHashMap.Raw.foldWith_eq_foldlWith_toList, List.foldlWith_max_eq_max?_mapWith]
--   simp
--   
--   rw! [DHashMap.Raw.toList, DHashMap.Raw.Internal.foldRev,
--     DHashMap.Raw.Internal.foldRevM]
--   simp [pure, Id.run]
--   
--   trans
--     ((mp.buckets.foldr (λ x1 x2 => DHashMap.Internal.AssocList.foldrM (m := Id)
--     (λ a b d => ⟨a, b⟩ :: (d : List ((_ : α) × Raw₀ α β))) x2 x1) []).mapWith
--           λ x h =>
--           haveI : x.2.WF := (
--             by
--               simp only [DHashMap.Raw.assocList_foldrM_Id_eq_foldr_toList, Sigma.eta,
--                 List.foldr_cons_eq_append'] at h
--               rw [←Array.foldr_toList, hb] at h
--               dsimp [Id] at h
--               rw [List.foldr_fn_append_eq_flatMap] at h
--               simp at h
--               obtain ⟨xs, h₁, h₂⟩ := h
--               rcases x with ⟨x, t₁⟩
--               dsimp
--               apply wf₃ x t₁
--               rw [DHashMap.Raw.get?_eq_some_iff_mem_toList wf₂]
--               rw [DHashMap.Raw.toList_eq_flatMap_buckets]
--               simp; grind
--           ); x.2.depth).max?.elim
--     0 id
-- 
-- -- #check 0 #exit
--   
--   on_goal 2 => congr
--   rw [List.mapWith_eq_map]
--   simp
--   split_ifs with h₁
--   ·
--     simp at h₁ ⊢
--     unfold Id at h₁
--     rw [←Array.foldr_toList] at h₁
--     rw [List.foldr_fn_append_eq_flatMap] at h₁
--     simp at h₁
--     clear ih; nm x; clear x
--     clear wf₂
--     have h₂ : bs.map f = bs.map (λ _ => 0)
--     ·
--       rw [List.map_eq_map_iff]
--       subst hf
--       simp
--       intro b₁ hb₁
--       specialize h₁ b₁ (by grind)
--       simp [h₁]
--     rw [h₂]
--     clear! f
--     simp
--     rw [List.max?_replicate]
--     grind
--   
--   unfold Id Id.instMonad
--   iterate 2 rw! [←Array.foldr_toList]
--   iterate 2 rw! [List.foldr_fn_append_eq_flatMap]
--   simp
--   rw! [←DHashMap.Raw.toList_eq_flatMap_buckets]
--   generalize hb₁ : Array.mk bs = bs₁
--   subst hb
--   rename' bs₁ => bs
--   simp at hb₁
--   simp [hb₁]
--   clear h₁
--   nm x; clear x
--   
--   rw! [DHashMap.Raw.toList_eq_flatMap_buckets, hb₁]
--   rw! [List.map_flatMap, List.map_eq_flatMap, List.flatMap, List.flatMap]
--   nth_rw 1 [List.map_eq_map_attach]
--   nth_rw 2 [List.map_eq_map_attach]
--   
--   congr 1
--   
--   sorry