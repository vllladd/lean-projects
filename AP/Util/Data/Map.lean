import AP.Util.Data.DMap

universe u v w

structure Map (α : Type u) (β : Type v)
[hh₁ : DecidableEq α] [hh₂ : Hashable α] : Type (max u v) where
  inner : Std.ExtDHashMap α (λ _ => β)
deriving Inhabited

variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Map α β}

namespace Map

open Std.DHashMap

def empty : Map α β := ⟨∅⟩

instance : EmptyCollection (Map α β) := ⟨empty⟩

theorem empty_def : (∅ : Map α β) = ⟨∅⟩ := rfl

def insertP (x : α × β) (mp : Map α β) : Map α β :=
  ⟨insert x.toSigma mp.inner⟩

instance : Insert (α × β) (Map α β) := ⟨insertP⟩

theorem insert_def {x : α × β} {mp : Map α β} :
insert x mp = ⟨insert x.toSigma mp.inner⟩ := rfl

@[simp]
protected def insert (mp : Map α β) (i : α) (x : β) : Map α β :=
  ⟨mp.inner.insert i x⟩

def ofList (xs : List (α × β)) : Map α β :=
  ⟨.ofList # xs.map Prod.toSigma⟩

def get? (i : α) (mp : Map α β) : Option β :=
  mp.inner.get? i

def get! (i : α) [h : Inhabited β] (mp : Map α β) : β :=
  mp.inner.get! i

def map (mp : Map α β) (f : α → β → γ) : Map α γ :=
  ⟨mp.inner.map f⟩

def mem (mp : Map α β) (i : α) : Prop :=
  i ∈ mp.inner

instance : Membership α (Map α β) := ⟨mem⟩

theorem mem_def {i} : i ∈ mp ↔ i ∈ mp.inner := by rfl

instance {i} : Decidable (mp.mem i) := by
  unfold mem; infer_instance

instance {i} : Decidable (i ∈ mp) := by
  change Decidable # mp.mem i; infer_instance

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x :=
  Std.ExtDHashMap.mem_iff_get?_eq_some

theorem get?_eq_some_of_mem {i : α} (h : i ∈ mp) : ∃ x, mp.get? i = some x :=
  Std.ExtDHashMap.get?_eq_some_of_mem h

theorem get?_eq_none_of_not_mem {i : α} (h : i ∉ mp) : mp.get? i = none :=
  Std.ExtDHashMap.get?_eq_none_of_not_mem h

@[simp]
theorem get?_eq_none_iff {i} : mp.get? i = none ↔ i ∉ mp :=
  Std.ExtDHashMap.get?_eq_none_iff

theorem get?_map {f : α → β → γ} {i : α} :
(mp.map f).get? i = (mp.get? i).map (f i) :=
  Std.ExtDHashMap.get?_map

theorem get!_map_eq_of_pos {f : α → β → γ} {i : α}
[ha : Inhabited β] [hb : Inhabited γ]
(h : i ∈ mp) : (mp.map f).get! i = f i (mp.get! i) := by
  rcases mp with ⟨⟨mp⟩⟩
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  induction mp using Quotient.inductionOn
  simp [get?] at hx
  simp [get!, Std.ExtDHashMap.get!_eq_get?, map, hx]

def toList [LinearOrder α] (mp : Map α β) : List (α × β) :=
  mp.inner.lift (λ m => m.toSortedList.map Sigma.toProd) #
    by simp

@[simp]
theorem ofList_nil : ofList (α := α) (β := β) [] = ∅ := rfl

@[simp]
theorem ofList_snoc {xs} {x : α × β} :
ofList (xs ++ [x]) = (ofList xs).insertP x := by
  unfold insertP ofList; simp

@[simp]
theorem toList_empty [LinearOrder α] : (∅ : Map α β).toList = [] := by
  change List.map _ _ = _; simp [toSortedList]

@[simp]
theorem mem_insertP {x : α × β} {i} :
i ∈ mp.insertP x ↔ i = x.1 ∨ i ∈ mp :=
  Std.ExtDHashMap.mem_insert'

@[simp]
theorem mem_insert' {i x j} :
j ∈ mp.insert i x ↔ j = i ∨ j ∈ mp := by
  simp [mem_def]; tauto

@[simp]
theorem mem_insert {x i} :
i ∈ Insert.insert x mp ↔ i = x.1 ∨ i ∈ mp :=
  mem_insert'

@[simp]
theorem mem_ofList {xs : List (α × β)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  induction xs using List.ind_pair_sigma; simp [ofList]
  exact Std.ExtDHashMap.mem_ofList'

@[simp]
theorem mem_map {f : α → β → γ} {i} :
i ∈ mp.map f ↔ i ∈ mp := by
  simp [mem_def, map]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  rcases mp with ⟨mp⟩; simp [empty_def]
  exact Std.ExtDHashMap.eq_empty_iff

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : Map α β).mem i :=
  Std.ExtDHashMap.not_mem_empty

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : Map α β) :=
  not_mem_empty'

theorem ext_iff' {m₁ m₂ : Map α β} :
m₁ = m₂ ↔ m₁.inner.1.out ~m m₂.inner.1.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.ext_iff'

theorem ext' {m₁ m₂ : Map α β}
(h : m₁.inner.1.out ~m m₂.inner.1.out) : m₁ = m₂ := by
  rwa [ext_iff']

theorem ext_iff {m₁ m₂ : Map α β} : m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.ext_iff

@[ext]
theorem ext {m₁ m₂ : Map α β} (h : ∀ i, m₁.get? i = m₂.get? i) : m₁ = m₂ := by
  rwa [ext_iff]

theorem get?_eq_ite_of_unit {m : Map α Unit} {i} :
m.get? i = if i ∈ m then some () else none :=
  Std.ExtDHashMap.get?_eq_ite_of_unit

@[simp]
theorem get?_empty {i} : (∅ : Map α β).get? i = none :=
  Std.ExtDHashMap.get?_empty

theorem ofList_eq_ofList_iff {xs ys : List (α × β)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  induction xs using List.ind_pair_sigma
  induction ys using List.ind_pair_sigma
  simp [ofList]
  rw [List.map_map] at hx hy
  rw [Std.ExtDHashMap.ofList_eq_ofList_iff hx hy]
  rw [List.map_perm_map_iff # by simp]

def range [ha : Fintype α] (f : α → β) : Map α β :=
  ⟨Std.ExtDHashMap.range f⟩
  
@[simp]
theorem mem_range [ha : Fintype α] {f : α → β} {i : α} : i ∈ range f :=
  Std.ExtDHashMap.mem_range

@[simp]
theorem nonempty_insert {x} : Insert.insert x mp ≠ ∅ := by
  simp [ext_iff', ←equiv_def]
  rcases mp with ⟨mp⟩
  rw [insert_def]
  simp
  have h₁ := @Std.ExtDHashMap.nonempty_insert α (λ _ => β) _ _
    mp x.toSigma
  simp at h₁
  rwa [Std.ExtDHashMap.inner_eq_iff_eq]

@[simp]
theorem nodup_toList [LinearOrder α] : mp.toList.Nodup := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList Std.ExtDHashMap.lift
  rw [Quotient.lift_eq]
  rw [List.nodup_map_iff # by simp]
  simp

@[simp]
theorem sorted_toList [LinearOrder α] : mp.toList.Sorted (·.1 ≤ ·.1) := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList Std.ExtDHashMap.lift
  apply mp.ind; simp

@[simp]
theorem mem_toList [LinearOrder α] {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList
  apply mp.ind
  clear mp; intro mp
  unfold toSortedList get? Std.ExtDHashMap.get?
  rcases x with ⟨x, y⟩
  unfold Std.ExtDHashMap.lift
  simp

@[simp]
theorem toList_eq_toList [LinearOrder α] {m₁ m₂ : Map α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨⟨m₁⟩⟩; rcases m₂ with ⟨⟨m₂⟩⟩
  simp [toList, Quotient.lift_eq, ←equiv_def]

@[simp]
theorem toList_eq_nil_iff [LinearOrder α] : mp.toList = [] ↔ mp = ∅ := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList
  apply mp.ind; clear mp; intro mp
  simp [empty_def]
  unfold Std.ExtDHashMap.lift
  simp
  change _ ↔ _ = Std.ExtDHashMap.mk' _
  simp
  change _ ↔ _ ~m _
  simp

@[simp]
def toDMap (mp : Map α β) : DMap α (λ _ => β) :=
  ⟨mp.inner⟩

end Map namespace DMap

@[simp]
def toMap (mp : DMap α (λ _ => β)) : Map α β :=
  ⟨mp.inner⟩

end DMap namespace Map

instance [hh : DecidableEq β] : DecidableEq (Map α β) :=
  λ m₁ m₂ => match h : decide # m₁.inner = m₂.inner with
  | true => isTrue # by
    rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
    simp at h; simpa
  | false => isFalse # by
    rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
    simp at h; simpa

def values [LinearOrder α] (mp : Map α β) : List β :=
  mp.toList.map (·.2)

def all (mp : Map α β) (p : α → β → Bool) : Bool :=
  mp.1.all p

@[simp]
theorem all_def [LinearOrder α] {p} : mp.all p = decide (∀ x ∈ mp.toList, p x.1 x.2) := by
  simp [all]; rfl

def modify (mp : Map α β) (i : α) (f : β → β) : Map α β :=
  ⟨mp.1.modify i f⟩

def modifyMany (mp : Map α β) (xs : List (α × (β → β))) : Map α β :=
  ⟨mp.1.modifyMany # xs.map (·.toSigma)⟩

@[simp]
theorem modifyMany_nil : mp.modifyMany [] = mp := by
  simp [modifyMany]

@[simp]
theorem modifyMany_cons {i x xs} :
mp.modifyMany ((i, x) :: xs) = (mp.modify i x).modifyMany xs := by
  simp [modifyMany, modify]

def insertMany (mp : Map α β) (xs : List (α × β)) : Map α β :=
  ⟨mp.1.insertMany # xs.map (·.toSigma)⟩

@[simp]
theorem insertMany_nil : mp.insertMany [] = mp := by
  simp [insertMany]

@[simp]
theorem insertMany_cons {i x xs} :
mp.insertMany ((i, x) :: xs) = (mp.insert i x).insertMany xs := by
  simp [insertMany, Std.ExtDHashMap.insertMany_cons, Std.ExtDHashMap.insert]

theorem get?_eq_ite [hb : Inhabited β] {i} :
mp.get? i = if i ∈ mp then some # mp.get! i else none :=
  mp.1.get?_eq_ite

@[simp]
theorem mem_modify {i j x} : i ∈ mp.modify j x ↔ i ∈ mp :=
  Std.ExtDHashMap.mem_modify

theorem get!_eq_get?_get! [Inhabited β] {i} : mp.get! i = (mp.get? i).get! :=
  Std.ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_modify {i} {f : β → β} {j} :
(mp.modify i f).get? j = if j = i then
(mp.get? j).map f else mp.get? j := by
  split_ifs with h₁; subst h₁; simp [modify, get?]
  simp [modify, get?, Std.ExtDHashMap.get?_modify, ne_symm' h₁]

@[simp]
theorem mem_values [LinearOrder α] {x} : x ∈ mp.values ↔ ∃ i, mp.get? i = some x := by
  simp [values]

instance [ha : Fintype α] [hb : Fintype β] : Fintype (Map α β) :=
  haveI h : Fintype # Std.ExtDHashMap α (λ _ => β) := inferInstance
  ⟨h.1.map ⟨.mk, λ _ _ => by simp⟩, by simp⟩

instance [ha : Finite α] [hb : Finite β] : Finite (Map α β) := by
  apply Fintype.finite
  replace ha := @Fintype.ofFinite _ ha
  replace hb := @Fintype.ofFinite _ hb
  infer_instance

@[simp]
theorem range_eq_range_iff [ha : Fintype α] {f g : α → β} :
range f = range g ↔ ∀ x, f x = g x := by simp [range]

theorem mem_of_get?_eq_some {i x} (h : mp.get? i = some x) : i ∈ mp := by
  simp [mem_iff_get?_eq_some, h]

theorem get!_eq_get!_get? {i} [hb : Inhabited β] :
mp.get! i = (mp.get? i).get! := Std.ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_eq_some_get!_iff {i} [hb : Inhabited β] :
mp.get? i = some (mp.get! i) ↔ i ∈ mp := by
  simp [get?_eq_ite]

@[simp]
theorem get?_eq_some_get?_get! {i} [hb : Inhabited β] :
mp.get? i = some (mp.get? i).get! ↔ i ∈ mp := by
  simp [←get!_eq_get!_get?]

def fold {γ : Type*} (mp : Map α β) (f : γ → α → β → γ) (z : γ)
(h_assoc : ∀ {acc i x j y}, f (f acc i x) j y = f (f acc j y) i x) : γ :=
  mp.inner.fold f z h_assoc

theorem fold_eq_foldl_toList [ha : LinearOrder α] {γ : Type*}
{z : γ} {f : γ → α → β → γ} {h_assoc} : mp.fold f z h_assoc =
mp.toList.foldl (λ acc (x : α × β) => f acc x.1 x.2) z := by
  convert Std.ExtDHashMap.fold_eq_foldl_toList; rotate_left; infer_instance
  simp [toList, Std.ExtDHashMap.toList, Std.ExtDHashMap.lift]
  rcases mp with ⟨⟨mp⟩⟩
  simp
  apply mp.ind
  simp [List.foldl_map]

theorem eq_iff_inner_eq {m₁ m₂ : Map α β} : m₁ = m₂ ↔ m₁.inner = m₂.inner := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

theorem eq_iff_toList_eq [ha : LinearOrder α] {m₁ m₂ : Map α β} :
m₁ = m₂ ↔ m₁.toList = m₂.toList := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

@[simp]
theorem ofList_toList [ha : LinearOrder α] : ofList mp.toList = mp := by
  rw [eq_iff_inner_eq]
  rw [←Std.ExtDHashMap.ofList_toList (mp := mp.inner)]
  unfold ofList
  dsimp
  rcases mp with ⟨⟨mp⟩⟩
  simp [toList, Std.ExtDHashMap.lift]
  apply mp.ind
  intro m
  simp
  rw [Std.ExtDHashMap.eq_iff_inner_eq]
  simp
  apply Quotient.eq_iff_equiv.mpr
  apply Std.DHashMap.equiv_iff_toList_perm.mpr
  trans m.toSortedList
  rotate_left; simp
  apply Std.DHashMap.toList_ofList_perm
  simp

theorem toList_ofList_perm [ha : LinearOrder α] {xs : List (α × β)}
(h : xs.map (·.1) |>.Nodup) : (ofList xs).toList.Perm xs := by
  generalize hy : xs.map Prod.toSigma = ys
  have hx : ys.map Sigma.toProd = xs; simp [←hy]
  subst hx; clear hy; rename' ys => xs
  simp at h
  trans (DMap.ofList xs).toList.map Sigma.toProd
  rotate_left
  · rw [List.map_perm_map_iff # by simp]
    exact DMap.toList_ofList_perm h
  simp [ofList]; rfl

def keys [ha : LinearOrder α] (mp : Map α β) : List α :=
  mp.inner.keys

@[simp]
theorem sorted_keys [ha : LinearOrder α] : mp.keys.Sorted (· ≤ ·) :=
  Std.ExtDHashMap.sorted_keys

theorem keys_eq_map_toList [ha : LinearOrder α] : mp.keys = mp.toList.map (·.1) := by
  rcases mp with ⟨mp⟩; simp [keys, toList, Std.ExtDHashMap.lift]; symm
  refine' Quotient.apply_lift (f := List.map # λ (x : α × β) => x.1) _ |>.trans _
  intro m₁ m₂ h₁; simp; exact Std.DHashMap.toSortedKeys_eq_of_equiv h₁; simp; rfl

def minKey? [ha : LinearOrder α] (mp : Map α β) : Option α :=
  mp.inner.minKey?

def maxKey? [ha : LinearOrder α] (mp : Map α β) : Option α :=
  mp.inner.maxKey?

def minKey! [Inhabited α] [ha : LinearOrder α] (mp : Map α β) : α :=
  mp.minKey?.get!

def maxKey! [Inhabited α] [ha : LinearOrder α] (mp : Map α β) : α :=
  mp.maxKey?.get!

theorem minKey?_eq_head?_keys [ha : LinearOrder α] : mp.minKey? = mp.keys.head? :=
  Std.ExtDHashMap.minKey?_eq_head?_keys

theorem maxKey?_eq_getLast?_keys [ha : LinearOrder α] : mp.maxKey? = mp.keys.getLast? :=
  Std.ExtDHashMap.maxKey?_eq_getLast?_keys

@[simp]
theorem minKey?_eq_none_iff [ha : LinearOrder α] : mp.minKey? = none ↔ mp = ∅ := by
  rw [eq_iff_inner_eq]; exact Std.ExtDHashMap.minKey?_eq_none_iff

@[simp]
theorem maxKey?_eq_none_iff [ha : LinearOrder α] : mp.maxKey? = none ↔ mp = ∅ := by
  rw [eq_iff_inner_eq]; exact Std.ExtDHashMap.maxKey?_eq_none_iff

theorem not_mem_of_lt_minKey? [ha : LinearOrder α] {m x}
(h₁ : mp.minKey? = some m) (h₂ : x < m) : x ∉ mp :=
  Std.ExtDHashMap.not_mem_of_lt_minKey? h₁ h₂

theorem not_mem_of_maxKey?_lt [ha : LinearOrder α] {m x}
(h₁ : mp.maxKey? = some m) (h₂ : m < x) : x ∉ mp :=
  Std.ExtDHashMap.not_mem_of_maxKey?_lt h₁ h₂

theorem not_mem_of_lt_minKey! [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x < mp.minKey!) : x ∉ mp := Std.ExtDHashMap.not_mem_of_lt_minKey! h

theorem not_mem_of_maxKey!_lt [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : mp.maxKey! < x) : x ∉ mp := Std.ExtDHashMap.not_mem_of_maxKey!_lt h