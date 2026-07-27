import Projects.Util.Data.DMap

universe u v w

structure Map (α : Type u) (β : Type v)
[hh₁ : DecidableEq α] [hh₂ : Hashable α] : Type (max u v) where
  inner : Std.ExtDHashMap α (λ _ => β)
deriving Inhabited

variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp m m₁ m₂ m₃ : Map α β}
variable [ha : LinearOrder α]
omit ha

open Std

namespace Map

def empty : Map α β := ⟨∅⟩

instance : EmptyCollection (Map α β) := ⟨empty⟩

theorem empty_def : (∅ : Map α β) = ⟨∅⟩ := rfl

def insertP (x : α × β) (mp : Map α β) : Map α β :=
  ⟨insert x.toSigma mp.inner⟩

instance : Insert (α × β) (Map α β) := ⟨insertP⟩

theorem insert_def {x : α × β} {mp : Map α β} :
insert x mp = ⟨insert x.toSigma mp.inner⟩ := rfl

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
  ExtDHashMap.mem_iff_get?_eq_some

theorem get?_eq_some_of_mem {i : α} (h : i ∈ mp) : ∃ x, mp.get? i = some x :=
  ExtDHashMap.get?_eq_some_of_mem h

theorem get?_eq_none_of_not_mem {i : α} (h : i ∉ mp) : mp.get? i = none :=
  ExtDHashMap.get?_eq_none_of_not_mem h

@[simp]
theorem get?_eq_none_iff {i} : mp.get? i = none ↔ i ∉ mp :=
  ExtDHashMap.get?_eq_none_iff

theorem get?_map {f : α → β → γ} {i : α} :
(mp.map f).get? i = (mp.get? i).map (f i) :=
  ExtDHashMap.get?_map

theorem get!_map_eq_of_pos {f : α → β → γ} {i : α}
[ha : Inhabited β] [hb : Inhabited γ]
(h : i ∈ mp) : (mp.map f).get! i = f i (mp.get! i) := by
  rcases mp with ⟨⟨mp⟩⟩
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  induction mp using Quotient.inductionOn
  simp [get?] at hx
  simp [get!, ExtDHashMap.get!_eq_get?, map, hx]

def toList (mp : Map α β) : List (α × β) :=
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
  change List.map _ _ = _; simp [DHashMap.toSortedList]

@[simp]
theorem mem_insertP {x : α × β} {i} :
i ∈ mp.insertP x ↔ i = x.1 ∨ i ∈ mp :=
  ExtDHashMap.mem_insert'

@[simp]
theorem mem_insert' {i x j} : j ∈ mp.insert i x ↔ j = i ∨ j ∈ mp := by
  simp [mem_def, Map.insert]

@[simp]
theorem mem_insert {x i} : i ∈ Insert.insert x mp ↔ i = x.1 ∨ i ∈ mp :=
  mem_insert'

@[simp]
theorem mem_ofList {xs : List (α × β)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  induction xs using List.ind_pair_sigma; simp [ofList]
  exact ExtDHashMap.mem_ofList'

@[simp]
theorem mem_map {f : α → β → γ} {i} :
i ∈ mp.map f ↔ i ∈ mp := by
  simp [mem_def, map]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  rcases mp with ⟨mp⟩; simp [empty_def]
  exact ExtDHashMap.eq_empty_iff

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : Map α β).mem i :=
  ExtDHashMap.not_mem_empty

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : Map α β) :=
  not_mem_empty'

theorem ext_iff' {m₁ m₂ : Map α β} :
m₁ = m₂ ↔ m₁.inner.1.out.Equiv m₂.inner.1.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact ExtDHashMap.ext_iff'

theorem ext' {m₁ m₂ : Map α β}
(h : m₁.inner.1.out.Equiv m₂.inner.1.out) : m₁ = m₂ := by
  rwa [ext_iff']

theorem ext_iff {m₁ m₂ : Map α β} : m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact ExtDHashMap.ext_iff

@[ext]
theorem ext {m₁ m₂ : Map α β} (h : ∀ i, m₁.get? i = m₂.get? i) : m₁ = m₂ := by
  rwa [ext_iff]

theorem get?_eq_ite_of_unit {m : Map α Unit} {i} :
m.get? i = if i ∈ m then some () else none :=
  ExtDHashMap.get?_eq_ite_of_unit

@[simp]
theorem get?_empty {i} : (∅ : Map α β).get? i = none :=
  ExtDHashMap.get?_empty

theorem ofList_eq_ofList_iff {xs ys : List (α × β)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  induction xs using List.ind_pair_sigma
  induction ys using List.ind_pair_sigma
  simp [ofList]
  rw [List.map_map] at hx hy
  rw [ExtDHashMap.ofList_eq_ofList_iff hx hy]
  rw [List.map_perm_map_iff # by simp]

def range [ha : Fintype α] (f : α → β) : Map α β :=
  ⟨ExtDHashMap.range f⟩
  
@[simp]
theorem mem_range [ha : Fintype α] {f : α → β} {i : α} : i ∈ range f :=
  ExtDHashMap.mem_range

@[simp]
theorem nonempty_insert {x} : Insert.insert x mp ≠ ∅ := by
  simp [ext_iff', ←DHashMap.equiv_def]
  rcases mp with ⟨mp⟩
  rw [insert_def]
  simp
  have h₁ := @ExtDHashMap.nonempty_insert α (λ _ => β) _ _
    mp x.toSigma
  simp at h₁
  rw [Quotient.out_equiv_out]
  rwa [ExtDHashMap.inner_eq_iff_eq]

@[simp]
theorem nodup_toList [LinearOrder α] : mp.toList.Nodup := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList ExtDHashMap.lift
  rw [Quotient.lift_eq]
  rw [List.nodup_map_iff # by simp]
  simp

@[simp]
theorem pairwise_toList [LinearOrder α] : mp.toList.Pairwise (·.1 ≤ ·.1) := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList ExtDHashMap.lift
  apply mp.ind; simp

@[simp]
theorem mem_toList [LinearOrder α] {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList
  apply mp.ind
  clear mp; intro mp
  unfold DHashMap.toSortedList get? ExtDHashMap.get?
  rcases x with ⟨x, y⟩
  unfold ExtDHashMap.lift
  simp

@[simp]
theorem toList_eq_toList [LinearOrder α] {m₁ m₂ : Map α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨⟨m₁⟩⟩; rcases m₂ with ⟨⟨m₂⟩⟩
  simp [ExtDHashMap.lift, toList, Quotient.lift_eq, ←DHashMap.equiv_def]
  rw [Quotient.out_equiv_out]

@[simp]
theorem toList_eq_nil_iff [LinearOrder α] : mp.toList = [] ↔ mp = ∅ := by
  rcases mp with ⟨⟨mp⟩⟩; unfold toList
  apply mp.ind; clear mp; intro mp
  simp [empty_def]
  unfold ExtDHashMap.lift
  simp
  change _ ↔ _ = ExtDHashMap.mk' _
  simp
  change _ ↔ DHashMap.Equiv _ _
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

def values (mp : Map α β) : List β :=
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
  simp [insertMany, ExtDHashMap.insertMany_cons, ExtDHashMap.insert, Map.insert]

theorem get?_eq_ite [hb : Inhabited β] {i} :
mp.get? i = if i ∈ mp then some # mp.get! i else none :=
  mp.1.get?_eq_ite

@[simp]
theorem mem_modify {i j x} : i ∈ mp.modify j x ↔ i ∈ mp :=
  ExtDHashMap.mem_modify

theorem get!_eq_get?_get! [Inhabited β] {i} : mp.get! i = (mp.get? i).get! :=
  ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_modify {i} {f : β → β} {j} :
(mp.modify i f).get? j = if j = i then
(mp.get? j).map f else mp.get? j := by
  split_ifs with h₁; subst h₁; simp [modify, get?]
  simp [modify, get?, ExtDHashMap.get?_modify, ne_symm' h₁]

@[simp]
theorem mem_values [LinearOrder α] {x} : x ∈ mp.values ↔ ∃ i, mp.get? i = some x := by
  simp [values]

instance [ha : Fintype α] [hb : Fintype β] : Fintype (Map α β) :=
  haveI h : Fintype # ExtDHashMap α (λ _ => β) := inferInstance
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
mp.get! i = (mp.get? i).get! := ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_eq_some_get!_iff {i} [hb : Inhabited β] :
mp.get? i = some (mp.get! i) ↔ i ∈ mp := by
  simp [get?_eq_ite]

@[simp]
theorem get?_eq_some_get?_get! {i} [hb : Inhabited β] :
mp.get? i = some (mp.get? i).get! ↔ i ∈ mp := by
  simp [←get!_eq_get!_get?]

def fold {γ : Type*} (mp : Map α β) (f : γ → α → β → γ) (z : γ)
(h_assoc : ∀ {acc i x j y}, i ≠ j → f (f acc i x) j y = f (f acc j y) i x) : γ :=
  mp.inner.fold f z h_assoc

theorem fold_eq_foldl_toList [ha : LinearOrder α] {γ : Type*}
{z : γ} {f : γ → α → β → γ} {h_assoc} : mp.fold f z h_assoc =
mp.toList.foldl (λ acc (x : α × β) => f acc x.1 x.2) z := by
  convert! ExtDHashMap.fold_eq_foldl_toList; rotate_left; infer_instance
  simp [toList, ExtDHashMap.toList, ExtDHashMap.lift]
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
  rw [←ExtDHashMap.ofList_toList (mp := mp.inner)]
  unfold ofList
  dsimp
  rcases mp with ⟨⟨mp⟩⟩
  simp [toList, ExtDHashMap.lift]
  apply mp.ind
  intro m
  simp
  rw [ExtDHashMap.eq_iff_inner_eq]
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

def keys (mp : Map α β) : List α :=
  mp.inner.keys

@[simp]
theorem sortedLE_keys [ha : LinearOrder α] : mp.keys.SortedLE :=
  ExtDHashMap.sortedLE_keys

@[simp]
theorem sortedLT_keys [ha : LinearOrder α] : mp.keys.SortedLT :=
  ExtDHashMap.sortedLT_keys

theorem keys_eq_map_fst_toList [ha : LinearOrder α] : mp.keys = mp.toList.map (·.1) := by
  rcases mp with ⟨mp⟩; simp [keys, toList, ExtDHashMap.lift]; symm
  refine' Quotient.apply_lift (f := List.map # λ (x : α × β) => x.1) _ |>.trans _
  intro m₁ m₂ h₁; simp; exact Std.DHashMap.toSortedKeys_eq_of_equiv h₁; simp; rfl

def minKey? (mp : Map α β) : Option α :=
  mp.inner.minKey?

def maxKey? (mp : Map α β) : Option α :=
  mp.inner.maxKey?

def minKey! [Inhabited α] (mp : Map α β) : α :=
  mp.minKey?.get!

def maxKey! [Inhabited α] (mp : Map α β) : α :=
  mp.maxKey?.get!

theorem minKey?_eq_head?_keys [ha : LinearOrder α] : mp.minKey? = mp.keys.head? :=
  ExtDHashMap.minKey?_eq_head?_keys

theorem maxKey?_eq_getLast?_keys [ha : LinearOrder α] : mp.maxKey? = mp.keys.getLast? :=
  ExtDHashMap.maxKey?_eq_getLast?_keys

@[simp]
theorem minKey?_eq_none_iff [ha : LinearOrder α] : mp.minKey? = none ↔ mp = ∅ := by
  rw [eq_iff_inner_eq]; exact ExtDHashMap.minKey?_eq_none_iff

@[simp]
theorem maxKey?_eq_none_iff [ha : LinearOrder α] : mp.maxKey? = none ↔ mp = ∅ := by
  rw [eq_iff_inner_eq]; exact ExtDHashMap.maxKey?_eq_none_iff

theorem not_mem_of_lt_minKey? [ha : LinearOrder α] {m x}
(h₁ : mp.minKey? = some m) (h₂ : x < m) : x ∉ mp :=
  ExtDHashMap.not_mem_of_lt_minKey? h₁ h₂

theorem not_mem_of_maxKey?_lt [ha : LinearOrder α] {m x}
(h₁ : mp.maxKey? = some m) (h₂ : m < x) : x ∉ mp :=
  ExtDHashMap.not_mem_of_maxKey?_lt h₁ h₂

theorem not_mem_of_lt_minKey! [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x < mp.minKey!) : x ∉ mp := ExtDHashMap.not_mem_of_lt_minKey! h

theorem not_mem_of_maxKey!_lt [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : mp.maxKey! < x) : x ∉ mp := ExtDHashMap.not_mem_of_maxKey!_lt h

theorem minKey?_le_of_mem [ha : LinearOrder α] {m x}
(h₁ : mp.minKey? = some m) (h₂ : x ∈ mp) : m ≤ x := by
  contrapose! h₂; exact not_mem_of_lt_minKey? h₁ h₂

theorem le_maxKey?_of_mem [ha : LinearOrder α] {m x}
(h₁ : mp.maxKey? = some m) (h₂ : x ∈ mp) : x ≤ m := by
  contrapose! h₂; exact not_mem_of_maxKey?_lt h₁ h₂

theorem minKey!_le_of_mem [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x ∈ mp) : mp.minKey! ≤ x := by
  contrapose! h; exact not_mem_of_lt_minKey! h

theorem le_maxKey!_of_mem [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x ∈ mp) : x ≤ mp.maxKey! := by
  contrapose! h; exact not_mem_of_maxKey!_lt h

theorem ind {p : Map α β → Prop} (h₁ : p ∅)
(h₂ : ∀ (m : Map α β) i x, p m → i ∉ m → p (m.insert i x)) m : p m := by
  rcases m with ⟨mp⟩; induction mp using ExtDHashMap.ind
  exact h₁; apply h₂ <;> assumption

@[simp]
theorem fold_empty {γ : Type*} {f : γ → (i : α) → β → γ} {z : γ} {h} :
(∅ : Map α β).fold f z h = z := ExtDHashMap.fold_empty

theorem fold_insert {γ : Type*} {f : γ → α → β → γ} {z : γ} {h i x}
(h₁ : i ∉ mp) : (mp.insert i x).fold f z h = mp.fold f (f z i x) h :=
  ExtDHashMap.fold_insert # by simpa

theorem insert_comm {i x j y} (h : i ≠ j ∨ x = y) :
(mp.insert i x).insert j y = (mp.insert j y).insert i x := by
  simp [Map.insert]; apply ExtDHashMap.insert_comm; simpa

@[simp]
theorem insert_idemp {i x} : (mp.insert i x).insert i x = mp.insert i x := by
  simp [Map.insert]

def size (mp : Map α β) : ℕ :=
  mp.1.size

def filter (mp : Map α β) (p : α → β → Bool) : Map α β :=
  ⟨mp.1.filter p⟩

def count (mp : Map α β) (p : α → β → Bool) : ℕ :=
  mp.1.count p

@[simp]
theorem size_filter_eq_count {p} : (mp.filter p).size = mp.count p :=
  mp.1.size_filter_eq_count

theorem count_eq_size_filter {p} : mp.count p = (mp.filter p).size :=
  size_filter_eq_count.symm

@[simp]
theorem count_le_size {p} : mp.count p ≤ mp.size :=
  mp.1.count_le_size

theorem count_eq_zero_iff {p} :
mp.count p = 0 ↔ ∀ i x, mp.get? i = some x → ¬p i x :=
  mp.1.count_eq_zero_iff

@[simp]
theorem count_empty {p} : (∅ : Map α β).count p = 0 :=
  ExtDHashMap.count_empty

theorem count_insert {p i x} (h : i ∉ mp) :
(mp.insert i x).count p = mp.count p + if p i x then 1 else 0 :=
  mp.1.count_insert h

def push (mp : Map α ℕ) (i : α) : Map α ℕ :=
  mp.insert i # (mp.get? i).getD 0 + 1

theorem get?_insert {i j x} :
(mp.insert j x).get? i = if j = i then some x else mp.get? i := by
  convert! mp.1.get?_insert; simp; rfl

theorem push_push_comm {i j} {mp : Map α ℕ} :
(mp.push i).push j = (mp.push j).push i := by
  ext; simp [push, get?_insert]; aesop

@[simp]
theorem mem_push {mp : Map α ℕ} {x y : α} : y ∈ mp.push x ↔ y = x ∨ y ∈ mp := by
  simp [push]

@[simp]
theorem length_toList [ha : LinearOrder α] : mp.toList.length = mp.size := by
  rcases mp with ⟨m⟩
  simp [toList, size, ExtDHashMap.lift, ExtDHashMap.size]
  induction m; simp

theorem mem_iff_mem_keys [ha : LinearOrder α] {k} : k ∈ mp ↔ k ∈ mp.keys := by
  simp [keys_eq_map_fst_toList, mem_iff_get?_eq_some]

@[simp]
theorem modifyMany_snoc {xs i f} :
mp.modifyMany (xs ++ [(i, f)]) = (mp.modifyMany xs).modify i f := by
  induction xs generalizing mp; simp
  nm x xs ih; rcases x with ⟨j, g⟩; simp [ih]

@[simp]
theorem modify_empty {i f} : (∅ : Map α β).modify i f = ∅ := by
  simp [empty_def, modify]

@[simp]
theorem mem_mk_iff {mp i} : i ∈ (⟨mp⟩ : Map α β) ↔ i ∈ mp := by
  rfl

theorem modify_of_notMem {i f} (h : i ∉ mp) : mp.modify i f = mp := by
  rcases mp with ⟨mp⟩
  rw [modify]
  simp at h ⊢
  exact ExtDHashMap.modify_of_notMem h

theorem modify_insert_of_ne {i x j f} (h : i ≠ j) :
(mp.insert i x).modify j f = (mp.modify j f).insert i x := by
  ext; simp [get?_insert]; grind

include ha in @[simp]
theorem toList_mk {mp} : (⟨mp⟩ : Map α β).toList = mp.toList.map Sigma.toProd := by
  rcases mp with ⟨mp⟩; induction mp using Quotient.inductionOn; nm mp; rfl

include ha in
theorem toList_insert_perm_cons_of_notMem {i x} (h : i ∉ mp) :
(mp.insert i x).toList.Perm (⟨i, x⟩ :: mp.toList) := by
  rcases mp with ⟨mp⟩
  simp at h
  have h₁ := ExtDHashMap.toList_insert_perm_cons_of_notMem h (x := x)
  simp [Map.insert]
  change List.Perm _ # Sigma.toProd ⟨i, x⟩ :: _
  rwa [←List.map_cons, List.map_perm_map_iff]; simp

include ha in
theorem values_insert_perm_of_notMem {i x} (h : i ∉ mp) :
(mp.insert i x).values.Perm (x :: mp.values) := by
  simp_rw [values]; have := toList_insert_perm_cons_of_notMem h (x := x); grind

@[simp]
theorem modify_insert_of_eq {i x f} : (mp.insert i x).modify i f = mp.insert i (f x) := by
  ext; simp [get?_insert]; grind

include ha in
theorem countP_values_modify_eq_of
{p : β → Bool} {i : α} {f : β → β} (h : ∀ x, p (f x) = p x) :
(mp.modify i f).values.countP p = mp.values.countP p := by
  by_cases h₁ : i ∉ mp; rw [modify_of_notMem h₁]
  push Not at h₁
  induction mp using ind; simp
  clear! mp
  nm mp j x ih hk
  simp at h₁
  rcases h₁ with rfl | h₁
  · clear ih
    simp
    apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans; symm
    apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans
    simp [List.countP_cons]
    rw [h]
  have h₂ : i ≠ j; grind
  specialize ih h₁
  rw [modify_insert_of_ne # ne_symm' h₂]
  have h₃ : j ∉ mp.modify i f; simpa
  apply List.Perm.countP_eq p (values_insert_perm_of_notMem h₃) |>.trans; symm
  apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans
  simp [List.countP_cons, ih]

include ha in
theorem countP_values_modifyMany_eq_of
{p : β → Bool} {xs : List (α × (β → β))}
(h : ∀ k f x, (k, f) ∈ xs → p (f x) = p x) :
(mp.modifyMany xs).values.countP p = mp.values.countP p := by
  induction xs using List.reverseRecOn; simp
  nm xs x ih
  rcases x with ⟨k, f⟩
  simp
  rw [←ih # by grind]
  clear ih
  rw [countP_values_modify_eq_of]
  specialize h k f
  grind

theorem size_insert {i x} (h : i ∉ mp) : (mp.insert i x).size = mp.size + 1 := by
  rcases mp with ⟨mp⟩; simp [Map.insert, size] at h ⊢; simp [ExtDHashMap.size_insert, h]

@[simp]
theorem size_modify {i f} : (mp.modify i f).size = mp.size := by
  cases mp; simp [modify, size]

include ha in
theorem get?_eq_some_iff {i x} : mp.get? i = some x ↔ (i, x) ∈ mp.toList := by
  simp

include ha in @[simp]
theorem nodup_keys : mp.keys.Nodup := by
  simp [keys]

include ha in @[simp]
theorem mem_keys_iff_mem {k} : k ∈ mp.keys ↔ k ∈ mp := by
  simp [←mem_iff_mem_keys]

include ha in @[simp]
theorem length_keys : mp.keys.length = mp.size := by
  simp [keys_eq_map_fst_toList]

include ha in @[simp]
theorem keys_modify {i f} : (mp.modify i f).keys = mp.keys := by
  apply List.eq_of_perm_of_pairwise (r := (· ≤ ·)) <;> try simp [←List.sortedLE_iff_pairwise]
  apply List.perm_of_nodup_and_subset_and_length_eq <;> try simp
  intro; simp

def erase (mp : Map α β) (i : α): Map α β :=
  ⟨mp.1.erase i⟩

@[simp]
theorem mem_erase {i j} : j ∈ mp.erase i ↔ j ≠ i ∧ j ∈ mp := by
  rcases mp with ⟨mp⟩; simp [erase]; grind

include ha in @[simp]
theorem pairwise_toList' : mp.toList.Pairwise (·.1 < ·.1) := by
  suffices h : mp.toList.map (·.1) |>.SortedLT
  · simp [List.sortedLT_iff_pairwise] at h; exact h
  rw [←keys_eq_map_fst_toList]; simp

include ha in
theorem values_eq_map_snd_toList : mp.values = mp.toList.map (·.2) := rfl

def keyIdx (mp : Map α β) (i : α) : ℕ :=
  mp.keys.idxOf i

include ha in
theorem keyIdx_lt_size {i} (h : i ∈ mp) : mp.keyIdx i < mp.size := by
  rw [keyIdx, ←length_keys]; apply List.idxOf_lt_length_of_mem; simpa

include ha in
theorem toList_modify_eq_list_modify {i f} (h : i ∈ mp) :
(mp.modify i f).toList = mp.toList.modify (mp.keyIdx i) (λ p => (p.1, f p.2)) := by
  rename' h => h₁
  have h₂ : i ∈ mp.modify i f; simpa
  rw [mem_iff_mem_keys, keys_eq_map_fst_toList, List.mem_map] at h₁ h₂
  obtain ⟨⟨i, y⟩, h₁, rfl⟩ := h₁
  obtain ⟨⟨j, z⟩, h₂, rfl⟩ := h₂
  dsimp at *
  rw [List.mem_iff_append] at h₁ h₂
  choose xs ys h₁ using h₁
  choose xs' ys' h₂ using h₂
  rw [h₁, h₂]
  have h₃ : (mp.modify j f).keys = mp.keys; simp
  have h₄' := mp.nodup_keys
  have h₅' := mp.modify j f |>.nodup_keys
  simp_rw [keys_eq_map_fst_toList] at h₃ h₄' h₅'
  simp [h₁, h₂] at h₃ h₄' h₅'
  have h₄ : j ∉ xs.map (·.1); grind
  have h₅ : j ∉ xs'.map (·.1); grind
  obtain ⟨h₆, h₇⟩ := List.eq_and_eq_of_append_cons_eq h₃ h₅ h₄
  have H : ∃ k, k = xs.length ∧ (xs' ++ (j, z) :: ys').map (·.1) =
    ((xs ++ (j, y) :: ys).modify k # λ p => (p.1, f p.2)).map (·.1)
  · simp [h₆, h₇]
  choose k hk' H using H
  have hk : k < mp.size
  · replace h₁ := congrArg (·.length) h₁
    simp at h₁
    omega
  rw [←h₁, ←h₂] at H ⊢
  have h : mp.keyIdx j = k
  · rw [keyIdx, keys_eq_map_fst_toList, h₁]; simp
    rw [List.idxOf_append]; simp [h₄, hk']
  rw [h]; clear h
  generalize H₁ : (mp.modify j f).toList = xs at H ⊢
  generalize H₂ : (mp.toList.modify k # λ p => (p.1, f p.2)) = ys at H ⊢
  have G₁ : ∀ i x, (i, x) ∈ ys → (i, x) ∈ xs
  · rename' xs => xs₁, ys => ys₁
    subst hk'
    intro c x G₁
    simp [←H₂] at G₁
    simp [h₁] at G₁
    rw [←H₁, h₂]
    simp
    rcases G₁ with G₁ | ⟨G₁, G₂⟩ | G₁
    · left
      have hc : c ≠ j
      · simp at h₄
        grind
      have G₂ : mp.get? c = some x
      · rw [get?_eq_some_iff, h₁]
        simp [G₁]
      replace G₂ : (mp.modify j f).get? c = some x
      · simpa [hc]
      rw [get?_eq_some_iff, h₂] at G₂
      simp [hc] at G₂
      rcases G₂ with G₂ | G₂; exact G₂
      exfalso
      replace G₁ : c ∈ xs.map (·.1); grind
      replace G₂ : c ∈ ys'.map (·.1); grind
      grind
    · subst G₁ G₂
      right; left
      simp
      replace h₁ := congrArg ((c, y) ∈ ·) h₁
      replace h₂ := congrArg ((c, z) ∈ ·) h₂
      simp at h₁
      simp [h₁] at h₂
      exact h₂
    · right; right
      have hc : c ≠ j
      · simp at h₄; grind
      have G₂ : mp.get? c = some x
      · rw [get?_eq_some_iff, h₁]
        simp [G₁]
      replace G₂ : (mp.modify j f).get? c = some x
      · simpa [hc]
      rw [get?_eq_some_iff, h₂] at G₂
      simp [hc] at G₂; symm at G₂
      rcases G₂ with G₂ | G₂; exact G₂
      exfalso
      replace G₁ : c ∈ ys.map (·.1); grind
      replace G₂ : c ∈ xs'.map (·.1); grind
      grind
  have H₁' : (xs.map (·.1)).Nodup
  · simp [←H₁, ←keys_eq_map_fst_toList]
  replace H₁ : xs.Pairwise (·.1 ≤ ·.1)
  · simp [←H₁]
  have H₃ : ys.Pairwise (·.1 < ·.1)
  · rw [←H₂, ←List.pairwise_map]; simp [List.map_modify_eq_of]
  replace H₂ : ys.Pairwise (·.1 ≤ ·.1)
  · rw [←H₂, ←List.pairwise_map]; simp [List.map_modify_eq_of]
  replace H₃ : (ys.map (·.1)).Nodup
  · rw [←List.pairwise_map] at H₃
    exact H₃.nodup
  nm a b; clear! a b xs' ys' z j f k y
  apply List.eq_of_perm_of_pairwise (r := (·.1 ≤ ·.1)) _ H₁ H₂ <;> try simp
  · intro i x j y h₁ h₂ h₃ h₄
    apply and_of
    · exact _root_.le_antisymm h₃ h₄
    rintro rfl
    clear h₃ h₄
    by_contra h₃
    rw [List.mem_iff_getElem] at h₁ h₂
    choose k₁ hk₁ h₁ using h₁
    choose k₂ hk₂ h₂ using h₂
    have h₄ : k₁ ≠ k₂; grind
    replace h₁ : (xs.map (·.1))[k₁]'(by grind) = i; grind
    replace h₂ : (ys.map (·.1))[k₂]'(by grind) = i; grind
    apply h₄
    rw! [←H] at h₂
    rw! [←h₂] at h₁
    rwa [←H₁'.getElem_inj_iff]
  apply List.perm_of_nodup_and_subset_and_length_eq
  · exact List.Nodup.of_map _ H₃
  · rintro ⟨i, x⟩ h₁; grind
  · replace H := congrArg (·.length) H
    simp at H; exact H.symm

include ha in
theorem keyIdx_eq_of_toList_eq_append {i x xs ys}
(h : mp.toList = xs ++ (i, x) :: ys) : mp.keyIdx i = xs.length := by
  rw [keyIdx, keys_eq_map_fst_toList, h]
  simp
  rw [List.idxOf_append]
  simp
  intro y h₁
  exfalso
  replace h := congrArg (·.map (·.1) |>.Nodup) h
  simp [←keys_eq_map_fst_toList] at h
  grind

include ha in
theorem values_modify_eq_list_modify {i f} (h : i ∈ mp) :
(mp.modify i f).values = mp.values.modify (mp.keyIdx i) f := by
  simp_rw [values_eq_map_snd_toList, toList_modify_eq_list_modify h]
  rw [←mem_keys_iff_mem, keys_eq_map_fst_toList, List.mem_map] at h
  obtain ⟨⟨i, x⟩, h, rfl⟩ := h
  dsimp
  rw [List.mem_iff_append] at h
  choose xs ys h using h
  rw [h, keyIdx_eq_of_toList_eq_append h]
  simp
  rw [show xs.length = (xs.map (·.2)).length by simp]
  rw [List.modify_length_append]; simp

include ha in
theorem countP_values_modify_eq_ite_of_get? {p : β → Bool} {i x f}
(h : mp.get? i = some x) : (mp.modify i f).values.countP p = mp.values.countP p +
(if p # f x then 1 else 0) - (if p x then 1 else 0) := by
  rw [values_modify_eq_list_modify # mem_of_get?_eq_some h]
  simp_rw [values_eq_map_snd_toList]
  rw [get?_eq_some_iff] at h
  rw [List.mem_iff_append] at h
  choose xs ys h using h
  rw [h, keyIdx_eq_of_toList_eq_append h]
  simp
  rw [show xs.length = (xs.map (·.2)).length by simp]
  rw [List.modify_length_append]; simp
  grind

def union (m₁ m₂ : Map α β) : Map α β :=
  ⟨m₁.inner.union m₂.inner⟩

instance : Union (Map α β) := ⟨union⟩
theorem union_def : m₁ ∪ m₂ = m₁.union m₂ := rfl

@[simp]
theorem inner_empty : (∅ : Map α β).inner = ∅ := rfl

@[simp]
theorem inner_union : (m₁ ∪ m₂).inner = m₁.inner ∪ m₂.inner := rfl

@[simp]
theorem empty_union : ∅ ∪ mp = mp := by
  simp [eq_iff_inner_eq]

@[simp]
theorem union_empty : mp ∪ ∅ = mp := by
  simp [eq_iff_inner_eq]

@[simp]
theorem insertP_pair {i x} : mp.insertP ⟨i, x⟩ = mp.insert i x := rfl

@[simp]
theorem get?_mk {mp : Std.ExtDHashMap α (λ _ => β)} {i} :
(Map.mk mp).get? i = mp.get? i := rfl

@[simp]
theorem mk_union_mk {mp₁ mp₂ : Std.ExtDHashMap α (λ _ => β)} :
Map.mk mp₁ ∪ Map.mk mp₂ = Map.mk (mp₁ ∪ mp₂) := rfl

theorem get?_union {i} : (m₁ ∪ m₂).get? i = (m₂.get? i).or (m₁.get? i) := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp [ExtDHashMap.get?_union]

@[simp]
theorem inner_ofList {xs : List (α × β)} :
(ofList xs).inner = .ofList (xs.map Prod.toSigma) := rfl

@[simp]
theorem ofList_singleton {x : α × β} : ofList [x] = (∅ : Map α β).insertP x := rfl

@[simp]
theorem insert_insert_same {i x y} : (mp.insert i x).insert i y = mp.insert i y := by
  ext; simp [get?_insert]; grind

theorem insert_union {i x} : (m₁ ∪ m₂).insert i x = m₁ ∪ m₂.insert i x := by
  ext; simp [get?_insert, get?_union]; split_ifs with h; grind; simp

theorem union_insert {i x} : m₁ ∪ m₂.insert i x = (m₁ ∪ m₂).insert i x :=
  insert_union.symm

@[simp]
theorem ofList_append {xs ys : List (α × β)} :
Map.ofList (xs ++ ys) = Map.ofList xs ∪ Map.ofList ys := by
  induction ys using List.reverseRecOn generalizing xs
  · simp
  nm ys x ih
  rcases x with ⟨j, x⟩
  rw [←List.append_assoc, ofList_snoc]
  simp [ih]; clear ih
  rw [union_insert]

theorem ofList_cons_of_mem {x : α × β} {xs y}
(h : (x.1, y) ∈ xs) : ofList (x :: xs) = ofList xs := by
  rcases x with ⟨i, x⟩
  dsimp at h
  rw [List.cons_eq_append, ofList_append]
  ext j z
  simp [get?_union]
  intro h₁ h₂
  replace h₂ := mem_of_get?_eq_some h₂
  simp at h₂
  grind

theorem get?_union_left {i} (h : i ∉ m₂) : (m₁ ∪ m₂).get? i = m₁.get? i := by
  simp [get?_union, get?_eq_none_of_not_mem h]

theorem get?_union_right {i} (h : i ∉ m₁) : (m₁ ∪ m₂).get? i = m₂.get? i := by
  simp [get?_union, get?_eq_none_of_not_mem h]

theorem get!_union_left [hb : Inhabited β] {i}
(h : i ∉ m₂) : (m₁ ∪ m₂).get! i = m₁.get! i := by
  simp [get!_eq_get!_get?, get?_union, get?_eq_none_of_not_mem h]

theorem get!_union_right [hb : Inhabited β] {i}
(h : i ∉ m₁) : (m₁ ∪ m₂).get! i = m₂.get! i := by
  simp [get!_eq_get!_get?, get?_union, get?_eq_none_of_not_mem h]

theorem get!_insert [hb : Inhabited β] {i x j} :
(mp.insert i x).get! j = if j = i then x else mp.get! j := by
  simp [get!_eq_get!_get?, get?_insert]; grind

theorem get?_ofList_eq_some_iff {xs : List (α × β)} {i x}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get? i = some x ↔ ⟨i, x⟩ ∈ xs := by
  simp [ofList]; rw [ExtDHashMap.get?_ofList_eq_some_iff (by simpa)]; simp

theorem get?_ofList_of_nodup {xs : List (α × β)} {i} (h : (xs.map (·.1)).Nodup) :
(ofList xs).get? i = (xs.find? (·.fst = i)).map (·.2) := by
  unfold Option.map; split
  · nm a x h₁; clear a
    rename' i => j
    rcases x with ⟨i, x⟩
    rw [get?_ofList_eq_some_iff h]
    grind
  nm a h₁; clear a
  simp at h₁ ⊢
  grind

theorem get!_ofList_of_nodup [hb : Inhabited β] {xs : List (α × β)} {i}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get! i =
((xs.find? (·.fst = i)).map (·.2)).get! := by
  rw [get!_eq_get!_get?, get?_ofList_of_nodup h]

@[simp]
theorem mem_union {i} : i ∈ m₁ ∪ m₂ ↔ i ∈ m₁ ∨ i ∈ m₂ := by
  simp [mem_iff_get?_eq_some, get?_union]; grind

include ha in @[simp]
theorem keys_mk {mp} : (⟨mp⟩ : Map α β).keys = mp.keys := rfl

@[simp]
theorem insert_mk {m i x} : (⟨m⟩ : Map α β).insert i x = ⟨m.insert i x⟩ := rfl

@[simp]
theorem erase_mk {m i} : (⟨m⟩ : Map α β).erase i = ⟨m.erase i⟩ := rfl

include ha in
theorem toList_insert_of_not_mem {i x} (h : i ∉ m) : (m.insert i x).toList =
(⟨i, x⟩ :: m.toList).mergeSort (·.1 ≤ ·.1) := by
  rcases m with ⟨m⟩; simp at h ⊢
  rw [ExtDHashMap.toList_insert_of_not_mem h]
  rw [List.map_mergeSort (s := (·.1 ≤ ·.1)) (by simp)]
  simp

include ha in
theorem keys_insert_of_not_mem {i x} (h : i ∉ m) :
(m.insert i x).keys = (i :: m.keys).mergeSort := by
  rcases m with ⟨m⟩; simp at h ⊢
  rw [ExtDHashMap.keys_insert_of_not_mem h]

@[simp]
theorem insert_erase_eq_self_iff {i x} :
(m.erase i).insert i x = m ↔ m.get? i = some x := by
  rcases m with ⟨m⟩; simp

include ha in @[simp]
theorem keys_eq_keys_iff {m₁ : Map α β} {m₂ : Map α γ} :
m₁.keys = m₂.keys ↔ ∀ i, i ∈ m₁ ↔ i ∈ m₂ := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

theorem union_assoc : (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) := by
  simp [ext_iff, get?_union]; grind

@[simp]
theorem union_self : m ∪ m = m := by
  simp [ext_iff, get?_union]

@[simp]
theorem union_union_self : m₁ ∪ (m₁ ∪ m₂) = m₁ ∪ m₂ := by
  simp [←union_assoc]

def diff (m₁ m₂ : Map α β) : Map α β :=
  ⟨m₁.1 \ m₂.1⟩

instance : SDiff (Map α β) := ⟨diff⟩
theorem diff_def : m₁ \ m₂ = m₁.diff m₂ := rfl

@[simp]
theorem mk_diff_mk {m₁ m₂} : (⟨m₁⟩ : Map α β) \ ⟨m₂⟩ = ⟨m₁ \ m₂⟩ := rfl

theorem get?_diff {i} : (m₁ \ m₂).get? i = if i ∈ m₂ then none else m₁.get? i := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp [ExtDHashMap.get?_diff]

@[simp]
theorem union_diff_self : m₁ ∪ (m₂ \ m₁) = m₂ ∪ m₁ := by
  simp [ext_iff, get?_union, get?_diff]
  intro i
  rw! (castMode := .all) [mem_iff_get?_eq_some]
  split_ifs with h; grind
  simp at h
  rw [←Option.eq_none_iff_forall_ne_some] at h
  grind

theorem union_eq_self_left_iff : m₁ ∪ m₂ = m₁ ↔
∀ i x, m₂.get? i = some x → m₁.get? i = some x := by
  simp [ext_iff, get?_union, Option.or]; grind

@[simp]
theorem union_insert_empty {i x} : m₁ ∪ (∅ : Map α β).insert i x = m₁.insert i x := by
  simp [ext_iff, get?_union, get?_insert]; grind

theorem toList_ofList [ha : LinearOrder α] {xs : List (α × β)}
(h : xs.map (·.1) |>.Nodup) : (ofList xs).toList = xs.mergeSort (·.1 ≤ ·.1) := by
  simp [ofList]
  have h₁ : xs.map Prod.toSigma |>.map (·.1) |>.Nodup
  · rw [List.nodup_map_iff_inj_on]
    rotate_left
    · rw [List.nodup_iff_getElem_ne_getElem] at h ⊢
      intro i j h₁ h₂ h₃
      specialize h i j (by grind) (by grind) h₃
      simp at h ⊢
      grind
    rintro ⟨i, x⟩ h₁ ⟨j, y⟩ h₂
    simp at h₁ h₂ ⊢
    rintro rfl; use rfl
    rw [List.nodup_iff_getElem_ne_getElem] at h
    simp at h
    rw [List.mem_iff_getElem] at h₁ h₂
    choose k h₁ h₃ using h₁
    choose n h₂ h₄ using h₂
    by_contra h₅
    have h₆ : k ≠ n; grind
    wlog h₇ : k < n with ih; grind
    specialize h _ _ h₁ h₂ h₇
    grind
  have h₂ := ExtDHashMap.toList_ofList h₁
  rw [h₂]; clear h₁ h₂
  rw [List.map_mergeSort (s := (·.1 ≤ ·.1))] <;> simp

theorem union_eq_union_iff_right (h₁ : ∀ i, i ∈ m → i ∉ m₁)
(h₂ : ∀ i, i ∈ m → i ∉ m₂) : m ∪ m₁ = m ∪ m₂ ↔ m₁ = m₂ := by
  simp [ext_iff, get?_union, Option.or]
  simp [mem_iff_get?_eq_some] at h₁ h₂; grind

theorem get?_union_ite {i} :
(m₁ ∪ m₂).get? i = if i ∈ m₂ then m₂.get? i else m₁.get? i := by
  rw! (castMode := .all) [mem_iff_get?_eq_some]
  simp [get?_union, Option.or]; split_ifs <;> grind

@[simp]
theorem mem_diff {i} : i ∈ m₁ \ m₂ ↔ i ∈ m₁ ∧ i ∉ m₂ := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp