import Projects.Util.Basic

universe u v w

structure DMap (α : Type u) (β : α → Type v)
[hh₁ : DecidableEq α] [hh₂ : Hashable α] : Type (max u v) where
  inner : Std.ExtDHashMap α β
deriving Inhabited

namespace DMap

open Std.DHashMap

variable {α : Type u} {β : α → Type v} {γ : α → Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : DMap α β}
variable [ha : LinearOrder α]
omit ha

def empty : DMap α β := ⟨∅⟩

instance : EmptyCollection (DMap α β) := ⟨empty⟩

theorem empty_def : (∅ : DMap α β) = ⟨∅⟩ := rfl

def insertP (x : Σ i, β i) (mp : DMap α β) : DMap α β :=
  ⟨insert x mp.inner⟩

instance : Insert (Σ i, β i) (DMap α β) := ⟨insertP⟩

theorem insert_def {x : Σ i, β i} {mp : DMap α β} :
insert x mp = ⟨insert x mp.inner⟩ := rfl

@[simp]
protected def insert (mp : DMap α β) (i : α) (x : β i) : DMap α β :=
  ⟨mp.inner.insert i x⟩

def ofList (xs : List (Σ i, β i)) : DMap α β :=
  ⟨.ofList xs⟩

def get? (i : α) (mp : DMap α β) : Option (β i) :=
  mp.inner.get? i

def get! (i : α) [h : Inhabited (β i)] (mp : DMap α β) : β i :=
  mp.inner.get! i

def map (mp : DMap α β) (f : ∀ i, β i → γ i) : DMap α γ :=
  ⟨mp.inner.map f⟩

def mem (mp : DMap α β) (i : α) : Prop :=
  i ∈ mp.inner

instance : Membership α (DMap α β) := ⟨mem⟩

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

theorem get?_map {f : ∀ i, β i → γ i} {i : α} :
(mp.map f).get? i = (mp.get? i).map (f i) :=
  Std.ExtDHashMap.get?_map

theorem get!_map_eq_of_pos {f : ∀ i, β i → γ i} {i : α}
[ha : Inhabited (β i)] [hb : Inhabited (γ i)]
(h : i ∈ mp) : (mp.map f).get! i = f i (mp.get! i) := by
  rcases mp with ⟨⟨mp⟩⟩
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  induction mp using Quotient.inductionOn
  simp [get?] at hx
  simp [get!, Std.ExtDHashMap.get!_eq_get?, map, hx]

def toList (mp : DMap α β) : List (Σ i, β i) :=
  mp.inner.lift toSortedList # by simp

@[simp]
theorem ofList_nil : ofList (α := α) (β := β) [] = ∅ := rfl

@[simp]
theorem ofList_snoc {xs} {x : Σ i, β i} :
ofList (xs ++ [x]) = (ofList xs).insertP x := by
  unfold insertP ofList; simp

@[simp]
theorem toList_empty [LinearOrder α] : (∅ : DMap α β).toList = [] :=
  Std.ExtDHashMap.toList_empty

@[simp]
theorem mem_insertP {x : Σ i, β i} {i} :
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
theorem mem_ofList {xs : List (Σ i, β i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs :=
  Std.ExtDHashMap.mem_ofList'

@[simp]
theorem mem_map {f : ∀ i, β i → γ i} {i} :
i ∈ mp.map f ↔ i ∈ mp := by
  simp [mem_def, map]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  rcases mp with ⟨mp⟩; simp [empty_def]
  exact Std.ExtDHashMap.eq_empty_iff

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : DMap α β).mem i :=
  Std.ExtDHashMap.not_mem_empty

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : DMap α β) :=
  not_mem_empty'

theorem ext_iff' {m₁ m₂ : DMap α β} :
m₁ = m₂ ↔ m₁.inner.1.out ~m m₂.inner.1.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.ext_iff'

theorem ext' {m₁ m₂ : DMap α β}
(h : m₁.inner.1.out ~m m₂.inner.1.out) : m₁ = m₂ := by
  rwa [ext_iff']

theorem ext_iff {m₁ m₂ : DMap α β} : m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.ext_iff

@[ext]
theorem ext {m₁ m₂ : DMap α β} (h : ∀ i, m₁.get? i = m₂.get? i) : m₁ = m₂ := by
  rwa [ext_iff]

theorem get?_eq_ite_of_unit {m : DMap α (λ _ => Unit)} {i} :
m.get? i = if i ∈ m then some () else none :=
  Std.ExtDHashMap.get?_eq_ite_of_unit

@[simp]
theorem get?_empty {i} : (∅ : DMap α β).get? i = none :=
  Std.ExtDHashMap.get?_empty

theorem ofList_eq_ofList_iff {xs ys : List (Σ i, β i)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  unfold ofList; simp
  exact Std.ExtDHashMap.ofList_eq_ofList_iff hx hy

def range [ha : Fintype α] (f : (i : α) → β i) : DMap α β :=
  ⟨Std.ExtDHashMap.range f⟩
  
@[simp]
theorem mem_range [ha : Fintype α] {f : (i : α) → β i} {i : α} : i ∈ range f :=
  Std.ExtDHashMap.mem_range

@[simp]
theorem nonempty_insert {x} : Insert.insert x mp ≠ ∅ := by
  simp [ext_iff', ←equiv_def]
  rcases mp with ⟨mp⟩
  simp [insert_def]
  rw [Quotient.out_equiv_out]
  apply ne_of_congr Std.ExtDHashMap.mk'
  exact Std.ExtDHashMap.nonempty_insert

@[simp]
theorem nodup_toList [LinearOrder α] : mp.toList.Nodup :=
  Std.ExtDHashMap.nodup_toList

@[simp]
theorem pairwise_toList [LinearOrder α] : mp.toList.Pairwise (·.1 ≤ ·.1) :=
  Std.ExtDHashMap.pairwise_toList

@[simp]
theorem mem_toList [LinearOrder α] {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 :=
  Std.ExtDHashMap.mem_toList

@[simp]
theorem toList_eq_toList [LinearOrder α] {m₁ m₂ : DMap α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.toList_eq_toList

@[simp]
theorem toList_eq_nil_iff [LinearOrder α] : mp.toList = [] ↔ mp = ∅ := by
  rcases mp with ⟨mp⟩; simp [empty_def]
  exact Std.ExtDHashMap.toList_eq_nil_iff

instance [hh : ∀ i, DecidableEq # β i] : DecidableEq (DMap α β) :=
  λ m₁ m₂ => match h : decide # m₁.inner = m₂.inner with
  | true => isTrue # by
    rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
    simp at h; simpa
  | false => isFalse # by
    rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
    simp at h; simpa

def all (mp : DMap α β) (p : (i : α) → β i → Bool) : Bool :=
  mp.1.all p

@[simp]
theorem all_def {p} [LinearOrder α] : mp.all p = decide (∀ x ∈ mp.toList, p x.1 x.2) := by
  simp [all]; rfl

def modify (mp : DMap α β) (i : α) (f : β i → β i) : DMap α β :=
  ⟨mp.1.modify i f⟩

def modifyMany (mp : DMap α β) (xs : List ((i : α) × (β i → β i))) : DMap α β :=
  ⟨mp.1.modifyMany xs⟩

@[simp]
theorem modifyMany_nil : mp.modifyMany [] = mp := by
  simp [modifyMany]

@[simp]
theorem modifyMany_cons {i x xs} :
mp.modifyMany (⟨i, x⟩ :: xs) = (mp.modify i x).modifyMany xs := by
  simp [modifyMany, modify]

def insertMany (mp : DMap α β) (xs : List ((i : α) × β i)) : DMap α β :=
  ⟨mp.1.insertMany xs⟩

@[simp]
theorem insertMany_nil : mp.insertMany [] = mp := by
  simp [insertMany]

@[simp]
theorem insertMany_cons {i x xs} :
mp.insertMany (⟨i, x⟩ :: xs) = (mp.insert i x).insertMany xs := by
  simp [insertMany, Std.ExtDHashMap.insertMany_cons, Std.ExtDHashMap.insert]

theorem get?_eq_ite {i} [hb : Inhabited # β i] :
mp.get? i = if i ∈ mp then some # mp.get! i else none :=
  mp.1.get?_eq_ite

@[simp]
theorem mem_modify {i j x} : i ∈ mp.modify j x ↔ i ∈ mp :=
  Std.ExtDHashMap.mem_modify

theorem get!_eq_get?_get! {i} [Inhabited (β i)] : mp.get! i = (mp.get? i).get! :=
  Std.ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_modify {i} {f : β i → β i} {j} :
(mp.modify i f).get? j = if h : i = j then
h ▸ ((mp.get? j).map (λ x => f (h.symm ▸ x))) else mp.get? j := by
  convert! Std.ExtDHashMap.get?_modify <;> simp
  generalize_proofs h₁; subst h₁; simp [get?]

instance [ha : Fintype α] [hb : ∀ i, Fintype (β i)] : Fintype (DMap α β) :=
  haveI h : Fintype # Std.ExtDHashMap α β := inferInstance
  ⟨h.1.map ⟨.mk, λ _ _ => by simp⟩, by simp⟩

instance [ha : Finite α] [hb : ∀ i, Finite (β i)] : Finite (DMap α β) := by
  apply Fintype.finite
  replace ha := @Fintype.ofFinite _ ha
  replace hb := λ i => @Fintype.ofFinite _ # hb i
  infer_instance

@[simp]
theorem range_eq_range_iff [ha : Fintype α] {f g : (i : α) → β i} :
range f = range g ↔ ∀ x, f x = g x := by simp [range]

theorem mem_of_get?_eq_some {i x} (h : mp.get? i = some x) : i ∈ mp := by
  simp [mem_iff_get?_eq_some, h]

theorem get!_eq_get!_get? {i} [hb : Inhabited (β i)] :
mp.get! i = (mp.get? i).get! := Std.ExtDHashMap.get!_eq_get!_get?

@[simp]
theorem get?_eq_some_get!_iff {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get! i) ↔ i ∈ mp := by
  simp [get?_eq_ite]

@[simp]
theorem get?_eq_some_get?_get! {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get? i).get! ↔ i ∈ mp := by
  simp [←get!_eq_get!_get?]

def fold {γ : Type*} (mp : DMap α β) (f : γ → (i : α) → β i → γ) (z : γ)
(h_assoc : ∀ {acc i x j y}, f (f acc i x) j y = f (f acc j y) i x) : γ :=
  mp.inner.fold f z h_assoc

theorem fold_eq_foldl_toList [ha : LinearOrder α] {γ : Type*}
{z : γ} {f : γ → (i : α) → β i → γ} {h_assoc} : mp.fold f z h_assoc =
mp.toList.foldl (λ acc (x : (i : α) × β i) => f acc x.1 x.2) z :=
  Std.ExtDHashMap.fold_eq_foldl_toList

theorem eq_iff_inner_eq {m₁ m₂ : DMap α β} : m₁ = m₂ ↔ m₁.inner = m₂.inner := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

theorem eq_iff_toList_eq [ha : LinearOrder α] {m₁ m₂ : DMap α β} :
m₁ = m₂ ↔ m₁.toList = m₂.toList := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

@[simp]
theorem ofList_toList [ha : LinearOrder α] : ofList mp.toList = mp := by
  rw [eq_iff_inner_eq]; exact Std.ExtDHashMap.ofList_toList

theorem toList_ofList_perm [ha : LinearOrder α] {xs : List ((i : α) × β i)}
(h : xs.map (·.1) |>.Nodup) : (ofList xs).toList.Perm xs :=
  Std.ExtDHashMap.toList_ofList_perm h

def keys (mp : DMap α β) : List α :=
  mp.inner.keys

@[simp]
theorem sortedLE_keys [ha : LinearOrder α] : mp.keys.SortedLE :=
  Std.ExtDHashMap.sortedLE_keys

@[simp]
theorem sortedLT_keys [ha : LinearOrder α] : mp.keys.SortedLT :=
  Std.ExtDHashMap.sortedLT_keys

theorem keys_eq_map_fst_toList [ha : LinearOrder α] : mp.keys = mp.toList.map (·.1) :=
  Std.ExtDHashMap.keys_eq_map_fst_toList

def minKey? (mp : DMap α β) : Option α :=
  mp.inner.minKey?

def maxKey? (mp : DMap α β) : Option α :=
  mp.inner.maxKey?

def minKey! [Inhabited α] (mp : DMap α β) : α :=
  mp.minKey?.get!

def maxKey! [Inhabited α] (mp : DMap α β) : α :=
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

theorem ind {p : DMap α β → Prop} (h₁ : p ∅)
(h₂ : ∀ (m : DMap α β) i x, p m → i ∉ m → p (m.insert i x)) m : p m := by
  rcases m with ⟨mp⟩; induction mp using Std.ExtDHashMap.ind
  exact h₁; apply h₂ <;> assumption

@[simp]
theorem fold_empty {γ : Type*} {f : γ → (i : α) → β i → γ} {z : γ} {h} :
(∅ : DMap α β).fold f z h = z := Std.ExtDHashMap.fold_empty

theorem fold_insert {γ : Type*} {f : γ → (i : α) → β i → γ} {z : γ} {h i x}
(h₁ : i ∉ mp) : (mp.insert i x).fold f z h = mp.fold f (f z i x) h :=
  Std.ExtDHashMap.fold_insert # by simpa

theorem insert_comm {i x j y} (h : i ≠ j ∨ HEq x y) :
(mp.insert i x).insert j y = (mp.insert j y).insert i x := by
  simp [DMap.insert]; exact Std.ExtDHashMap.insert_comm h

@[simp]
theorem insert_idemp {i x} : (mp.insert i x).insert i x = mp.insert i x := by
  simp [DMap.insert]

def size (mp : DMap α β) : ℕ :=
  mp.1.size

def filter (mp : DMap α β) (p : (i : α) → β i → Bool) : DMap α β :=
  ⟨mp.1.filter p⟩

def count (mp : DMap α β) (p : (i : α) → β i → Bool) : ℕ :=
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
theorem count_empty {p} : (∅ : DMap α β).count p = 0 :=
  Std.ExtDHashMap.count_empty

theorem count_insert {p i x} (h : i ∉ mp) :
(mp.insert i x).count p = mp.count p + if p i x then 1 else 0 :=
  mp.1.count_insert h

theorem mem_iff_mem_keys [ha : LinearOrder α] {k} : k ∈ mp ↔ k ∈ mp.keys := by
  simp [keys_eq_map_fst_toList, mem_iff_get?_eq_some]