import AP.Util.Basic

universe u v w

structure DMap (α : Type u) (β : α → Type v)
[hh₁ : LinearOrder α] [hh₂ : Hashable α] : Type (max u v) where
  inner : Std.ExtDHashMap α β

namespace DMap

open Std.DHashMap

variable {α : Type u} {β : α → Type v} {γ : α → Type w}
variable [hh₁ : LinearOrder α] [hh₂ : Hashable α]
variable {mp : DMap α β}

def empty : DMap α β := ⟨∅⟩

instance : EmptyCollection (DMap α β) := ⟨empty⟩

theorem empty_def : (∅ : DMap α β) = ⟨∅⟩ := rfl

instance : Inhabited (DMap α β) := ⟨∅⟩

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
theorem toList_empty : (∅ : DMap α β).toList = [] :=
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
  apply ne_of_congr Std.ExtDHashMap.mk'
  exact Std.ExtDHashMap.nonempty_insert

@[simp]
theorem nodup_toList : mp.toList.Nodup :=
  Std.ExtDHashMap.nodup_toList

@[simp]
theorem sorted_toList : mp.toList.Sorted (·.1 ≤ ·.1) :=
  Std.ExtDHashMap.sorted_toList

@[simp]
theorem mem_toList {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 :=
  Std.ExtDHashMap.mem_toList

@[simp]
theorem toList_eq_toList {m₁ m₂ : DMap α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.toList_eq_toList

@[simp]
theorem toList_eq_nil_iff : mp.toList = [] ↔ mp = ∅ := by
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
theorem all_def {p} : mp.all p = decide (∀ x ∈ mp.toList, p x.1 x.2) := by
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
  convert Std.ExtDHashMap.get?_modify <;> simp
  generalize_proofs h₁; subst h₁; simp [get?]