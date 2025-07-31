import AP.Util.Data.DMap

universe u v w

structure Map (α : Type u) (β : Type v)
[hh₁ : LinearOrder α] [hh₂ : Hashable α] : Type (max u v) where
  inner : Std.ExtDHashMap α (λ _ => β)

variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : LinearOrder α] [hh₂ : Hashable α]
variable {mp : Map α β}

namespace Map

open Std.DHashMap

def empty : Map α β := ⟨⟦∅⟧⟩

instance : EmptyCollection (Map α β) := ⟨empty⟩

theorem empty_def : (∅ : Map α β) = ⟨⟦∅⟧⟩ := rfl

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
  (mp.get? i).get!

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
  rcases mp with ⟨mp⟩
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  simp [get!, get?_map, hx]

def toList (mp : Map α β) : List (α × β) :=
  mp.inner.lift (λ m => m.toSortedList.map Sigma.toProd) #
    by simp [equiv_def]

@[simp]
theorem ofList_nil : ofList (α := α) (β := β) [] = ∅ := rfl

@[simp]
theorem ofList_snoc {xs} {x : α × β} :
ofList (xs ++ [x]) = (ofList xs).insertP x := by
  unfold insertP ofList; simp

@[simp]
theorem toList_empty : (∅ : Map α β).toList = [] := by
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
m₁ = m₂ ↔ m₁.inner.out ~m m₂.inner.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  exact Std.ExtDHashMap.ext_iff'

theorem ext' {m₁ m₂ : Map α β}
(h : m₁.inner.out ~m m₂.inner.out) : m₁ = m₂ := by
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
  exact Std.ExtDHashMap.nonempty_insert

@[simp]
theorem nodup_toList : mp.toList.Nodup := by
  rcases mp with ⟨mp⟩
  rw [toList, Quotient.lift_eq]
  rw [List.nodup_map_iff # by simp]
  simp

@[simp]
theorem sorted_toList : mp.toList.Sorted (·.1 ≤ ·.1) := by
  rcases mp with ⟨mp⟩
  apply mp.ind; simp [toList]

@[simp]
theorem mem_toList {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  rcases mp with ⟨mp⟩
  apply mp.ind
  clear mp; intro mp
  unfold toList toSortedList get? Std.ExtDHashMap.get?
  rcases x with ⟨x, y⟩
  simp

@[simp]
theorem toList_eq_toList {m₁ m₂ : Map α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
  simp [toList, Quotient.lift_eq, ←equiv_def]

@[simp]
theorem toList_eq_nil_iff : mp.toList = [] ↔ mp = ∅ := by
  rcases mp with ⟨mp⟩
  apply mp.ind; clear mp; intro mp
  simp [empty_def, toList]
  rw [Quotient.mk_eq_mk]
  change _ ↔ _ ~m _
  simp [toSortedList]

@[simp]
def toDMap (mp : Map α β) : DMap α (λ _ => β) :=
  ⟨mp.inner⟩

end Map namespace DMap

@[simp]
def toMap (mp : DMap α (λ _ => β)) : Map α β :=
  ⟨mp.inner⟩

end DMap namespace Map