import AP.Util.Data.Map

universe u v w

structure Set' (α : Type u)
[hh₁ : DecidableEq α] [hh₂ : Hashable α] : Type u where
  inner : Std.ExtDHashMap α (λ _ => Unit)
deriving Inhabited

variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s : Set' α}

namespace Set'

open Std.DHashMap

def empty : Set' α := ⟨∅⟩

instance : EmptyCollection (Set' α) := ⟨empty⟩

theorem empty_def : (∅ : Set' α) = ⟨∅⟩ := rfl

def insertP (x : α) (s : Set' α) : Set' α :=
  ⟨insert ⟨x, ()⟩ s.inner⟩

instance : Insert α (Set' α) := ⟨insertP⟩

theorem insert_def {x : α} {s : Set' α} :
insert x s = ⟨insert ⟨x, ()⟩ s.inner⟩ := rfl

@[simp]
protected def insert (s : Set' α) (i : α) : Set' α :=
  ⟨s.inner.insert i ()⟩

def ofList (xs : List α) : Set' α :=
  ⟨.ofList # xs.map (⟨·, ()⟩)⟩

def mem (s : Set' α) (i : α) : Prop :=
  i ∈ s.inner

instance : Membership α (Set' α) := ⟨mem⟩

theorem mem_def {i} : i ∈ s ↔ i ∈ s.inner := by rfl

instance {i} : Decidable (s.mem i) := by
  unfold mem; infer_instance

instance {i} : Decidable (i ∈ s) := by
  change Decidable # s.mem i; infer_instance

def toList [LinearOrder α] (s : Set' α) : List α :=
  s.inner.lift (·.toSortedKeys) # by
    intro s₁ s₂ h; dsimp; unfold toSortedKeys; congr 1; simpa

@[simp]
theorem ofList_nil : ofList (α := α) [] = ∅ := rfl

@[simp]
theorem ofList_snoc {xs} {x : α} :
ofList (xs ++ [x]) = (ofList xs).insertP x := by
  unfold insertP ofList; simp

@[simp]
theorem toList_empty [LinearOrder α] : (∅ : Set' α).toList = [] := by
  change List.map _ _ = _; simp [toSortedList]

@[simp]
theorem mem_insertP {x : α} {i} :
i ∈ s.insertP x ↔ i = x ∨ i ∈ s :=
  Std.ExtDHashMap.mem_insert'

@[simp]
theorem mem_insert' {i j} :
j ∈ s.insert i ↔ j = i ∨ j ∈ s := by
  simp [mem_def]; tauto

@[simp]
theorem mem_insert {x i} :
i ∈ Insert.insert x s ↔ i = x ∨ i ∈ s :=
  mem_insert'

@[simp]
theorem mem_ofList {xs : List α} {i} :
i ∈ ofList xs ↔ i ∈ xs := by
  simp [ofList, mem_def]

theorem eq_empty_iff : s = ∅ ↔ ∀ i, i ∉ s := by
  rcases s with ⟨mp⟩; simp [empty_def]
  exact Std.ExtDHashMap.eq_empty_iff

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : Set' α).mem i :=
  Std.ExtDHashMap.not_mem_empty

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : Set' α) :=
  not_mem_empty'

theorem ext_iff' {s₁ s₂ : Set' α} :
s₁ = s₂ ↔ s₁.inner.1.out ~m s₂.inner.1.out := by
  rcases s₁ with ⟨s₁⟩; rcases s₂ with ⟨s₂⟩; simp
  exact Std.ExtDHashMap.ext_iff'

theorem ext' {s₁ s₂ : Set' α}
(h : s₁.inner.1.out ~m s₂.inner.1.out) : s₁ = s₂ := by
  rwa [ext_iff']

theorem ext_iff {s₁ s₂ : Set' α} : s₁ = s₂ ↔ ∀ i, i ∈ s₁ ↔ i ∈ s₂ := by
  rcases s₁ with ⟨s₁⟩; rcases s₂ with ⟨s₂⟩
  simp [mem_def, Std.ExtDHashMap.ext_iff, Option.eq_iff_of_subsingleton]

@[ext]
theorem ext {s₁ s₂ : Set' α} (h : ∀ i, i ∈ s₁ ↔ i ∈ s₂) : s₁ = s₂ := by
  rwa [ext_iff]

theorem get?_eq_ite_of_unit {m : Map α Unit} {i} :
m.get? i = if i ∈ m then some () else none :=
  Std.ExtDHashMap.get?_eq_ite_of_unit

theorem ofList_eq_ofList_iff {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  simp [ofList]
  rw [Std.ExtDHashMap.ofList_eq_ofList_iff]
  any_goals simpa
  rw [List.map_perm_map_iff]
  intro x y h; simp at h; exact h

def univ [ha : Fintype α] : Set' α :=
  ⟨Std.ExtDHashMap.range # λ _ => ()⟩

@[simp]
theorem mem_univ [ha : Fintype α] {i : α} : i ∈ univ :=
  Std.ExtDHashMap.mem_range

@[simp]
theorem nonempty_insert {x} : Insert.insert x s ≠ ∅ := by
  simp [ext_iff', ←equiv_def]
  rcases s with ⟨s⟩
  rw [insert_def]
  simp
  have h₁ := @Std.ExtDHashMap.nonempty_insert α (λ _ => Unit) _ _
    s ⟨x, ()⟩
  simp at h₁
  rwa [Std.ExtDHashMap.inner_eq_iff_eq]

@[simp]
theorem nodup_toList [LinearOrder α] : s.toList.Nodup := by
  rcases s with ⟨⟨s⟩⟩; unfold toList Std.ExtDHashMap.lift
  rw [Quotient.lift_eq]
  simp

@[simp]
theorem sorted_toList [LinearOrder α] : s.toList.Sorted (· ≤ ·) := by
  rcases s with ⟨⟨s⟩⟩; unfold toList Std.ExtDHashMap.lift
  apply s.ind; simp

@[simp]
theorem mem_toList [LinearOrder α] {x} : x ∈ s.toList ↔ x ∈ s := by
  rcases s with ⟨⟨s⟩⟩; unfold toList
  apply s.ind; clear s; intro s
  unfold toSortedKeys Std.ExtDHashMap.lift
  change _ ↔ x ∈ s
  simp [Option.eq_iff_of_subsingleton]

@[simp]
theorem toList_eq_toList [LinearOrder α] {s₁ s₂ : Set' α} :
s₁.toList = s₂.toList ↔ s₁ = s₂ := by
  rcases s₁ with ⟨⟨s₁⟩⟩; rcases s₂ with ⟨⟨s₂⟩⟩
  simp [toList, Quotient.lift_eq]
  exact Quotient.out_equiv_out (x := s₁)

@[simp]
theorem toList_eq_nil_iff [LinearOrder α] : s.toList = [] ↔ s = ∅ := by
  rcases s with ⟨⟨s⟩⟩; unfold toList
  apply s.ind; clear s; intro s
  simp [empty_def]
  unfold Std.ExtDHashMap.lift
  simp
  change _ ↔ _ = Std.ExtDHashMap.mk' _
  simp
  change _ ↔ _ ~m _
  simp

@[simp]
def toDMap (s : Set' α) : DMap α (λ _ => Unit) :=
  ⟨s.inner⟩

@[simp]
def toMap (s : Set' α) : Map α Unit :=
  ⟨s.inner⟩

instance : DecidableEq (Set' α) :=
  λ s₁ s₂ => match h : decide # s₁.inner = s₂.inner with
  | true => isTrue # by
    rcases s₁ with ⟨s₁⟩; rcases s₂ with ⟨s₂⟩
    simp at h; simpa
  | false => isFalse # by
    rcases s₁ with ⟨s₁⟩; rcases s₂ with ⟨s₂⟩
    simp at h; simpa

instance : Inhabited (Set α) := ⟨∅⟩

def values [LinearOrder α] (s : Set' α) : List α :=
  s.1.keys

@[simp]
theorem mem_values [LinearOrder α] {i} : i ∈ s.values ↔ i ∈ s := by
  simp [values]; rfl

def all (s : Set' α) (p : α → Bool) : Bool :=
  s.1.all # λ i _ => p i

@[simp]
theorem all_def [LinearOrder α] {p} : s.all p = decide (∀ x ∈ s.values, p x) := by
  simp [all, values, Option.eq_iff_of_subsingleton]

instance [ha : Fintype α] : Fintype (Set' α) :=
  haveI h : Fintype # Std.ExtDHashMap α (λ _ => Unit) := inferInstance
  ⟨h.1.map ⟨.mk, λ _ _ => by simp⟩, by simp⟩

instance [ha : Finite α] : Finite (Set' α) := by
  apply Fintype.finite
  replace ha := @Fintype.ofFinite _ ha
  infer_instance

def fold (s : Set' α) (f : β → α → β) (z : β)
(h_assoc : ∀ {acc x y}, f (f acc x) y = f (f acc y) x) : β :=
  s.inner.fold (λ acc x _ => f acc x) z # by simpa

def fold₁ (s : Set' α) (f : α → α → α)
(h_comm : ∀ {x y}, f x y = f y x)
(h_assoc : ∀ {acc x y}, f (f acc x) y = f (f acc y) x) : Option α :=
  s.fold (λ acc x => some # acc.elim x (f · x)) none # by
    rintro (⟨⟩ | acc) x y <;> simp
    exact h_comm; exact h_assoc

omit hb₁ hb₂ in
theorem fold_eq_foldl_toList [ha : LinearOrder α]
{z : β} {f : β → α → β} {h_assoc} : s.fold f z h_assoc = s.toList.foldl f z := by
  convert Std.ExtDHashMap.fold_eq_foldl_toList; rotate_left; infer_instance
  simp [toList, Std.ExtDHashMap.toList, Std.ExtDHashMap.lift]
  rcases s with ⟨⟨mp⟩⟩
  simp
  apply mp.ind
  intro m
  simp [toSortedKeys, List.foldl_map]

theorem eq_iff_inner_eq {s₁ s₂ : Set' α} : s₁ = s₂ ↔ s₁.inner = s₂.inner := by
  rcases s₁, s₂ with ⟨⟨s₁⟩, ⟨s₂⟩⟩; simp

theorem eq_iff_toList_eq [ha : LinearOrder α] {s₁ s₂ : Set' α} :
s₁ = s₂ ↔ s₁.toList = s₂.toList := by
  rcases s₁, s₂ with ⟨⟨s₁⟩, ⟨s₂⟩⟩; simp

@[simp]
theorem ofList_toList [ha : LinearOrder α] : ofList s.toList = s := by
  rcases s with ⟨⟨mp⟩⟩
  simp [ofList, toList, Std.ExtDHashMap.lift, Std.ExtDHashMap.ofList]
  apply mp.ind; intro m; simp
  apply Quotient.eq_iff_equiv.mp
  simp [toSortedKeys]
  exact ofList_toSortedList_equiv

theorem toList_ofList_perm [ha : LinearOrder α] {xs : List α}
(h : xs.Nodup) : (ofList xs).toList.Perm xs := by
  generalize hy : xs.map (λ x => (⟨x, ()⟩ : (i : α) × Unit)) = ys
  have hx : ys.map (·.1) = xs; simp [←hy]
  subst hx; clear hy; rename' ys => xs
  trans (DMap.ofList xs).toList.map (·.1)
  rotate_left
  · rw [List.map_perm_map_iff]
    exact DMap.toList_ofList_perm h
    rintro ⟨x, _⟩ ⟨y, _⟩ h; simp at h; simp [h]
  simp [ofList]; rfl

theorem ind_ofList [ha : LinearOrder α] {p : Set' α → Prop}
(h : ∀ (xs : List α), xs.Nodup → xs.Sorted (· ≤ ·) → p (ofList xs))
(s : Set' α) : p s := by
  rw [←ofList_toList (s := s)]; apply h <;> simp

def min? [ha : LinearOrder α] (s : Set' α) : Option α :=
  s.inner.minKey?

def max? [ha : LinearOrder α] (s : Set' α) : Option α :=
  s.inner.maxKey?

def min! [Inhabited α] [ha : LinearOrder α] (s : Set' α) : α :=
  s.min?.get!

def max! [Inhabited α] [ha : LinearOrder α] (s : Set' α) : α :=
  s.max?.get!

theorem min?_eq_head?_toList [ha : LinearOrder α] : s.min? = s.toList.head? :=
  Std.ExtDHashMap.minKey?_eq_head?_keys

theorem maxKey?_eq_getLast?_toList [ha : LinearOrder α] : s.max? = s.toList.getLast? :=
  Std.ExtDHashMap.maxKey?_eq_getLast?_keys

@[simp]
theorem min?_eq_none_iff [ha : LinearOrder α] : s.min? = none ↔ s = ∅ := by
  rw [eq_iff_inner_eq]; exact Std.ExtDHashMap.minKey?_eq_none_iff

@[simp]
theorem max?_eq_none_iff [ha : LinearOrder α] : s.max? = none ↔ s = ∅ := by
  rw [eq_iff_inner_eq]; exact Std.ExtDHashMap.maxKey?_eq_none_iff

theorem not_mem_of_lt_min? [ha : LinearOrder α] {m x}
(h₁ : s.min? = some m) (h₂ : x < m) : x ∉ s :=
  Std.ExtDHashMap.not_mem_of_lt_minKey? h₁ h₂

theorem not_mem_of_max?_lt [ha : LinearOrder α] {m x}
(h₁ : s.max? = some m) (h₂ : m < x) : x ∉ s :=
  Std.ExtDHashMap.not_mem_of_maxKey?_lt h₁ h₂

theorem not_mem_of_lt_min! [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x < s.min!) : x ∉ s := Std.ExtDHashMap.not_mem_of_lt_minKey! h

theorem not_mem_of_max!_lt [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : s.max! < x) : x ∉ s := Std.ExtDHashMap.not_mem_of_maxKey!_lt h