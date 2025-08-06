import AP.Util.Data.Map

universe u v w

structure Set' (α : Type u)
[hh₁ : DecidableEq α] [hh₂ : Hashable α] : Type u where
  inner : Std.ExtDHashMap α (λ _ => Unit)

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

instance : Inhabited (Map α β) := ⟨∅⟩

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