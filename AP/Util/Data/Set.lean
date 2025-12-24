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
variable {s s' s₁ s₂ s₃ : Set' α}
variable [ha : LinearOrder α]
omit ha

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
theorem mem_insert {i j} :
j ∈ s.insert i ↔ j = i ∨ j ∈ s := by
  simp [Set'.insert, mem_def]; tauto

@[simp]
theorem mem_insert' {x i} :
i ∈ Insert.insert x s ↔ i = x ∨ i ∈ s :=
  mem_insert

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
theorem sorted_toList' [LinearOrder α] : s.toList.Sorted (· ≤ ·) := by
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
  simp [Std.ExtDHashMap.lift, toList, Quotient.lift_eq]
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

theorem forall_mem_iff_all {p : α → Prop} [hp : DecidablePred p] :
(∀ x ∈ s, p x) ↔ s.all p := by
  rcases s with ⟨⟨mp⟩⟩
  simp [all, Std.ExtDHashMap.all, mem_def]
  induction mp using Quotient.ind
  simp [Std.ExtDHashMap.mem_iff_get?_eq_some]; rfl

instance {p : α → Prop} [hp : DecidablePred p] : Decidable # ∀ x ∈ s, p x :=
  match h : s.all p with
  | true => .isTrue # by simpa [forall_mem_iff_all]
  | false => .isFalse # by simpa [forall_mem_iff_all]

@[simp]
theorem all_iff {p} [DecidablePred p] : s.all p = decide (∀ x ∈ s, p x) := by
  simp [forall_mem_iff_all]

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

theorem ind_ofList' [ha : LinearOrder α] {p : Set' α → Prop}
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

theorem min?_le_of_mem [ha : LinearOrder α] {m x}
(h₁ : s.min? = some m) (h₂ : x ∈ s) : m ≤ x := by
  contrapose! h₂; exact not_mem_of_lt_min? h₁ h₂

theorem le_max?_of_mem [ha : LinearOrder α] {m x}
(h₁ : s.max? = some m) (h₂ : x ∈ s) : x ≤ m := by
  contrapose! h₂; exact not_mem_of_max?_lt h₁ h₂

theorem min!_le_of_mem [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x ∈ s) : s.min! ≤ x := by
  contrapose! h; exact not_mem_of_lt_min! h

theorem le_max!_of_mem [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x ∈ s) : x ≤ s.max! := by
  contrapose! h; exact not_mem_of_max!_lt h

def subset (s s' : Set' α) : Prop :=
  ∀ x ∈ s, x ∈ s'

instance : HasSubset (Set' α) := ⟨subset⟩

theorem subset_def : s ⊆ s' ↔ ∀ x ∈ s, x ∈ s' := by rfl

def subset_comp (s s' : Set' α) : Bool :=
  s.all (· ∈ s')

theorem subset_iff_subset_comp : s ⊆ s' ↔ s.subset_comp s' := by
  simp [subset_def, subset_comp]

instance : Decidable (s ⊆ s') :=
  match h : s.subset_comp s' with
  | true => .isTrue # by simpa [subset_iff_subset_comp]
  | false => .isFalse # by simpa [subset_iff_subset_comp]

@[simp]
theorem subset_comp_eq : s.subset_comp s' = decide (s ⊆ s') := by
  simp [subset_iff_subset_comp]

@[refl, simp]
theorem subset_refl : s ⊆ s := λ _ h => h

@[trans]
theorem subset_trans (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₃) : s₁ ⊆ s₃ := by
  intro x hx; apply h₂; apply h₁; exact hx

theorem insert_comm {x y : α} : (s.insert x).insert y = (s.insert y).insert x := by
  ext z; simp; tauto

theorem ind {p : Set' α → Prop} (h₁ : p ∅)
(h₂ : ∀ (s : Set' α) x, x ∉ s → p s → p (s.insert x)) (s : Set' α) : p s := by
  rcases s with ⟨mp⟩; induction mp using Std.ExtDHashMap.ind
  exact h₁; apply h₂ <;> assumption

def union (s₁ s₂ : Set' α) : Set' α :=
  s₂.fold (λ s x => s.insert x) s₁ # by simp [insert_comm]

instance : Union (Set' α) := ⟨union⟩

theorem union_def : s₁ ∪ s₂ = s₁.union s₂ := rfl

omit hb₁ hb₂ in @[simp]
theorem fold_empty {f : β → α → β} {z : β} {h} : (∅ : Set' α).fold f z h = z :=
  Std.ExtDHashMap.fold_empty

omit hb₁ hb₂ in
theorem fold_insert {f : β → α → β} {z : β} {h x}
(h₁ : x ∉ s) : (s.insert x).fold f z h = s.fold f (f z x) h :=
  Std.ExtDHashMap.fold_insert # by simpa

@[simp]
theorem mem_union {x : α} : x ∈ s₁ ∪ s₂ ↔ x ∈ s₁ ∨ x ∈ s₂ := by
  simp [union_def, union]
  induction s₂ using ind generalizing s₁
  · simp
  nm s₂ y h₁ ih
  generalize_proofs h₂
  unfold fold Set'.insert
  rw [Std.ExtDHashMap.fold_insert h₁]
  rw [←Set'.insert, ←fold]; rotate_left; exact h₂
  simp
  apply ih.trans
  rw [←Set'.insert]
  simp
  tauto

def ofFinset (s : Finset α) : Set' α :=
  s.1.liftWith ofList # by
    intro xs ys (h₁ : s.1.out.Perm xs) (h₂ : s.1.out.Perm ys)
    rw [ofList_eq_ofList_iff]
    · exact h₁.symm.trans h₂
    · simp [←h₁.nodup_iff]
    · simp [←h₂.nodup_iff]

@[simp]
theorem mem_ofFinset {s : Finset α} {x} : x ∈ ofFinset s ↔ x ∈ s := by
  simp [ofFinset]

open Classical in noncomputable
def ofSet (s : Set α) : Set' α :=
  if h : s.Finite then haveI := h.fintype; ofFinset s.toFinset else ∅

theorem mem_ofSet {s : Set α} {x} (h : s.Finite) : x ∈ ofSet s ↔ x ∈ s := by
  simp [ofSet, h]

instance : Coe (List α) (Set' α) := ⟨ofList⟩
instance : Coe (Finset α) (Set' α) := ⟨ofFinset⟩
noncomputable instance : Coe (Set α) (Set' α) := ⟨ofSet⟩

def filter (s : Set' α) (p : α → Bool) : Set' α :=
  .mk # s.1.filter # λ x _ => p x

@[simp]
theorem mem_filter {p x} : x ∈ s.filter p ↔ x ∈ s ∧ p x := by
  simp [filter, mem_def, Std.ExtDHashMap.mem_filter]

def diff (s₁ s₂ : Set' α) : Set' α :=
  s₁.filter (· ∉ s₂)

instance : SDiff (Set' α) := ⟨diff⟩

theorem diff_def : s₁ \ s₂ = s₁.diff s₂ := rfl

@[simp]
theorem mem_diff {x} : x ∈ s₁ \ s₂ ↔ x ∈ s₁ ∧ x ∉ s₂ := by
  simp [diff_def, diff]

def inter (s₁ s₂ : Set' α) : Set' α :=
  s₁.filter (· ∈ s₂)

instance : Inter (Set' α) := ⟨inter⟩

theorem inter_def : s₁ ∩ s₂ = s₁.inter s₂ := rfl

@[simp]
theorem mem_inter {x} : x ∈ s₁ ∩ s₂ ↔ x ∈ s₁ ∧ x ∈ s₂ := by
  simp [inter_def, inter]

@[simp]
theorem inter_left_subset_self : s₁ ∩ s₂ ⊆ s₁ := by
  intro x; simp; tauto

@[simp]
theorem inter_right_subset_self : s₂ ∩ s₁ ⊆ s₁ := by
  intro x; simp

theorem inter_subset_inter_of_left (h : s₁ ⊆ s₂) : s₁ ∩ s₃ ⊆ s₂ ∩ s₃ := by
  intro x; specialize h x; simp; tauto

theorem inter_subset_inter_of_right (h : s₁ ⊆ s₂) : s₃ ∩ s₁ ⊆ s₃ ∩ s₂ := by
  intro x; specialize h x; simp; tauto

theorem insert_eq_of_mem {x} (h : x ∈ s) : s.insert x = s := by
  ext y; simp; rintro rfl; exact h

@[simp]
theorem insert_idemp {x} : (s.insert x).insert x = s.insert x := by
  simp [Set'.insert]

def map (s : Set' α) (f : α → β) : Set' β :=
  s.fold (z := ∅) (λ s' x => s'.insert # f x) insert_comm

@[simp]
theorem map_empty {f : α → β} : (∅ : Set' α).map f = ∅ := by
  simp [map]

@[simp]
theorem map_insert {f : α → β} {x : α} : (s.insert x).map f = (s.map f).insert (f x) := by
  unfold map
  suffices h : ∀ z h, (s.insert x).fold (λ s' x ↦ s'.insert (f x)) z h =
    (s.fold (λ (s' : Set' β) x ↦ s'.insert (f x)) z h).insert (f x); apply h
  intro z hh
  dsimp at hh
  induction s using Set'.ind generalizing z
  · rw [fold_insert # by simp]; simp
  clear! s; nm s y h ih
  by_cases h₁ : x ∈ s.insert y
  · simp at h₁
    rcases h₁ with rfl | h₁
    · simp [ih]
    rw [insert_comm]
    rw [insert_eq_of_mem h₁] at ih ⊢
    rw [fold_insert h]
    apply ih
  rw [fold_insert h₁]
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  simp_rw [fold_insert h₂] at ih
  by_cases h₃ : y ∈ s
  · rw [insert_eq_of_mem h₃, ih]
  simp [fold_insert h₃]
  rw [insert_comm, ih]

@[simp]
theorem mem_map {f : α → β} {y : β} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  induction s using Set'.ind; simp; aesop

theorem eq_empty_iff_not_mem : s = ∅ ↔ ∀ x, x ∉ s := by
  constructor; rintro rfl; simp; intro h; ext i; simp [h]

@[simp]
theorem map_eq_empty_iff {f : α → β} : s.map f = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_not_mem, mem_map, not_exists, not_and,
    forall_apply_eq_imp_iff₂, imp_false]

@[simp]
theorem empty_eq_map_iff {f : α → β} : ∅ = s.map f ↔ s = ∅ := by
  rw [eq_comm]; exact map_eq_empty_iff

@[simp]
theorem map_map {f : α → β} {g : β → γ} : (s.map f).map g = s.map (g # f ·) := by
  ext; simp

@[simp] theorem map_id : s.map id = s := by ext; simp
@[simp] theorem map_id' : s.map (·) = s := map_id

def erase (s : Set' α) (x : α) : Set' α :=
  ⟨s.1.erase x⟩

@[simp]
theorem mem_erase {x y} : y ∈ s.erase x ↔ x ≠ y ∧ y ∈ s := by
  convert s.1.mem_erase; simp

theorem erase_eq_of_not_mem {x} (h : x ∉ s) : s.erase x = s := by
  aesop

def toSet (s : Set' α) : Set α :=
  {x | x ∈ s}

@[simp]
theorem mem_toSet {x} : x ∈ s.toSet ↔ x ∈ s := by simp [toSet]

@[simp]
theorem toSet_empty : (∅ : Set' α).toSet = ∅ := by ext; simp

@[simp]
theorem toSet_insert {x} : (s.insert x).toSet = insert x s.toSet := by ext; simp

theorem toSet_ofSet {s : Set α} (h : s.Finite) :
(Set'.ofSet s).toSet = s := by
  ext x; simp [mem_ofSet h]

def size (s : Set' α) : ℕ :=
  s.1.size

def count (s : Set' α) (p : α → Bool) : ℕ :=
  s.1.count # λ x _ => p x

@[simp]
theorem size_filter_eq_count {p} : (s.filter p).size = s.count p :=
  s.1.size_filter_eq_count

theorem count_eq_size_filter {p} : s.count p = (s.filter p).size :=
  size_filter_eq_count.symm

@[simp]
theorem count_le_size {p} : s.count p ≤ s.size :=
  s.1.count_le_size

theorem count_eq_zero_iff {p} : s.count p = 0 ↔ ∀ x, x ∈ s → ¬p x := by
  convert s.1.count_eq_zero_iff; nm x; simp
  use λ h₁ h₂ => h₁ # s.1.mem_of_get?_eq_some h₂
  intro h₁ h₂; apply h₁; have h₃ := s.1.get?_eq_some_of_mem h₂
  simp at h₃; exact h₃

@[simp]
theorem count_empty {p} : (∅ : Set' α).count p = 0 :=
  Std.ExtDHashMap.count_empty

theorem count_insert {p i} (h : i ∉ s) :
(s.insert i).count p = s.count p + if p i then 1 else 0 :=
  s.1.count_insert h

theorem subset_iff_exi_disj_union : s₁ ⊆ s₂ ↔ ∃ s₃, (∀ x ∈ s₃, x ∉ s₁) ∧ s₁ ∪ s₃ = s₂ := by
  constructor
  · intro h; use s₂ \ s₁; simp; ext x; simp; tauto
  · rintro ⟨s₃, h₁, rfl⟩; intro x hx; simp_all only [mem_union, true_or]

theorem subset_iff_exi_union : s₁ ⊆ s₂ ↔ ∃ s₃, s₁ ∪ s₃ = s₂ := by
  constructor
  · intro h; use s₂ \ s₁; ext x; simp; tauto
  · rintro ⟨s₃, h₁, rfl⟩; intro x hx; simp_all only [mem_union, true_or]

@[simp] theorem size_empty : (∅ : Set' α).size = 0 := rfl
@[simp] theorem empty_union : ∅ ∪ s = s := by ext; simp
@[simp] theorem union_empty : s ∪ ∅ = s := by ext; simp
@[simp] theorem empty_inter : ∅ ∩ s = ∅ := by ext; simp
@[simp] theorem inter_empty : s ∩ ∅ = ∅ := by ext; simp
@[simp] theorem empty_diff : (∅ : Set' α) \ s = ∅ := by ext; simp
@[simp] theorem diff_empty : s \ (∅ : Set' α) = s := by ext; simp

@[simp]
theorem size_eq_zero_iff : s.size = 0 ↔ s = ∅ := by
  rw [size, ←Std.ExtDHashMap.eq_empty_iff_size_eq_zero, ←eq_iff_inner_eq, ←empty_def]

theorem size_insert {x} (h : x ∉ s) : (s.insert x).size = s.size + 1 := by
  rcases s with ⟨m⟩; simp [mem_def] at h
  simp [Set'.insert, size, Std.ExtDHashMap.size_insert, h]

theorem erase_eq_empty_iff {x} : s.erase x = ∅ ↔ ∀ y, y ∈ s → y = x := by
  rw [ext_iff]; simp; constructor
  · intro hy y hs; by_contra! h; exact hy _ h.symm hs 
  · intro hy y hs; by_contra! h; specialize hy _ h; exact hs hy.symm

theorem mem_iff_of_size_eq_one {x y} (h₁ : s.size = 1) (h₂ : x ∈ s) : y ∈ s ↔ y = x := by
  symm; constructor; rintro rfl; exact h₂; intro h₃; symm; by_contra! h₄
  revert x y h₁; apply s.ind; simp; clear! s; rintro s z hz - x y h₁ hx hy h₂
  simp [size_insert hz] at h₁; subst h₁; simp at hx hy; simp [hx, hy] at h₂

theorem eq_of_size_eq_one_and_mem {x y} (h₁ : s.size = 1)
(h₂ : x ∈ s) (h₃ : y ∈ s) : x = y := by
  rw [mem_iff_of_size_eq_one h₁ h₂] at h₃; exact h₃.symm

theorem size_eq_one_of_size_le_one_and_mem {x}
(h₁ : s.size ≤ 1) (h₂ : x ∈ s) : s.size = 1 := by
  by_contra! h₃; simp [Nat.le_one_iff, h₃] at h₁; simp [h₁] at h₂

theorem insert_erase_eq_of_mem {x} (h : x ∈ s) : (s.erase x).insert x = s := by
  ext y; simp [eq_comm]; constructor
  · rintro (⟨rfl, h₁⟩ | h₁); exact h; exact h₁.2
  · intro h₁; simp [h₁, em]

theorem eq_insert_erase_of_mem {x} (h : x ∈ s) : s = (s.erase x).insert x :=
  insert_erase_eq_of_mem h |>.symm

theorem size_erase_add_one {x} (h : x ∈ s) : (s.erase x).size + 1 = s.size := by
  nth_rw 2 [s.eq_insert_erase_of_mem h]; rw [size_insert # by simp]

theorem size_erase {x} (h : x ∈ s) : (s.erase x).size = s.size - 1 := by
  simp [←size_erase_add_one h]

theorem diff_insert {x} : s₁ \ s₂.insert x = (s₁ \ s₂).erase x := by
  ext y; simp; tauto

theorem erase_diff {x} : (s₁ \ s₂).erase x = s₁ \ s₂.insert x :=
  diff_insert.symm

@[simp]
theorem union_eq_empty_iff : s₁ ∪ s₂ = ∅ ↔ s₁ = ∅ ∧ s₂ = ∅ := by
  simp [ext_iff]; constructor <;> intros <;>
  simp_all only [not_false_eq_true, implies_true, and_self]

@[simp]
theorem erase_empty {x} : (∅ : Set' α).erase x = ∅ := by
  simp [erase_eq_empty_iff]

theorem diff_eq_empty_iff_subset : s₁ \ s₂ = ∅ ↔ s₁ ⊆ s₂ := by
  simp [ext_iff, subset_def]

theorem subset_antisymm (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₁) : s₁ = s₂ := by
  ext x; constructor; apply h₁; apply h₂

@[simp] theorem union_self : s ∪ s = s := by ext; simp
@[simp] theorem inter_self : s ∩ s = s := by ext; simp
@[simp] theorem diff_self : s \ s = ∅ := by ext; simp

theorem exi_mem_of_ne_empty (h : s ≠ ∅) : ∃ x, x ∈ s := by
  simp [eq_empty_iff] at h; exact h

theorem ne_empty_of_mem {x} (h : x ∈ s) : s ≠ ∅ := by
  simp [eq_empty_iff]; use x

theorem eq_empty_of_subset (h₁ : s₁ ⊆ s₂) (h₂ : s₂ = ∅) : s₁ = ∅ := by
  rw [eq_empty_iff] at h₂ ⊢; intro x hx; exact h₂ x # h₁ x hx

theorem ne_empty_of_subset (h₁ : s₁ ⊆ s₂) (h₂ : s₁ ≠ ∅) : s₂ ≠ ∅ := by
  simp [eq_empty_iff] at h₂ ⊢; obtain ⟨x, hx⟩ := h₂; use x, h₁ x hx

@[simp]
theorem insert_ne_empty {x} : s.insert x ≠ ∅ := by
  apply ne_empty_of_mem (x := x); simp

theorem disjoint_comm : (∀ x ∈ s₁, x ∉ s₂) ↔ (∀ x ∈ s₂, x ∉ s₁) := by
  tauto

theorem diff_eq_left_iff : s₁ \ s₂ = s₁ ↔ ∀ x ∈ s₁, x ∉ s₂ := by
  simp [ext_iff]

theorem diff_eq_left_iff' : s₁ \ s₂ = s₁ ↔ ∀ x ∈ s₂, x ∉ s₁ := by
  simp [ext_iff]; exact disjoint_comm

@[simp]
theorem diff_eq_right_iff : s₁ \ s₂ = s₂ ↔ s₁ = ∅ ∧ s₂ = ∅ := by
  simp [ext_iff, forall_and]

theorem mem_of_subset {x} (h : s₁ ⊆ s₂) (hx : x ∈ s₁) : x ∈ s₂ := h x hx
theorem not_mem_of_subset {x} (h : s₁ ⊆ s₂) (hx : x ∉ s₂) : x ∉ s₁ := (hx # h x ·)

theorem ne_empty_of_size_ne_zero (h : s.size ≠ 0) : s ≠ ∅ := by
  simp at h; exact h

theorem ne_empty_of_size_eq_add_one {n} (h : s.size = n + 1) : s ≠ ∅ := by
  rintro rfl; simp at h

theorem size_eq_one_iff : s.size = 1 ↔ ∃ x ∈ s, ∀ y ∈ s, y = x := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := s.exi_mem_of_ne_empty # ne_empty_of_size_eq_add_one h
    use x, hx; intro y hy; apply eq_of_size_eq_one_and_mem h hy hx
  · rintro ⟨x, hx, h⟩
    rw [eq_insert_erase_of_mem hx, size_insert # by simp]
    simp [eq_empty_iff]
    intro y h₁ hy
    exact ne_symm' h₁ # h y hy

theorem size_eq_one_of {x} (hx : x ∈ s) (h : ∀ y, y ∈ s → y = x) : s.size = 1 := by
  rw [size_eq_one_iff]; use x

theorem eq_insert_empty_of_size_eq_one {x}
(h : s.size = 1) (hx : x ∈ s) : s = (∅ : Set' α).insert x := by
  ext y; simp; symm; constructor; rintro rfl; exact hx
  intro hy; exact eq_of_size_eq_one_and_mem h hy hx

@[simp]
theorem erase_subset {x} : s.erase x ⊆ s := by
  intro y; simp

@[simp]
theorem empty_subset : ∅ ⊆ s := by
  intro; simp

def toMap (s : Set' α) (f : α → β) : Map α β :=
  ⟨s.1.map # λ x _ => f x⟩

omit hb₁ hb₂ in @[simp]
theorem mem_toMap {f : α → β} {i} : i ∈ s.toMap f ↔ i ∈ s := by
  rcases s with ⟨m⟩
  simp [toMap, mem_def, Map.mem_def]

omit hb₁ hb₂ in @[simp]
theorem get?_toMap_eq_some_iff {f : α → β} {i x} :
(s.toMap f).get? i = some x ↔ i ∈ s ∧ f i = x := by
  rcases s with ⟨m⟩
  simp [toMap, Map.get?, mem_def]
  rintro rfl
  rw [Std.ExtDHashMap.mem_iff_get?_eq_some]
  simp [exi_unit_iff]

omit hb₁ hb₂ in @[simp]
theorem toMap_empty {f : α → β} : (∅ : Set' α).toMap f = ∅ := by
  ext i x; simp

omit ha₁ ha₂ in @[simp]
theorem mem_list_foldl_map_push_iff {xs : List α} {f : α → β} {y : β} {mp : Map β ℕ} :
y ∈ xs.foldl (λ mp x => mp.push (f x)) mp ↔ y ∈ mp ∨ ∃ x ∈ xs, f x = y := by
  induction xs generalizing mp <;> simp
  nm x xs ih
  simp [ih]
  tauto

theorem toList_erase [ha : LinearOrder α] {x} : (s.erase x).toList = s.toList.erase x := by
  rw [List.eq_iff_of_nodup_and_sorted']
  rotate_left
  · simp
  · apply List.nodup_erase; simp
  · simp
  · apply List.sorted_erase; simp
  intro y
  simp [List.mem_erase_iff_of_nodup]
  tauto

theorem count_eq_countP_toList [ha : LinearOrder α] {p : α → Bool} :
s.count p = s.toList.countP p := by
  generalize hn : s.size = n
  induction n generalizing s
  · simp at hn; simp [hn]
  nm n ih
  cases h : s.toList
  · simp at h; simp [h] at hn
  nm x xs
  have h₁ : x ∈ s
  · rw [←mem_toList, h]
    simp
  have h₂ := insert_erase_eq_of_mem h₁
  rw [←h₂, count_insert # by simp, List.countP_cons]
  have h₃ : (s.erase x).size = n
  · simp [size_erase h₁, hn]
  rw [ih h₃]
  simp [toList_erase, h]

theorem fold_map_push_eq_map_toMap {f : α → β} :
s.fold (λ mp x => mp.push # f x) (∅ : Map β ℕ) Map.push_push_comm =
(s.map f).toMap (s.count # λ x => f x = ·) := by
  classical
  rw [fold_eq_foldl_toList]
  ext y n
  simp
  generalize hm : (∅ : Map β ℕ) = mp
  suffices H : ((s.toList.foldl (λ (mp : Map β ℕ) x => mp.push # f x) mp).get? y).getD 0 =
    (mp.get? y).getD 0 + s.count (λ x => f x = y)
  · subst hm;
    simp at H
    constructor
    · intro h
      simp [h ]at H
      subst H
      simp
      replace h := Map.mem_of_get?_eq_some h
      simp at h
      exact h
    · rintro ⟨⟨x, hx, rfl⟩, rfl⟩
      generalize s.toList.foldl (λ (mp : Map β ℕ) x => mp.push # f x) ∅ = mp₀ at H ⊢
      cases h : mp₀.get? # f x <;> simp [h] at H
      · rw [eq_comm] at H
        simp [count_eq_zero_iff] at H
        cases H x hx rfl
      nm k
      simp [H]
  clear hm
  rw [count_eq_countP_toList]
  generalize s.toList = xs; clear! s
  induction xs generalizing mp <;> simp
  nm x xs ih
  rw [ih]; clear ih
  simp [List.countP_cons, Map.push, Map.get?_insert]
  split_ifs with h
  · subst h
    simp
    ring_nf
  simp

theorem fold_map_push_eq_toMap :
s.fold (λ mp x => mp.push x) (∅ : Map α ℕ) Map.push_push_comm =
s.toMap (s.count # λ y => y = ·) := by
  convert s.fold_map_push_eq_map_toMap (f := id); simp

omit hb₁ hb₂ in
theorem get?_toMap_eq {f : α → β} {x} :
(s.toMap f).get? x = if x ∈ s then some (f x) else none := by
  rcases s with ⟨m⟩
  simp [toMap, Map.get?, mem_def]
  cases h : m.get? x
  · rw [Std.ExtDHashMap.get?_eq_none_iff] at h
    simp [h]
  nm y
  simp
  rw [Std.ExtDHashMap.mem_iff_get?_eq_some]
  use y

@[simp]
theorem length_toList [ha : LinearOrder α] : s.toList.length = s.size := by
  rcases s with ⟨m⟩
  simp [toList, size, Std.ExtDHashMap.lift, Std.ExtDHashMap.size]
  induction m; simp

omit hb₁ hb₂ in @[simp]
theorem size_toMap {f : α → β} : (s.toMap f).size = s.size := by
  rcases s with ⟨m⟩
  simp [toMap, size, Map.size]

theorem size_ofList_of_nodup {xs : List α} (h : xs.Nodup) : (ofList xs).size = xs.length := by
  simp [ofList, size]
  rw [Std.ExtDHashMap.size_ofList]
  · simp
  · simpa [List.pairwise_map]

@[simp]
theorem size_ofFinset {s : Finset α} : (ofFinset s).size = s.card := by
  simp [ofFinset, size_ofList_of_nodup]
  change s.val.toList.length = s.card; simp

@[simp]
theorem subset_insert {x} : s ⊆ s.insert x := by
  intro y hy; simp [hy]

def unionList (xs : List (Set' α)) : Set' α :=
  xs.foldl (· ∪ ·) ∅

@[simp]
theorem unionList_nil : unionList ([] : List (Set' α)) = ∅ := rfl

theorem union_comm : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext; simp [or_comm]

theorem inter_comm : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  ext; simp [and_comm]

theorem union_assoc : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  ext; simp [or_assoc]

theorem inter_assoc : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by
  ext; simp [and_assoc]

@[simp]
theorem unionList_cons {s : Set' α} {xs} : unionList (s :: xs) = s ∪ unionList xs := by
  unfold unionList
  generalize (∅ : Set' α) = z
  simp
  induction xs generalizing s z
  · simp [union_comm]
  nm s' xs ih
  simp
  rw [←ih]; clear ih
  congr 1
  simp_rw [union_assoc]
  congr 1
  exact union_comm

@[simp]
theorem unionList_append {xs ys : List (Set' α)} :
unionList (xs ++ ys) = unionList xs ∪ unionList ys := by
  induction xs generalizing ys <;> simp
  nm s xs ih; rw [ih, union_assoc]

theorem unionList_of_perm {xs ys : List (Set' α)}
(h : xs.Perm ys) : unionList xs = unionList ys := by
  induction h <;> clear xs ys; rfl
  · nm s xs ys h₁ ih; simp [ih]
  · nm s t xs; simp; simp_rw [←union_assoc, union_comm]
  · nm xs ys zs h₁ h₂ ih₁ ih₂; rwa [ih₁]

@[simp]
theorem mem_unionList {xs : List (Set' α)} {x} :
x ∈ unionList xs ↔ ∃ s ∈ xs, x ∈ s := by
  induction xs <;> simp; grind

theorem size_le_of_subset (h : s₁ ⊆ s₂) : s₁.size ≤ s₂.size := by
  induction s₁ using Set'.ind generalizing s₂
  · simp
  nm s₁ x h₁ ih
  rw [size_insert h₁]
  specialize @ih (s₂.erase x) _
  · intro y
    specialize h y
    simp at h ⊢
    grind
  rw [size_erase # h x # by simp] at ih
  suffices : s₂.size ≠ 0; omega
  simp [eq_empty_iff]
  use x
  apply h
  simp

theorem size_eq_size_add_one_of
(h : ∃ x, x ∉ s₂ ∧ s₁ = s₂.insert x) : s₁.size = s₂.size + 1 := by
  obtain ⟨x, hx, rfl⟩ := h; rw [size_insert hx]

theorem size_inter_insert_left {x} (h₁ : x ∉ s₁) (h₂ : x ∈ s₂) :
(s₁.insert x ∩ s₂).size = (s₁ ∩ s₂).size + 1 := by
  apply size_eq_size_add_one_of; use x
  simp [h₁, h₂]; ext; simp; grind

theorem size_inter_insert_right {x} (h₁ : x ∈ s₁) (h₂ : x ∉ s₂) :
(s₁ ∩ s₂.insert x).size = (s₁ ∩ s₂).size + 1 := by
  simp_rw [inter_comm (s₁ := s₁)]; exact size_inter_insert_left h₂ h₁

theorem insert_inter_eq {x} (h : x ∈ s₂) : s₁.insert x ∩ s₂ = (s₁ ∩ s₂).insert x := by
  ext; simp; grind

theorem inter_insert_eq {x} (h : x ∈ s₁) : s₁ ∩ s₂.insert x = (s₁ ∩ s₂).insert x := by
  ext; simp; grind

theorem subset_of_eq (h : s₁ = s₂) : s₁ ⊆ s₂ := by
  simp [h]

theorem subset_of_inter_eq_left (h : s₁ ∩ s₂ = s₁) : s₁ ⊆ s₂ := by
  intro x hx; rw [←h] at hx; simp at hx; tauto

theorem subset_of_inter_eq_right (h : s₁ ∩ s₂ = s₂) : s₂ ⊆ s₁ := by
  intro x hx; rw [←h] at hx; simp at hx; tauto

theorem inter_eq_left_of_subset (h : s₁ ⊆ s₂) : s₁ ∩ s₂ = s₁ := by
  ext x; specialize h x; simpa

theorem inter_eq_right_of_subset (h : s₂ ⊆ s₁) : s₁ ∩ s₂ = s₂ := by
  ext x; specialize h x; simpa

@[simp]
theorem inter_eq_left_iff : s₁ ∩ s₂ = s₁ ↔ s₁ ⊆ s₂ :=
  ⟨subset_of_inter_eq_left, inter_eq_left_of_subset⟩

@[simp]
theorem inter_eq_right_iff : s₁ ∩ s₂ = s₂ ↔ s₂ ⊆ s₁ :=
  ⟨subset_of_inter_eq_right, inter_eq_right_of_subset⟩

theorem eq_of_subset_and_size_eq (h₁ : s₁ ⊆ s₂) (h₂ : s₁.size = s₂.size) : s₁ = s₂ := by
  induction s₁ using ind generalizing s₂
  · symm at h₂; simp at h₂; rw [h₂]
  nm s₁ x hx ih
  rw [size_insert hx] at h₂
  specialize @ih (s₂.erase x) _
  · intro y
    specialize h₁ y
    simp at h₁ ⊢
    grind
  have h₃ := h₁ x # by simp
  rw [size_erase h₃] at ih
  specialize ih # by omega
  rw [ih, insert_erase_eq_of_mem h₃]

theorem subset_of_size_inter_eq_size_left (h : (s₁ ∩ s₂).size = s₁.size) : s₁ ⊆ s₂ :=
  subset_of_inter_eq_left # eq_of_subset_and_size_eq (by simp) h

theorem subset_of_size_inter_eq_size_right (h : (s₁ ∩ s₂).size = s₂.size) : s₂ ⊆ s₁ :=
  subset_of_inter_eq_right # eq_of_subset_and_size_eq (by simp) h

@[simp]
theorem size_inter_eq_size_left_iff : (s₁ ∩ s₂).size = s₁.size ↔ s₁ ⊆ s₂ := by
  use subset_of_size_inter_eq_size_left; intro h; rw [inter_eq_left_of_subset h]

@[simp]
theorem size_inter_eq_size_right_iff : (s₁ ∩ s₂).size = s₂.size ↔ s₂ ⊆ s₁ := by
  use subset_of_size_inter_eq_size_right; intro h; rw [inter_eq_right_of_subset h]

@[simp]
theorem insert_subset_iff {x} : s₁.insert x ⊆ s₂ ↔ x ∈ s₂ ∧ s₁ ⊆ s₂ := by
  simp [subset_def]

theorem diff_insert_eq_diff_erase {x} : s₁ \ s₂.insert x = (s₁ \ s₂).erase x := by
  ext y; simp; grind

theorem size_diff_add_eq_of_subset (h : s₁ ⊆ s₂) : (s₂ \ s₁).size + s₁.size = s₂.size := by
  induction s₁ using ind generalizing s₂; simp
  nm s₁ x hx ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  rw [size_insert hx, diff_insert_eq_diff_erase]
  rw [size_erase # by simp; grind]
  specialize ih h₂
  rw [←add_assoc]
  convert ih using 1; clear ih
  cases h₃ : (s₂ \ s₁).size
  rotate_left; omega
  simp [diff_eq_empty_iff_subset] at h₃
  cases hx # h₃ x h₁

theorem size_diff_eq_of_subset (h : s₁ ⊆ s₂) : (s₂ \ s₁).size = s₂.size - s₁.size := by
  have := size_diff_add_eq_of_subset h; omega

def ssubset (s₁ s₂ : Set' α) : Prop :=
  s₁ ⊆ s₂ ∧ s₁ ≠ s₂

instance : HasSSubset (Set' α) := ⟨ssubset⟩
theorem ssubset_def : s₁ ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ s₁ ≠ s₂ := by rfl

@[simp]
theorem union_eq_left_iff_subset : s₁ ∪ s₂ = s₁ ↔ s₂ ⊆ s₁ := by
  simp [ext_iff, subset_def]

@[simp]
theorem union_eq_right_iff_subset : s₁ ∪ s₂ = s₂ ↔ s₁ ⊆ s₂ := by
  simp [ext_iff, subset_def]

theorem ssubset_iff_exi_disj_union :
s₁ ⊂ s₂ ↔ ∃ s₃, s₃ ≠ ∅ ∧ (∀ x ∈ s₃, x ∉ s₁) ∧ s₁ ∪ s₃ = s₂ := by
  rw [ssubset_def, subset_iff_exi_disj_union]
  by_cases h : s₁ = s₂
  · simp [h]
    intro s₃ h₁ h₂
    simp [subset_def]
    choose x hx using exi_mem_of_ne_empty h₁
    use x, hx, h₂ x hx
  simp [h]
  apply exists_congr
  intro s₃
  simp
  rintro h₁ rfl rfl
  simp at h

theorem insert_union {x} : s₁.insert x ∪ s₂ = (s₁ ∪ s₂).insert x := by
  ext; simp; grind

theorem union_insert {x} : s₁ ∪ s₂.insert x = (s₁ ∪ s₂).insert x := by
  ext; simp; grind

theorem size_union (h : ∀ x ∈ s₁, x ∉ s₂) : (s₁ ∪ s₂).size = s₁.size + s₂.size := by
  induction s₁ using ind; simp
  clear! s₁
  nm s₁ x hx ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  rw [size_insert hx, Nat.add_one_add, insert_union, size_insert # by simp; grind]
  rw [ih h₂]

theorem size_union' (h : ∀ x ∈ s₂, x ∉ s₁) : (s₁ ∪ s₂).size = s₁.size + s₂.size := by
  apply size_union; grind

@[simp]
theorem pos_size_iff : 0 < s.size ↔ s ≠ ∅ := by
  simp [Nat.pos_iff_ne_zero]

theorem size_lt_of_ssubset (h : s₁ ⊂ s₂) : s₁.size < s₂.size := by
  rw [ssubset_iff_exi_disj_union] at h; obtain ⟨s₂, h₁, h₂, rfl⟩ := h; simpa [size_union' h₂]

theorem eq_of_subset_and_subset (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  eq_of_subset_and_size_eq h₁ # le_antisymm (size_le_of_subset h₁) (size_le_of_subset h₂)

theorem ssubset_iff_exi : s₁ ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ∃ x, x ∈ s₂ ∧ x ∉ s₁ := by
  rw [ssubset_def]
  simp
  intro h
  rw [ext_iff]
  rw [subset_def] at h
  grind

theorem diff_subset_of_right (h₁ : s₂ ⊆ s₃) : s₁ \ s₃ ⊆ s₁ \ s₂ := by
  simp [subset_def] at h₁ ⊢; tauto

theorem diff_ssubset_of_right (h₁ : s₂ ⊆ s₃)
(h₂ : ∃ x ∈ s₁, x ∈ s₃ ∧ x ∉ s₂) : s₁ \ s₃ ⊂ s₁ \ s₂ := by
  choose x hx h₂ h₃ using h₂
  rw [ssubset_iff_exi]
  simp [subset_def] at h₁ ⊢
  tauto

noncomputable
def compr (P : α → Prop) : Set' α :=
  ofSet # setOf P

def singleton (x : α) : Set' α :=
  ofList [x]

@[simp]
theorem mem_singleton {x y : α} : x ∈ singleton y ↔ x = y := by
  simp [singleton]

@[simp]
theorem singleton_eq_iff {x y : α} : singleton x = singleton y ↔ x = y := by
  simp [ext_iff]

@[simp]
theorem singleton_ne_empty {x : α} : singleton x ≠ ∅ := by
  simp [ext_iff]

@[simp]
theorem size_singleton {x : α} : (singleton x).size = 1 := by
  simp [singleton, size_ofList_of_nodup]

@[simp]
theorem empty_insert_eq_singleton {x : α} : (∅ : Set' α).insert x = singleton x := by
  simp [ext_iff]

@[simp]
theorem toSet_singleton {x : α} : (singleton x).toSet = {x} := by
  ext; simp

@[simp]
theorem erase_singleton_self {x : α} : (singleton x).erase x = ∅ := by
  ext; simp; grind

@[simp]
theorem insert_singleton_self {x : α} : (singleton x).insert x = singleton x := by
  ext; simp

def toFinset (s : Set' α) : Finset α :=
  s.fold (λ s₁ x => insert x s₁) ∅ # by grind

@[simp]
theorem toFinset_empty : (∅ : Set' α).toFinset = ∅ := by
  simp [toFinset]

theorem mem_toFinset_of_mem {x} (hx : x ∈ s) : x ∈ s.toFinset := by
  classical
  unfold toFinset
  rw [fold_eq_foldl_toList]
  rw [←mem_toList] at hx
  generalize s.toList = xs at hx ⊢; clear! s
  induction xs using List.reverseRecOn <;> grind

@[simp]
theorem ofList_cons {xs : List α} {x} : ofList (x :: xs) = (ofList xs).insert x := by
  ext; simp

@[simp]
theorem ofList_append {xs ys : List α} : ofList (xs ++ ys) = ofList xs ∪ ofList ys := by
  ext; simp

theorem ind_ofList [ha : LinearOrder α] {p : Set' α → Prop}
(h : ∀ (xs : List α), xs.Sorted (· < ·) → p (ofList xs)) (s : Set' α) : p s := by
  induction s using ind_ofList'; nm xs h₁ h₂; apply h _ # h₂.lt_of_le h₁

@[simp]
theorem sorted_toList [ha : LinearOrder α] : s.toList.Sorted (· < ·) :=
  sorted_toList'.lt_of_le nodup_toList

theorem toList_ofList_of_nodup [ha : LinearOrder α] {xs : List α}
(h : xs.Nodup) : (ofList xs).toList = xs.mergeSort := by
  induction xs; simp
  nm x xs ih
  simp at h ⊢
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  rw [List.eq_iff_of_nodup_and_sorted (r := (· < ·))] <;> try simp [h₁, h₂]
  · intro y z h₃ h₄ h₅ h₆
    replace h₅ := h₅.trans h₆
    simp at h₅
  · have H := @(x :: xs).sorted_mergeSort α (le := (· ≤ ·))
    simp at H
    apply List.Sorted.lt_of_le _ # by simp [h₁, h₂]
    apply H

theorem toList_ofList_of_sorted [ha : LinearOrder α] {xs : List α}
(h : xs.Sorted (· < ·)) : (ofList xs).toList = xs := by
  rw [toList_ofList_of_nodup h.nodup]
  rw [List.mergeSort_of_sorted]
  simp; exact h.le_of_lt

omit hb₁ hb₂
theorem fold_insert_of_notMem' {f : β → α → β} {z x hh} (hx : x ∉ s) :
(s.insert x).fold f z hh = s.fold f (f z x) hh := by
  classical
  simp_rw [fold_eq_foldl_toList]  
  have h₁ : x ∈ (s.insert x).toList; simp
  have h₂ : s.insert x |>.toList.Nodup; simp
  rw [List.mem_iff_append] at h₁
  choose xs ys h₁ using h₁
  rw [h₁] at h₂ ⊢
  suffices h₃ : s.toList = xs ++ ys
  · rw [h₃]
    simp
    congr
    clear! ys x
    rw [List.foldl_apply_comm]
    apply hh
  have h₅ := s.insert x |>.sorted_toList
  rw [h₁] at h₅
  induction s using ind_ofList'
  nm zs H₁ H₂
  replace H₂ := H₂.lt_of_le H₁
  rw [toList_ofList_of_sorted H₂]
  simp at hx
  have H₃ := h₂.of_append_left
  have H₄ : (xs ++ x :: ys).erase x = (xs ++ ys)
  · grind
  have H₅ : xs ++ ys |>.Nodup
  · rw [←H₄]; exact List.nodup_erase h₂
  have H₆ := List.nodup_append_comm.mp H₅
  apply List.eq_of_perm_of_sorted_loc (r := (· ≤ ·)) <;> try simp
  · symm
    apply List.perm_of_nodup_and_subset_and_length_eq H₁
    · intro y hy
      simp
      replace h₁ := congrArg (y ∈ ·) h₁
      simp at h₁
      grind
    · rw [←H₄, ←h₁]
      simp
      rw [size_insert # by simpa]
      simp
      rw [size_ofList_of_nodup H₁]
  · apply H₂.le_of_lt
  · rw [←H₄, ←h₁]; apply List.sorted_erase; simp

omit hb₁ hb₂
theorem fold_insert_of_notMem {f : β → α → β} {z x hh} (hx : x ∉ s) :
(s.insert x).fold f z hh = f (s.fold f z hh) x := by
  classical
  rw [fold_insert_of_notMem' hx]
  simp_rw [fold_eq_foldl_toList]
  rw [List.foldl_apply_comm]
  apply hh

@[simp]
theorem toFinset_insert {x} : (s.insert x).toFinset = insert x s.toFinset := by
  classical
  by_cases hx : x ∈ s
  · rw [insert_eq_of_mem hx, Finset.insert_eq_of_mem]
    exact mem_toFinset_of_mem hx
  exact fold_insert_of_notMem hx

@[simp]
theorem mem_toFinset {x} : x ∈ s.toFinset ↔ x ∈ s := by
  classical
  refine ⟨?_, mem_toFinset_of_mem⟩
  intro h
  rw [toFinset] at h
  rw [s.fold_eq_foldl_toList] at h
  rw [←mem_toList]
  generalize s.toList = xs at h ⊢; clear! s
  induction xs using List.reverseRecOn <;> grind

theorem toSet_union : (s₁ ∪ s₂).toSet = s₁.toSet ∪ s₂.toSet := by
  ext; simp

theorem toSet_inter : (s₁ ∩ s₂).toSet = s₁.toSet ∩ s₂.toSet := by
  ext; simp

theorem toFinset_union : (s₁ ∪ s₂).toFinset = s₁.toFinset ∪ s₂.toFinset := by
  ext; simp

theorem toFinset_inter : (s₁ ∩ s₂).toFinset = s₁.toFinset ∩ s₂.toFinset := by
  ext; simp

@[simp]
theorem finite_toSet : s.toSet.Finite := by
  apply Set.finite_of_subset_finset s.toFinset; simp

@[simp]
theorem toFinset_coe_set : (s.toFinset : Set α) = s.toSet := by
  ext; simp

@[simp]
theorem card_toFinset : s.toFinset.card = s.size := by
  induction s using ind; simp
  clear! s; nm s x hx ih
  simp
  rw [size_insert hx, Finset.card_insert_of_notMem, ih]
  simpa

@[simp]
theorem ncard_toSet : s.toSet.ncard = s.size := by
  rw [←toFinset_coe_set, Set.ncard_coe_finset]; simp

@[simp]
theorem ofSet_toSet_list {xs : List α} : ofSet xs.toSet = ofList xs := by
  ext; simp; rw [mem_ofSet] <;> simp

@[simp]
theorem list_toSet_ofList {xs : List α} : (ofList xs).toSet = xs.toSet := by
  ext; simp;

theorem ssubset_of (x : α) (h₁ : s₁ ⊆ s₂) (h₂ : x ∉ s₁) (h₃ : x ∈ s₂) : s₁ ⊂ s₂ := by
  use h₁; rintro rfl; contradiction