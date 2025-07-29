import AP.Util.Data.Set.Defs

namespace Util.Data

universe u v w
variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α]

namespace Set

def mem (s : Set α) (i : α) : Prop :=
  DMap.mem s i

instance : Membership α (Set α) := ⟨mem⟩

protected def insert (i : α) (s : Set α) : Set α :=
  DMap.insert s i ()

instance : Insert α (Set α) := ⟨Set.insert⟩

def toList (s : Set α) : List α :=
  (DMap.toList s).map (·.1)

def ofList (xs : List α) : Set α :=
  DMap.ofList # xs.map (⟨·, ()⟩)

def toDMap {β : α → Type v} (s : Set α) (f : (i : α) → β i) : DMap α β :=
  DMap.map s # @λ i _ => f i

def toMap {β : Type v} (s : Set α) (f : α → β) : Map α β :=
  DMap.map s # @λ i _ => f i

variable {s : Set α}

theorem mem_def {i} : i ∈ s ↔ DMap.instMembership.mem s i := by rfl

instance {i} : Decidable (s.mem i) := by
  change Decidable (DMap.mem s i)
  infer_instance

instance {i} : Decidable (i ∈ s) := by
  change Decidable (s.mem i)
  infer_instance

@[simp]
theorem mem_toDMap {β : α → Type v} {f : (i : α) → β i} {i} :
i ∈ s.toDMap f ↔ i ∈ s := by simp [toDMap]

@[simp]
theorem mem_toMap {β : Type v} {f : α → β} {i} :
i ∈ s.toMap f ↔ i ∈ s := by simp [toMap, Map.mem_def]

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : Set α).mem i := by
  simp [empty_def, mem]; exact DMap.not_mem_empty'

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : Set α) :=
  not_mem_empty'

theorem eq_empty_iff : s = ∅ ↔ ∀ i, i ∉ s := DMap.eq_empty_iff

@[simp]
theorem toDMap_empty {β : α → Type v} {f : (i : α) → β i} :
(∅ : Set α).toDMap f = ∅ := by simp [DMap.eq_empty_iff]

theorem ext_iff {s₁ s₂ : Set α} : s₁ = s₂ ↔ ∀ i, i ∈ s₁ ↔ i ∈ s₂ := by
  unfold Set at s₁ s₂
  rw [DMap.ext_iff]
  apply forall_congr'
  intro i
  simp_rw [DMap.get?_eq_ite_of_unit]
  split_ifs with h₁ h₂ h₂ <;> simp [h₁, h₂]

@[ext]
theorem ext {s₁ s₂ : Set α} (h : ∀ i, i ∈ s₁ ↔ i ∈ s₂) : s₁ = s₂ := by
  rwa [ext_iff]

@[simp]
theorem toDMap_eq_empty_iff {β : α → Type v} {f : (i : α) → β i} :
s.toDMap f = ∅ ↔ s = ∅ := by simp [eq_empty_iff, DMap.eq_empty_iff]

@[simp]
theorem toMap_eq_empty_iff {β : Type v} {f : α → β} :
s.toMap f = ∅ ↔ s = ∅ := by simp [eq_empty_iff, Map.eq_empty_iff]

theorem ofList_eq_ofList_iff {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) : ofList xs = ofList ys ↔ xs.Perm ys := by
  convert DMap.ofList_eq_ofList_iff _ _
  rw [List.perm_ext_iff_of_nodup hx hy]
  rw [List.perm_ext_iff_of_nodup]
  any_goals
    try simp
    rwa [List.nodup_map_iff]
    intro a b h
    simp at h
    exact h
  simp
  constructor
  · rintro h ⟨x, u⟩
    simp [h]
  · intro h x
    specialize h ⟨x, ()⟩
    simp at h
    exact h
  all_goals simpa

@[simp]
theorem mem_ofList {xs : List α} {i} :
i ∈ ofList xs ↔ i ∈ xs := by simp [mem_def, ofList]

def ofFinset (s : Finset α) : Set α := by
  rcases s with ⟨m, h⟩
  apply m.liftWith ofList
  intro xs ys h₁ h₂
  generalize hz : m.out = zs at h₁ h₂ ⊢
  change m.toList = _ at hz
  change zs.Perm xs at h₁
  change zs.Perm ys at h₂
  have h₃ : zs.Nodup :=
    by
      subst zs
      simpa
  have h₄ := h₁.nodup h₃
  have h₅ := h₂.nodup h₃
  rw [ofList_eq_ofList_iff h₄ h₅]
  exact h₁.symm.trans h₂

@[simp]
theorem mem_ofFinset {s : Finset α} {i} : i ∈ ofFinset s ↔ i ∈ s := by
  rcases s with ⟨m, h⟩
  simp [ofFinset]
  exact Multiset.mem_toList

def univ [ha : Fintype α] : Set α :=
  ofFinset ha.elems

@[simp]
theorem mem_univ [ha : Fintype α] {i : α} : i ∈ univ := by simp [univ]

@[simp]
theorem mem_insert {x y} : y ∈ insert x s ↔ y = x ∨ y ∈ s :=
  DMap.mem_insert

theorem nonempty_insert {x} : insert x s ≠ ∅ :=
  DMap.nonempty_insert

@[simp]
theorem nodup_toList : s.toList.Nodup := by
  unfold Set at s
  unfold toList
  rw [List.nodup_map_iff_inj_on # by simp]
  rintro ⟨i, x⟩ hx ⟨j, y⟩ hy h
  dsimp at h
  simp [h]

@[simp]
theorem sorted_toList : s.toList.Sorted (· ≤ ·) := by
  unfold Set at s
  unfold toList
  set f : α → Σ (i : α), Unit := λ x => ⟨x, ()⟩ with hf
  set g : (Σ (i : α), Unit) → α := λ x => x.1 with hg
  have hb : f.Bijective :=
    by
      constructor
      · intro a b h
        simp [hf] at h
        exact h
      · intro y
        use y.1
  let e : Equiv _ _ := by
    apply Equiv.mk f g
    · intro x
      rfl
    · intro x
      rfl
  let lin := e.toLinearOrder
  rw [StrictMono.sorted_le_listMap]
  rotate_left
  · intro x y h
    exact h
  exact DMap.sorted_toList

def has (x : α) : Bool :=
  (s.get? x).isSome

@[simp]
theorem mem_toList {x} : x ∈ s.toList ↔ s.has x := by
  simp [toList, has, Option.isSome_iff_exists]

@[simp]
theorem toList_eq_toList {s₁ s₂ : Set α} :
s₁.toList = s₂.toList ↔ s₁ = s₂ := by
  refine' ⟨λ h => _, by rintro rfl; rfl⟩
  unfold toList at h
  rw [←DMap.toList_eq_toList]
  rwa [List.map_inj_right] at h
  rintro ⟨x, _⟩ ⟨y, _⟩
  simp

@[simp]
theorem toList_eq_nil_iff : s.toList = [] ↔ s = ∅ := by
  simp [toList]

def map {β : Type*} [hb₁ : LinearOrder β] [hb₂ : Hashable β]
(f : α → β) (s : Set α) : Set β := by
  nm x; clear x
  sorry

#check 0 #exit

section Fold

variable {β : Type*} (op : β → β → β)
  [hc : Std.Commutative op] [ha : Std.Associative op]

def fold (b : β) (f : α → β) (s : Set α) : β :=

end Fold

def fold {β : Type*} (f : α → β → β) (z : β)
(h_comm : ∀ {x y}, )

#check 0 #exit

Implement min and max using folding

def min (s : Set α) : Option α :=
  s.toList.head?

def max (s : Set α) : Option α :=
  s.toList.getLast?

#check 0 #exit

-----

theorem min_of_nonempty (h : s ≠ ∅) : ∃ x, s.max = some x := by
  unfold max
  simp [ext_iff] at h
  contrapose! h
  rw [←Option.eq_none_iff_forall_ne_some] at h
  simp at h
  intro x
  simp [Li]

def map {β : Type*} [Hashable β] [LinearOrder β] (f : α → β) (s : Set α) : Set β := by
  nm x h₂ h₃; clear x
  refine' s.lift _ _
  · intro m
    apply Set.ofList
    exact m.keys.map f
  intro m₁ m₂ h
  simp

#check 0 #exit

theorem mem_union_iff {a : α} (m₁ m₂ : HashSet α) :
a ∈ m₁.union m₂ ↔ a ∈ m₁ ∨ a ∈ m₂ := by
  sorry

theorem contains_toArray_iff {a : α} (m : HashSet α) :
m.contains a ↔ m.toArray.contains a := by
  rw [contains_iff_mem]
  unfold toArray