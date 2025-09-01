import AP.Util.DHashMap

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Std.ExtDHashMap α β}

namespace Std.ExtDHashMap

@[simp]
theorem not_mem_empty' {i : α} : i ∉ (∅ : Std.ExtDHashMap α β) :=
  not_mem_empty

@[simp]
theorem not_mem_lift_empty {i : α} :
¬Membership.mem (γ := Std.ExtDHashMap α β) ⟨⟦∅⟧⟩ i :=
  not_mem_empty

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  rw [←Option.isSome_iff_exists]
  exact mem_iff_isSome_get?

theorem get?_eq_some_of_mem {i : α} (h : i ∈ mp) : ∃ x, mp.get? i = some x := by
  rwa [←mem_iff_get?_eq_some]

theorem get?_eq_none_of_not_mem {i : α} (h : i ∉ mp) : mp.get? i = none := by
  simp [mem_iff_get?_eq_some] at h
  rwa [Option.eq_none_iff_forall_ne_some]

@[simp]
theorem get?_eq_none_iff {i} : mp.get? i = none ↔ i ∉ mp := by
  refine' ⟨_, get?_eq_none_of_not_mem⟩
  intro h
  contrapose! h
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  simp [hx]

def toList [LinearOrder α] (mp : Std.ExtDHashMap α β) : List (Σ i, β i) :=
  mp.lift Std.DHashMap.toSortedList # by simp

@[simp]
theorem toList_empty [LinearOrder α] : (∅ : Std.ExtDHashMap α β).toList = [] := by
  change List.mergeSort _ _ = _; simp

@[simp]
theorem ofList_snoc {xs} {x : Σ i, β i} :
ofList (xs ++ [x]) = Insert.insert x (ofList xs) := by
  dsimp
  unfold Std.ExtDHashMap.ofList Std.ExtDHashMap.insert
  rw [Std.DHashMap.ofList_snoc]; rfl

@[simp]
theorem mem_insert' {x : Σ i, β i} {i} :
i ∈ Insert.insert x mp ↔ i = x.1 ∨ i ∈ mp := by
  simp; tauto

@[simp]
theorem mem_ofList' {xs : List (Σ i, β i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  change contains _ _ ↔ _
  simp only [contains_ofList, List.contains_eq_mem, List.mem_map,
    Sigma.exists, exists_and_right, exists_eq_right, decide_eq_true_eq]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  change mp = ⟨⟦∅⟧⟩ ↔ _
  rcases mp with ⟨mp⟩
  simp
  apply mp.ind
  intro m
  rw [Quotient.eq_iff_equiv]
  change m.Equiv ∅ ↔ _
  simp
  exact Std.DHashMap.isEmpty_iff_forall_not_mem

theorem ext_iff' {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ m₁.1.out.Equiv m₂.1.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
  symm; simp
  induction m₁, m₂ using Quotient.inductionOn₂
  nm m₁ m₂
  change ⟦m₁⟧.out ≈ ⟦m₂⟧.out ↔ _
  rw [Quotient.eq_iff_equiv]
  simp
  rfl

theorem ext_iff {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  induction m₁, m₂ using Quotient.inductionOn₂
  rw [Quotient.eq_iff_equiv]
  exact Std.DHashMap.equiv_iff_get?

theorem get?_eq_ite_of_unit {m : Std.ExtDHashMap α (λ _ => Unit)} {i} :
m.get? i = if i ∈ m then some () else none := by
  split_ifs with h
  · obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
    simp [hx]
  rw [get?_eq_none_of_not_mem h]

theorem ofList_eq_ofList_iff {xs ys : List (Σ i, β i)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  have hx' := hx.of_map _
  have hy' := hy.of_map _
  simp [ofList]
  change Std.DHashMap.Equiv _ _ ↔ _
  rw [Std.DHashMap.equiv_iff_toList_perm]
  rw [List.perm_ext_iff_of_nodup hx' hy']
  rw [List.perm_ext_iff_of_nodup (by simp) (by simp)]
  apply forall_congr'
  rintro ⟨i, x⟩
  simp
  generalize h₁ : Std.DHashMap.ofList xs = m₁
  generalize h₂ : Std.DHashMap.ofList ys = m₂
  have h₃ : xs.Perm m₁.toList :=
    by
      subst h₁
      exact (Std.DHashMap.toList_ofList_perm hx).symm
  have h₄ : ys.Perm m₂.toList :=
    by
      subst h₂
      exact (Std.DHashMap.toList_ofList_perm hy).symm
  rw [h₃.mem_iff, h₄.mem_iff]
  simp

omit hh₂ in private theorem range'_aux {ms xs : List α}
{f : (i : α) → Option (β i)} (hm : ms.Nodup) (hx : ms.Perm xs) :
xs.filterMap (λ i => f i |>.map # Sigma.mk i) |>.map (·.1) |>.Nodup := by
  simp [List.map_filterMap, List.nodup_filterMap_iff]
  intro x h₁ y h₂
  rw [hx.nodup_iff, List.nodup_iff_count] at hm
  use hm _
  intro z h₃ w h₄ h₅; exact h₅.symm

def range' [ha : Fintype α] (f : (i : α) → Option (β i)) : Std.ExtDHashMap α β := by
  apply ha.1.1.liftWith # λ xs => ofList # xs.filterMap # λ i => (f i).map (⟨i, ·⟩)
  classical
  rcases ha with ⟨⟨m, hm⟩, ha⟩
  replace hm : m.toList.Nodup := by simpa
  intro xs ys (hx : m.toList.Perm xs) (hy : m.toList.Perm ys)
  rw [ofList_eq_ofList_iff]
  rotate_left
  · exact range'_aux hm hx
  · exact range'_aux hm hy
  apply List.filterMap_perm_filterMap_of
  trans m.toList
  · exact hx.symm
  · exact hy

def range [ha : Fintype α] (f : (i : α) → β i) : Std.ExtDHashMap α β := by
  apply ha.1.1.liftWith # λ xs => ofList # xs.map # λ i => ⟨i, f i⟩
  rcases ha with ⟨⟨m, hm⟩, ha⟩
  replace hm : m.toList.Nodup := by simpa
  intro xs ys (hx : m.toList.Perm xs) (hy : m.toList.Perm ys)
  rw [ofList_eq_ofList_iff]
  rotate_left
  · simp; exact hx.nodup hm
  · simp; exact hy.nodup hm
  rw [List.map_perm_map_iff]
  · exact hx.symm.trans hy
  intro x y h
  simp at h
  exact h.1

@[simp]
theorem mem_range [ha : Fintype α] {f : (i : α) → β i} {i : α} : i ∈ range f := by
  simp [range]

@[simp]
theorem mem_range' [ha : Fintype α] {f : (i : α) → Option (β i)} {i : α} :
i ∈ range' f ↔ ∃ x, f i = some x := by
  simp [range']; aesop

@[simp]
theorem nonempty_insert {x} : Insert.insert x mp ≠ ⟨⟦∅⟧⟩ := by
  apply ne_of_congr (x.1 ∈ ·); simp

@[simp]
theorem nodup_toList [LinearOrder α] : mp.toList.Nodup := by
  rcases mp with ⟨mp⟩
  apply mp.ind; intro mp
  exact Std.DHashMap.nodup_toSortedList

@[simp]
theorem sorted_toList [LinearOrder α] : mp.toList.Sorted (·.1 ≤ ·.1) := by
  rcases mp with ⟨mp⟩
  apply mp.ind; simp [toList, lift]

@[simp]
theorem mem_toList {x} [LinearOrder α] : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  rcases mp with ⟨mp⟩
  unfold toList get? lift
  apply mp.ind
  clear mp; intro mp
  rcases x with ⟨i, x⟩
  simp [Std.DHashMap.toSortedList]

@[simp]
theorem toList_eq_toList [LinearOrder α] {m₁ m₂ : Std.ExtDHashMap α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  refine' ⟨λ h => _, λ h => by rw [h]⟩
  rw [List.eq_iff_of_nodup_and_sorted (·.1 ≤ ·.1)] at h
  any_goals simp
  rotate_left
  · rintro ⟨i, x⟩ ⟨j, y⟩
    simp
    intro h₁ h₂ h₃ h₄
    have h₅ := le_antisymm h₃ h₄
    subst h₅
    use rfl
    simp [h₁] at h₂
    simpa
  rw [ext_iff]
  intro i
  ext x
  specialize h ⟨i, x⟩
  simp at h
  exact h

@[simp]
theorem toList_eq_nil_iff [LinearOrder α] : mp.toList = [] ↔ mp = ∅ := by
  rw [←toList_empty, toList_eq_toList]

theorem eq_iff_inner_eq {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ m₁.1 = m₂.1 := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp

theorem inner_eq_iff_eq {m₁ m₂ : Std.ExtDHashMap α β} :
m₁.1 = m₂.1 ↔ m₁ = m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp

def fold {γ : Type*} (mp : Std.ExtDHashMap α β) (f : γ → (i : α) → β i → γ) (z : γ)
(h_assoc : ∀ {acc i x j y}, f (f acc i x) j y = f (f acc j y) i x) : γ :=
  mp.lift (·.fold f z) # λ _ _ => DHashMap.fold_eq_fold_of_equiv @h_assoc

def decideEq [hh : ∀ i, DecidableEq # β i]
(m₁ m₂ : Std.ExtDHashMap α β) : Bool := by
  classical
  rcases m₁ with ⟨m₁⟩
  rcases m₂ with ⟨m₂⟩
  apply m₁.liftOn₂ m₂ Std.DHashMap.decideEquiv
  clear m₁ m₂
  intro a₁ b₁ a₂ b₂ ha hb
  simp
  change a₁.Equiv a₂ at ha
  change b₁.Equiv b₂ at hb
  constructor <;> intro h
  · trans a₁; exact ha.symm
    trans b₁ <;> assumption
  · trans a₂; exact ha
    trans b₂; exact h
    exact hb.symm

theorem eq_iff_decideEq [hh : ∀ i, DecidableEq # β i]
{m₁ m₂ : Std.ExtDHashMap α β} : m₁ = m₂ ↔ m₁.decideEq m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
  simp [decideEq]
  induction m₁, m₂ using Quotient.inductionOn₂
  simp; rfl

instance [hh : ∀ i, DecidableEq # β i] :
DecidableEq (Std.ExtDHashMap α β) :=
  λ m₁ m₂ => match h : m₁.decideEq m₂ with
  | true => isTrue # by rwa [eq_iff_decideEq]
  | false => isFalse # by simpa [eq_iff_decideEq]

@[simp]
theorem decideEq_eq [hh : ∀ i, DecidableEq # β i]
{m₁ m₂ : Std.ExtDHashMap α β} : m₁.decideEq m₂ = decide (m₁ = m₂) := by
  simp [eq_iff_decideEq]

def all (mp : ExtDHashMap α β) (p : (i : α) → β i → Bool) : Bool :=
  mp.inner.lift (·.all p) # by
    intro m₁ m₂ (h : m₁.Equiv m₂); simp
    rw [Std.DHashMap.equiv_iff_get?] at h
    simp [h]

@[simp]
theorem all_def {p} [LinearOrder α] : mp.all p = decide (∀ x ∈ mp.toList, p x.1 x.2) := by
  rcases mp with ⟨mp⟩; apply mp.ind; simp [all, get?, lift]

def keys [LinearOrder α] (mp : Std.ExtDHashMap α β) : List α :=
  mp.lift Std.DHashMap.toSortedKeys # λ m₁ _ =>
    m₁.toSortedKeys_eq_of_equiv

@[simp]
theorem mem_keys [LinearOrder α] {i} : i ∈ mp.keys ↔ i ∈ mp := by
  rcases mp with ⟨mp⟩
  apply mp.ind; intro mp
  simp [keys, lift]; rfl

def modifyMany (mp : ExtDHashMap α β)
(xs : List ((i : α) × (β i → β i))) : ExtDHashMap α β :=
  mk' # mp.1.map (·.modifyMany xs) # λ a _ =>
    a.modifyMany_equiv_modifyMany_of_equiv

@[simp]
theorem modifyMany_nil : mp.modifyMany [] = mp := by
  rcases mp with ⟨mp⟩; apply mp.ind; simp [modifyMany]

@[simp]
theorem modifyMany_cons {i x xs} :
mp.modifyMany (⟨i, x⟩ :: xs) = (mp.modify i x).modifyMany xs := by
  rcases mp with ⟨mp⟩; apply mp.ind; intro mp; rfl

theorem get!_eq_get? {i} [hb : Inhabited (β i)] :
mp.get! i = (mp.get? i).get! := by
  rcases mp with ⟨mp⟩; apply mp.ind; intro mp
  simp [get!, get?, lift]; exact mp.get!_eq_get!_get?

theorem get?_eq_ite {i} [hb : Inhabited # β i] :
mp.get? i = if i ∈ mp then some # mp.get! i else none := by
  rw [get!_eq_get!_get?]
  split_ifs with h₁ <;> simp [mem_iff_get?_eq_some] at h₁
  · obtain ⟨x, h₁⟩ := h₁; simp [h₁]
  · rw [Option.eq_none_iff_forall_ne_some.mpr h₁]

theorem get?_ofList_eq_some_iff {xs : List ((i : α) × β i)} {i x}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get? i = some x ↔ ⟨i, x⟩ ∈ xs :=
  Std.DHashMap.get?_ofList_eq_some_iff h

@[simp]
theorem get?_range [ha : Fintype α] {f : (i : α) → β i} {i} :
(range f).get? i = some (f i) := by
  simp [range]
  rw [get?_ofList_eq_some_iff # by simp]
  simp

@[simp]
theorem get?_range' [ha : Fintype α] {f : (i : α) → Option (β i)} {i} :
(range' f).get? i = f i := by
  simp [range']
  ext x
  rw [get?_ofList_eq_some_iff]
  rotate_left
  · clear i x
    simp [List.map_filterMap]
    rw [List.nodup_filterMap_iff]
    simp
    rintro x y h₁ x' y' h₂ rfl; rfl
  simp; aesop

theorem injective_range [ha : Fintype α] :
Function.Injective (Std.ExtDHashMap.range (α := α) (β := β)) := by
  intro f g h
  ext i
  rw [ext_iff] at h
  specialize h i
  simp at h
  exact h

theorem injective_range' [ha : Fintype α] :
Function.Injective (Std.ExtDHashMap.range' (α := α) (β := β)) := by
  intro f g h
  ext i
  rw [ext_iff] at h
  specialize h i
  simp at h
  simp [h]

instance [ha : Fintype α] [hb : ∀ i, Fintype (β i)] : Fintype (Std.ExtDHashMap α β) := by
  have hf : Fintype # (i : α) → Option (β i) := inferInstance
  refine' ⟨hf.1.map ⟨_, injective_range'⟩, _⟩
  intro m
  simp
  use m.get?
  ext x y
  simp

instance [ha : Finite α] [hb : ∀ i, Finite (β i)] : Finite (Std.ExtDHashMap α β) := by
  apply Fintype.finite
  replace ha := @Fintype.ofFinite _ ha
  replace hb := λ i => @Fintype.ofFinite _ # hb i
  infer_instance

@[simp]
theorem range_eq_range_iff [ha : Fintype α] {f g : (i : α) → β i} :
range f = range g ↔ ∀ x, f x = g x :=
  ⟨λ h => by simp [injective_range h], λ h => by congr; ext; apply h⟩

@[simp]
theorem range'_eq_range'_iff [ha : Fintype α] {f g : (i : α) → Option (β i)} :
range' f = range' g ↔ ∀ x, f x = g x :=
  ⟨λ h => by simp [injective_range' h], λ h => by congr; ext:1; apply h⟩

theorem mem_of_get?_eq_some {i x} (h : mp.get? i = some x) : i ∈ mp := by
  simp [mem_iff_get?_eq_some, h]

@[simp]
theorem get?_eq_some_get!_iff {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get! i) ↔ i ∈ mp := by
  simp [get?_eq_ite]

@[simp]
theorem get?_eq_some_get?_get! {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get? i).get! ↔ i ∈ mp := by
  simp [←get!_eq_get!_get?]

theorem fold_eq_foldl_toList [ha : LinearOrder α] {γ : Type*}
{z : γ} {f : γ → (i : α) → β i → γ} {h_assoc} : mp.fold f z h_assoc =
mp.toList.foldl (λ acc (x : (i : α) × β i) => f acc x.1 x.2) z := by
  rcases mp with ⟨mp⟩
  simp [fold, lift, toList]
  apply mp.ind
  intro m
  simp only [Quotient.lift_mk]
  rw [Std.DHashMap.fold_eq_foldl_toList]
  apply List.foldl_eq_foldl_of_perm h_assoc
  simp

theorem eq_iff_toList_eq [ha : LinearOrder α] {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ m₁.toList = m₂.toList := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

@[simp]
theorem ofList_toList [ha : LinearOrder α] : ofList mp.toList = mp := by
  rcases mp with ⟨mp⟩
  rw [eq_iff_inner_eq]
  apply mp.ind
  intro m
  simp
  apply Quotient.eq_iff_equiv.mpr
  exact DHashMap.ofList_toSortedList_equiv

theorem toList_ofList_perm [ha : LinearOrder α] {xs : List ((i : α) × β i)}
(h : xs.map (·.1) |>.Nodup) : (ofList xs).toList.Perm xs := by
  trans (DHashMap.ofList xs).toList
  rotate_left; exact DHashMap.toList_ofList_perm h
  simp [ofList, toList, lift]

@[simp]
theorem sorted_keys [ha : LinearOrder α] : mp.keys.Sorted (· ≤ ·) := by
  rcases mp with ⟨mp⟩; apply mp.ind; intro m; simp [keys, lift]

theorem keys_eq_map_fst_toList [ha : LinearOrder α] : mp.keys = mp.toList.map (·.1) := by
  unfold keys toList lift Std.DHashMap.toSortedKeys
  symm; apply Quotient.apply_lift

-----

def minKey? [ha : LinearOrder α] (mp : Std.ExtDHashMap α β) : Option α :=
  mp.fold (λ acc i _ => some # acc.elim i # λ acc => min acc i) none # by
    rintro (_ | acc) i x j y <;> simp; apply min_comm; apply inf_right_comm

def maxKey? [ha : LinearOrder α] (mp : Std.ExtDHashMap α β) : Option α :=
  mp.fold (λ acc i _ => some # acc.elim i # λ acc => max acc i) none # by
    rintro (_ | acc) i x j y <;> simp; apply max_comm; apply sup_right_comm

def minKey! [Inhabited α] [ha : LinearOrder α] (mp : Std.ExtDHashMap α β) : α :=
  mp.minKey?.get!

def maxKey! [Inhabited α] [ha : LinearOrder α] (mp : Std.ExtDHashMap α β) : α :=
  mp.maxKey?.get!

theorem minKey?_eq_head?_keys [ha : LinearOrder α] : mp.minKey? = mp.keys.head? := by
  rw [minKey?, fold_eq_foldl_toList]
  convert @mp.keys.min?_eq_head? α _ _
  rotate_left; simp_rw [min_eq_left_iff]; exact sorted_keys
  rw [keys_eq_map_fst_toList]
  generalize hx : mp.toList = xs
  cases xs; rfl
  nm x xs
  trans xs.map (·.1) |>.foldl
    (λ acc i => some # acc.elim i # λ acc => min acc i) (some x.1)
  rotate_left; simp [List.min?_eq_foldl, List.foldl_map]
  simp [List.foldl_map]

theorem maxKey?_eq_getLast?_keys [ha : LinearOrder α] : mp.maxKey? = mp.keys.getLast? := by
  rw [maxKey?, fold_eq_foldl_toList]
  convert @mp.keys.max?_eq_getLast? α _ _
  rotate_left; exact sorted_keys
  rw [keys_eq_map_fst_toList]
  generalize hx : mp.toList = xs
  cases xs; rfl
  nm x xs
  trans xs.map (·.1) |>.foldl
    (λ acc i => some # acc.elim i # λ acc => max acc i) (some x.1)
  rotate_left; simp [List.max?_eq_foldl, List.foldl_map]
  simp [List.foldl_map]

@[simp]
theorem minKey?_eq_none_iff [ha : LinearOrder α] : mp.minKey? = none ↔ mp = ∅ := by
  rw [ext_iff]; simp
  simp_rw [minKey?_eq_head?_keys, ←mem_keys]
  cases h₁ : mp.keys <;> simp
  nm i ks; use i; simp

@[simp]
theorem maxKey?_eq_none_iff [ha : LinearOrder α] : mp.maxKey? = none ↔ mp = ∅ := by
  rw [ext_iff]; simp
  simp_rw [maxKey?_eq_getLast?_keys, ←mem_keys]
  cases h₁ : mp.keys <;> simp
  nm i ks; use i; simp

theorem not_mem_of_lt_minKey? [ha : LinearOrder α] {m x}
(h₁ : mp.minKey? = some m) (h₂ : x < m) : x ∉ mp := by
  rw [minKey?_eq_head?_keys] at h₁
  rw [←mem_keys]
  have h₃ := mp.sorted_keys
  intro h₄
  generalize mp.keys = ks at h₁ h₃ h₄
  cases ks
  · simp at h₁
  nm i ks
  simp at h₁ h₃ h₄
  subst h₁
  rcases h₃ with ⟨h₃, h₅⟩
  rcases h₄ with rfl | h₄
  · simp at h₂
  specialize h₃ x h₄
  contrapose! h₂
  exact h₃

theorem not_mem_of_maxKey?_lt [ha : LinearOrder α] {m x}
(h₁ : mp.maxKey? = some m) (h₂ : m < x) : x ∉ mp := by
  rw [maxKey?_eq_getLast?_keys] at h₁
  rw [←mem_keys]
  have h₃ := mp.sorted_keys
  intro h₄
  generalize mp.keys = ks at h₁ h₃ h₄
  induction ks using List.reverseRecOn
  · simp at h₁
  nm ks i ih; clear ih
  simp at h₁ h₃ h₄
  symm at h₄
  subst h₁
  rcases h₃ with ⟨h₃, h₅⟩
  rcases h₄ with rfl | h₄
  · simp at h₂
  specialize h₅ x h₄
  contrapose! h₂
  exact h₅

theorem not_mem_of_lt_minKey! [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : x < mp.minKey!) : x ∉ mp := by
  unfold minKey! at h
  cases h₁ : mp.minKey?
  · simp at h₁; simp [h₁]
  nm i; simp [h₁] at h
  exact not_mem_of_lt_minKey? h₁ h

theorem not_mem_of_maxKey!_lt [ha₁ : Inhabited α] [ha₂ : LinearOrder α] {x}
(h : mp.maxKey! < x) : x ∉ mp := by
  unfold maxKey! at h
  cases h₁ : mp.maxKey?
  · simp at h₁; simp [h₁]
  nm i; simp [h₁] at h
  exact not_mem_of_maxKey?_lt h₁ h

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

@[simp]
theorem keys_eq_nil_iff [LinearOrder α] : mp.keys = [] ↔ mp.isEmpty := by
  rw [keys_eq_map_fst_toList, List.map_eq_nil_iff]; simp

theorem keys_empty [LinearOrder α] : (∅ : ExtDHashMap α β).keys = [] := by
  simp

theorem ind {p : ExtDHashMap α β → Prop} (h₁ : p ∅)
(h₂ : ∀ (mp : ExtDHashMap α β) i x, p mp → i ∉ mp → p (mp.insert i x)) mp : p mp := by
  rcases mp with ⟨mp⟩
  apply mp.ind; clear! mp; intro mp
  induction mp using DHashMap.ind
  · nm mp h₃
    specialize h₁
    convert h₁
    change _ = ⟦∅⟧
    simp
    change mp.Equiv ∅
    simpa
  nm mp₁ mp₂ i x ih h₃ h₄
  specialize h₂ ⟨Quotient.mk _ mp₁⟩ i x ih h₃
  convert h₂
  change _ = ⟦_⟧
  simp
  change mp₂.Equiv _
  rw [DHashMap.equiv_iff_mem_toList] at h₄ ⊢
  simp
  rintro ⟨j, y⟩
  specialize h₄ ⟨j, y⟩
  simp at h₄
  exact h₄.symm

@[simp]
theorem fold_empty {γ : Type*} {f : γ → (i : α) → β i → γ} {z : γ} {h} :
(∅ : ExtDHashMap α β).fold f z h = z := by
  simp [fold, lift]; change (Quotient.mk _ ∅).lift _ _ = _; simp

theorem fold_insert {γ : Type*} {f : γ → (i : α) → β i → γ} {z : γ} {h i x}
(h₁ : i ∉ mp) : (mp.insert i x).fold f z h = mp.fold f (f z i x) h := by
  rcases mp with ⟨mp⟩
  change ExtDHashMap.lift _ _ _ ≠ _ at h₁
  simp [lift] at h₁
  revert h₁
  apply mp.ind; clear! mp
  intro mp h₁
  simp at h₁
  replace h₁ : i ∉ mp
  · change mp.contains i ≠ _
    simpa only [ne_eq, Bool.not_eq_true]
  simp [fold, lift, DHashMap.fold_eq_foldl_toList, insert]
  trans (⟨i, x⟩ :: mp.toList).foldl (λ a b => f a b.1 b.2) z
  rotate_left; rfl
  apply List.foldl_eq_foldl_of_perm h
  exact DHashMap.toList_insert_perm_cons_of_not_mem h₁