import Projects.Util.List.Part_001
import Projects.Util.List.BirdWadler

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

@[simp]
theorem sequence_singleton : sequence [xs] = xs.map ([·]) := by
  simp [sequence_cons]

@[simp]
theorem combinations_one : xs.combinations 1 = xs.map ([·]) := by
  simp [combinations]

theorem combinations_succ {n} : xs.combinations (n + 1) =
xs.flatMap (λ x => xs.combinations n |>.map (x :: ·)) := by
  simp [combinations, replicate_succ, sequence_cons]

@[simp]
theorem length_combinations {n} : (xs.combinations n).length = xs.length ^ n := by
  induction n
  · simp
  nm n ih
  rw [combinations_succ]
  simp [ih, pow_succ']

@[simp]
theorem mem_combinations {n} : ys ∈ xs.combinations n ↔ ys.length = n ∧ ys ⊆ xs := by
  induction n generalizing xs ys
  · simp
    rintro rfl; simp
  nm n ih
  simp [combinations_succ, ih]; clear ih
  constructor
  · rintro ⟨x, hx, ys, ⟨h₁, h₂⟩, rfl⟩
    simp; tauto
  · rintro ⟨h₁, h₂⟩
    cases ys <;> simp at h₁
    nm y ys
    simp at h₂
    choose hy h₂ using h₂
    use y, hy, ys

section

variable [ha : LinearOrder α]
include ha

@[simp]
theorem sortedLe_cons {x} : (x :: xs).SortedLE ↔ (∀ y ∈ xs, x ≤ y) ∧ xs.SortedLE := by
  simp [sortedLE_iff_pairwise]

@[simp]
theorem sortedLt_cons {x} : (x :: xs).SortedLT ↔ (∀ y ∈ xs, x < y) ∧ xs.SortedLT := by
  simp [sortedLT_iff_pairwise]

@[simp]
theorem sortedLe_snoc {x} : (xs ++ [x]).SortedLE ↔ xs.SortedLE ∧ ∀ y ∈ xs, y ≤ x := by
  simp [sortedLE_iff_pairwise]

@[simp]
theorem sortedLT_snoc {x} : (xs ++ [x]).SortedLT ↔ xs.SortedLT ∧ ∀ y ∈ xs, y < x := by
  simp [sortedLT_iff_pairwise]

@[grind =]
theorem sortedLE_append : (xs ++ ys).SortedLE ↔
xs.SortedLE ∧ ys.SortedLE ∧ ∀ x ∈ xs, ∀ y ∈ ys, x ≤ y := by
  simp [sortedLE_iff_pairwise, pairwise_append]

@[grind =]
theorem sortedLT_append : (xs ++ ys).SortedLT ↔
xs.SortedLT ∧ ys.SortedLT ∧ ∀ x ∈ xs, ∀ y ∈ ys, x < y := by
  simp [sortedLT_iff_pairwise, pairwise_append]

end

theorem head!_eq_getd_head [ha : Inhabited α] : xs.head! = xs.head?.getd := by
  cases xs <;> rfl

@[simp]
theorem head!_mem_iff [ha : Inhabited α] : xs.head! ∈ xs ↔ xs ≠ [] := by
  cases xs <;> simp

theorem head!_mem [ha : Inhabited α] (h : xs ≠ []) : xs.head! ∈ xs := by
  simpa

theorem map_init {f : α → β} : xs.init.map f = (xs.map f).init := by
  induction xs using List.reverseRecOn <;> simp_all

theorem init_map {f : α → β} : (xs.map f).init = xs.init.map f :=
  map_init.symm

theorem tail_map {f : α → β} : (xs.map f).tail = xs.tail.map f :=
  map_tail.symm

theorem tail_init : xs.init.tail = xs.tail.init := by
  rcases xs with _ | ⟨x, _ | _⟩ <;> simp

theorem init_tail : xs.tail.init = xs.init.tail :=
  tail_init.symm

attribute [instance high] instLE
attribute [simp] cons_lt_cons_iff cons_le_cons_iff

@[simp]
theorem append_lt_append_iff_right [ha : LinearOrder α] :
xs ++ ys < xs ++ zs ↔ ys < zs := by
  induction xs; simp; simpa

@[simp]
theorem append_le_append_iff_right [ha : LinearOrder α] :
xs ++ ys ≤ xs ++ zs ↔ ys ≤ zs := by
  induction xs; simp; simpa

attribute [-simp] getElem!_eq_getElem?_getD

theorem ext_getd [ha : Inhabited α] : xs = ys ↔ xs.length = ys.length ∧
∀ ⦃i⦄, i < xs.length → i < ys.length → xs[i]?.getd = ys[i]?.getd := by
  constructor; rintro rfl; simp; rintro ⟨h₁, h₂⟩
  rw [List.ext_getElem?_iff]; intro i
  by_cases h₃ : xs.length ≤ i; grind
  specialize @h₂ i (by omega) (by omega)
  iterate 2 rw [List.getElem?_eq_getElem # by grind] at h₂ ⊢
  simp at h₂ ⊢; exact h₂

theorem ext_getElem!_iff [ha : Inhabited α] : xs = ys ↔ xs.length = ys.length ∧
∀ ⦃i⦄, i < xs.length → i < ys.length → xs[i]! = ys[i]! := by
  constructor; rintro rfl; simp; rintro ⟨h₁, h₂⟩
  rw [List.ext_getElem?_iff]; intro i
  by_cases h₃ : xs.length ≤ i; grind
  specialize @h₂ i (by omega) (by omega)
  iterate 2 rw [List.getElem!_eq_getElem # by grind] at h₂
  iterate 2 rw [List.getElem?_eq_getElem # by grind]
  simp at h₂ ⊢; exact h₂

@[simp]
theorem getElem!_eq_getElem_simp [ha : Inhabited α] {i}
{h : i < xs.length} : xs[i]! = xs[i] ↔ True := by
  simp [getElem!_eq_getElem h]

@[simp]
theorem getElem_eq_getElem!_simp [ha : Inhabited α] {i}
{h : i < xs.length} : xs[i] = xs[i]! ↔ True := by
  simp [getElem!_eq_getElem h]

@[simp]
theorem mapWith_append {f : (x : α) → x ∈ xs ++ ys → β} : (xs ++ ys).mapWith f =
xs.mapWith (λ x h => f x # by grind) ++ ys.mapWith (λ x h => f x # by grind) := by
  induction xs generalizing ys; simp; rfl; nm x xs ih; simp [ih]

theorem eq_mapWith_getElem_range' :
xs = (range xs.length).mapWith λ i h => xs[i]'(by grind) := by
  induction xs using List.reverseRecOn; rfl; nm xs x ih; rw! [length_append]
  simp; rw! [range_succ]; simp; convert ih using 2; grind

theorem eq_mapWith_getElem_range {n} (h : xs.length = n) :
xs = (range n).mapWith λ i h => xs[i]'(by grind) := by
  convert xs.eq_mapWith_getElem_range'; exact h.symm

attribute [simp] map_fst_zip map_snd_zip

theorem length_le_sum_of [ha₁ : LinearOrder α] [ha₂ : Semiring α] [ha₃ : AddLeftMono α]
(h : ∀ x ∈ xs, 1 ≤ x) : xs.length ≤ xs.sum := by
  induction xs; simp
  clear! xs
  nm x xs ih
  simp
  specialize ih (by grind)
  specialize h x (by simp)
  nth_rw 2 [add_comm]
  apply add_le_add ih h

theorem length_lt_sum_of [ha₁ : LinearOrder α] [ha₂ : Semiring α]
[ha₃ : AddLeftMono α] [ha₃ : AddLeftStrictMono α]
(h₁ : ∀ x ∈ xs, 1 ≤ x) (h₂ : ∃ x ∈ xs, 1 < x) : xs.length < xs.sum := by
  induction xs; simp_all
  clear! xs
  nm x xs ih
  simp
  specialize ih (by grind)
  nth_rw 2 [add_comm]
  choose y h₂ using h₂
  simp at h₂
  rcases h₂ with ⟨rfl | h₂, h₃⟩
  · have h₄ : xs.length ≤ xs.sum
    · apply length_le_sum_of
      grind
    exact add_lt_add_of_le_of_lt h₄ h₃
  specialize ih ⟨y, by grind⟩
  specialize h₁ x (by simp)
  exact add_lt_add_of_lt_of_le ih h₁

theorem mem_zip_iff {ys : List β} {xy} : xy ∈ xs.zip ys ↔ ∃ (i : ℕ) (h₁ : i < xs.length)
(h₂ : i < ys.length), xs[i] = xy.1 ∧ ys[i] = xy.2 := by
  induction xs generalizing ys <;> simp
  nm x xs ih; cases ys <;> simp
  rw [ih]; clear ih; simp
  constructor; on_goal 2 => grind
  rintro (rfl | h); use 0; simp; tauto

@[simp]
theorem mem_zip_range_length_iff {xy} : xy ∈ xs.zip (.range xs.length) ↔
∃ (h : xy.2 < xs.length), xs[xy.2] = xy.1 := by
  grind [mem_zip_iff]

theorem take_eq_take_of_prefix {n} (h₁ : xs <+: ys)
(h₂ : n ≤ xs.length) : xs.take n = ys.take n := by
  induction xs generalizing ys n
  · simp at h₂; simp [h₂]
  nm x xs ih
  cases ys; grind
  nm y ys
  simp at *
  rcases h₁ with ⟨rfl, h₁⟩
  cases n; rfl; grind

theorem sum_le_of_prefix {xs ys: List ℕ} (h : xs <+: ys) : xs.sum ≤ ys.sum := by
  obtain ⟨ys, rfl⟩ := h; simp

theorem sum_lt_of_prefix {xs ys: List ℕ} (h₁ : xs <+: ys) (h₂ : xs.length ≠ ys.length)
(h₃ : ∃ n ∈ ys.drop xs.length, n ≠ 0) : xs.sum < ys.sum := by
  obtain ⟨ys, rfl⟩ := h₁; simp
  obtain ⟨n, hn, h₃⟩ := h₃
  simp at hn
  simp [Nat.pos_iff_ne_zero]
  rw [sum_eq_zero_iff]
  grind

theorem le_max_of_le_mem [ha : LinearOrder α] {x}
(h : ∃ y ∈ xs, x ≤ y) : x ≤ xs.max (by grind) := by
  obtain ⟨y, h₁, h₂⟩ := h; exact h₂.trans # le_max_of_mem h₁

theorem foldl_eq_foldlWith' [ha : DecidableEq α] {f : β → α → β} {z} :
xs.foldl f z = xs.foldlWith (λ acc x _ => f acc x) z := by
  rw [foldlWith_eq_foldl]
  simp
  rw [←foldl_attach]
  nth_rw 2 [←foldl_attach]
  congr
  grind

theorem foldl_eq_foldlWith : foldl = λ (f : β → α → β) z (xs : List α) =>
xs.foldlWith (z := z) (λ acc x _ => f acc x) := by
  classical funext; rw [foldl_eq_foldlWith']

theorem foldl_dite_mem_apply' [ha : DecidableEq α]
{f : (x : α) → x ∈ xs → β} {g : γ → α → β → γ} {z} (z' : β) :
xs.foldl (λ acc x => if h : x ∈ xs then g acc x (f x h) else z) =
xs.foldl (λ acc x => g acc x # if h : x ∈ xs then f x h else z') := by
  simp_rw [foldl_eq_foldlWith]; grind

theorem foldl_dite_mem_apply [ha : DecidableEq α]
{f : (x : α) → x ∈ xs → β} {g : γ → α → β → γ} {z z₁} (z' : β) :
xs.foldl (λ acc x => if h : x ∈ xs then g acc x (f x h) else z) z₁ =
xs.foldl (λ acc x => g acc x # if h : x ∈ xs then f x h else z') z₁ :=
  congrArg (· z₁) # foldl_dite_mem_apply' z'

theorem mapWith_eq_map_attach {f : (x : α) → x ∈ xs → β} :
xs.mapWith f = xs.attach.map λ x => f x.1 x.2 := by
  induction xs <;> simp; grind

theorem le_foldl_dite_max [ha : DecidableEq α] [hb : LinearOrder β]
{f : (x : α) → x ∈ xs → β} {x z z₁} (h : x ∈ xs) : f x h ≤ xs.foldl (init := z₁)
λ acc x => if h : x ∈ xs then max acc (f x h) else z := by
  rw [@xs.foldl_dite_mem_apply α β β _  f (λ acc _ x => max acc x) z z₁ z]
  rw [foldl_eq_foldlWith]
  dsimp
  rw [foldlWith_max_eq_max?_mapWith]
  rw [mapWith_eq_map_attach]
  rw [max?_eq_some_max]
  rotate_left
  · simp
    grind
  simp
  right
  apply le_max_of_mem
  simp
  grind

theorem flatMap_eq_flatten_map {f : α → List β} : xs.flatMap f = (xs.map f).flatten := by
  exact flatMap_def

theorem foldr_fn_append_eq_flatMap {f : α → List β} {zs} :
xs.foldr (λ x acc => f x ++ acc) zs = xs.flatMap f ++ zs := by
  cases xs <;> simp; rfl

theorem map_eq_map_attach {f : α → β} : xs.map f = xs.attach.map (λ x => f x.1) := by
  simp

@[simp]
theorem getElem?_singleton_eq_some_iff {x y : α} {i} : [x][i]? = some y ↔ i = 0 ∧ x = y := by
  grind

theorem foldr_eq_foldl' {f : α → α → α} {z}
[Std.Associative f] [Std.LawfulIdentity f z] : xs.foldr f z = xs.foldl f z :=
  foldr_eq_foldl

theorem foldr_eq_foldr_map {f : α → β → β} {z} (g₁ : α → β) (g₂ : β → β → β)
(h : ∀ ⦃x acc⦄, f x acc = g₂ (g₁ x) acc) : xs.foldr f z = (xs.map g₁).foldr g₂ z := by
  rw [foldr_map, funext₂ @h]

theorem foldl_eq_foldl_map {f : β → α → β} {z} (g₁ : α → β) (g₂ : β → β → β)
(h : ∀ ⦃acc x⦄, f acc x = g₂ acc (g₁ x)) : xs.foldl f z = (xs.map g₁).foldl g₂ z := by
  rw [foldl_map, funext₂ @h]

@[simp] theorem min!_nil [Top α] [Min α] : ([] : List α).min! = ⊤ := rfl
@[simp] theorem max!_nil [Bot α] [Max α] : ([] : List α).max! = ⊥ := rfl

@[simp]
theorem min!_cons [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] {x} :
(x :: xs).min! = min x xs.min! := by
  simp [min!, min?]; cases xs <;> simp; exact foldl_assoc

@[simp]
theorem max!_cons [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] {x} :
(x :: xs).max! = max x xs.max! := by
  simp [max!, max?]; cases xs <;> simp; exact foldl_assoc

theorem elim_min?_eq_min! [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] {f : α → α} {z : α} :
xs.min?.elim z f = if xs = [] then z else f xs.min! := by
  cases xs <;> simp; nm x xs; congr; simp [min!, min?]; cases xs <;> simp

theorem elim_max?_eq_max! [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] {f : α → α} {z : α} :
xs.max?.elim z f = if xs = [] then z else f xs.max! := by
  cases xs <;> simp; nm x xs; congr; simp [max!, max?]; cases xs <;> simp

@[simp]
theorem elim_min?_id_eq_min! [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α]
{z : α} : xs.min?.elim z id = haveI := Classical.propDecidable;
if z = ⊤ ∨ xs ≠ [] then xs.min! else z := by
  cases xs <;> simp; nm x xs; simp [min!, min?]; cases xs <;> simp

@[simp]
theorem elim_max?_id_eq_max! [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α]
{z : α} : xs.max?.elim z id = haveI := Classical.propDecidable;
if z = ⊥ ∨ xs ≠ [] then xs.max! else z := by
  cases xs <;> simp; nm x xs; simp [max!, max?]; cases xs <;> simp

@[simp]
theorem min_append [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] :
(xs ++ ys).min! = min xs.min! ys.min! := by
  induction xs generalizing ys <;> simp; grind

@[simp]
theorem max_append [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] :
(xs ++ ys).max! = max xs.max! ys.max! := by
  induction xs generalizing ys <;> simp; grind

theorem min!_eq_min [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] (h : xs ≠ []) :
xs.min! = xs.min (by grind) := by
  induction xs <;> simp; grind; clear! xs; nm x xs ih
  rw [min_cons, elim_min?_eq_min!]; split_ifs with h₁; subst h₁; simp; grind

theorem max!_eq_max [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] (h : xs ≠ []) :
xs.max! = xs.max (by grind) := by
  induction xs <;> simp; grind; clear! xs; nm x xs ih
  rw [max_cons, elim_max?_eq_max!]; split_ifs with h₁; subst h₁; simp; grind

@[simp]
theorem min_cons_cons' [ha₁ : SemilatticeInf α] {x y} :
(x :: y :: xs).min (by simp) = min x ((y :: xs).min (by simp)) := by
  rw [min_cons_cons]; induction xs generalizing x y; simp
  clear! xs; nm k xs ih; simp_rw [min_cons_cons, ih]; grind

@[simp]
theorem max_cons_cons' [ha₁ : SemilatticeSup α] {x y} :
(x :: y :: xs).max (by simp) = max x ((y :: xs).max (by simp)) := by
  rw [max_cons_cons]; induction xs generalizing x y; simp
  clear! xs; nm k xs ih; simp_rw [max_cons_cons, ih]; grind

theorem Perm.min [ha₁ : SemilatticeInf α] {h₁ : xs ≠ []} {h₂ : ys ≠ []}
(h : xs ~ ys) : xs.min h₁ = ys.min h₂ := by
  induction h <;> clear! xs ys; simp
  · nm x xs ys h ih; cases xs; simp at h; simp [h]
    nm x₁ xs; cases ys; simp at h; nm y₁ ys; simp at ih; simp [ih]
  · nm x y xs; rw! [min_cons_cons, show min y x = min x y by grind, ←min_cons_cons]; rfl
  · nm xs ys zs h₃ h₄ ih₁ ih₂; apply ih₁.trans # ih₂.trans rfl; rintro rfl; simp [h₂] at h₄

theorem Perm.max [ha₁ : SemilatticeSup α] {h₁ : xs ≠ []} {h₂ : ys ≠ []}
(h : xs ~ ys) : xs.max h₁ = ys.max h₂ := by
  induction h <;> clear! xs ys; simp
  · nm x xs ys h ih; cases xs; simp at h; simp [h]
    nm x₁ xs; cases ys; simp at h; nm y₁ ys; simp at ih; simp [ih]
  · nm x y xs; rw! [max_cons_cons, show max y x = max x y by grind, ←max_cons_cons]; rfl
  · nm xs ys zs h₃ h₄ ih₁ ih₂; apply ih₁.trans # ih₂.trans rfl; rintro rfl; simp [h₂] at h₄

theorem Perm.min! [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α]
(h : xs ~ ys) : xs.min! = ys.min! := by
  cases xs; simp at h; simp [h]; nm x xs; cases ys; simp at h
  nm y ys; iterate 2 rw [min!_eq_min (by grind)];; exact h.min

theorem Perm.max! [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α]
(h : xs ~ ys) : xs.max! = ys.max! := by
  cases xs; simp at h; simp [h]; nm x xs; cases ys; simp at h
  nm y ys; iterate 2 rw [max!_eq_max (by grind)];; exact h.max

@[simp]
theorem min!_reverse [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] :
xs.reverse.min! = xs.min! := by
  apply Perm.min!; simp

@[simp]
theorem max!_reverse [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] :
xs.reverse.max! = xs.max! := by
  apply Perm.max!; simp

@[simp]
theorem foldr_min_eq_min! [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] {z} :
xs.foldr min z = min z xs.min! := by
  induction xs <;> simp; grind

@[simp]
theorem foldr_max_eq_max! [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] {z} :
xs.foldr max z = max z xs.max! := by
  induction xs <;> simp; grind

@[simp]
theorem foldl_min_eq_min! [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] {z} :
xs.foldl min z = min z xs.min! := by
  rw [←foldr_reverse, ←min!_reverse, min_comm!, foldr_min_eq_min!]; grind

@[simp]
theorem foldl_max_eq_max! [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] {z} :
xs.foldl max z = max z xs.max! := by
  rw [←foldr_reverse, ←max!_reverse, max_comm!, foldr_max_eq_max!]; grind

theorem min!_flatten [ha₁ : SemilatticeInf α] [ha₂ : OrderTop α] {L : List (List α)} :
L.flatten.min! = (L.map min!).min! := by
  induction L <;> simp; grind

theorem max!_flatten [ha₁ : SemilatticeSup α] [ha₂ : OrderBot α] {L : List (List α)} :
L.flatten.max! = (L.map max!).max! := by
  induction L <;> simp; grind

theorem min!_flatMap [hb₁ : SemilatticeInf β] [hb₂ : OrderTop β] {f : α → List β} :
(xs.flatMap f).min! = (xs.map λ x => f x |>.min!).min! := by
  rw [flatMap, min!_flatten, map_map]; rfl

theorem max!_flatMap [hb₁ : SemilatticeSup β] [hb₂ : OrderBot β] {f : α → List β} :
(xs.flatMap f).max! = (xs.map λ x => f x |>.max!).max! := by
  rw [flatMap, max!_flatten, map_map]; rfl

theorem range_add' {n m : Nat} : range (n + m) = range m ++ (range n).map (m + ·) := by
  rw [add_comm, range_add]

theorem range_succ' {n : ℕ} : range (n + 1) = 0 :: (range n).map (· + 1) := by
  rw [range_add']; simp; omega

@[simp]
theorem map_getElem!_range_length [ha : Inhabited α] :
(range xs.length).map (xs[·]!) = xs := by
  apply ext_getElem <;> simp

theorem map_getElem!_range_of_le_length [ha : Inhabited α] {n : ℕ}
(h : n ≤ xs.length) : (range n).map (xs[·]!) = xs.take n := by
  apply ext_getElem <;> simp; omega

theorem map_getElem!_range_of_length_le [ha : Inhabited α] {n : ℕ}
(h : xs.length ≤ n) : (range n).map (xs[·]!) = xs ++ replicate (n - xs.length) default := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; simp [range_add]

theorem map_getElem!_range [ha : Inhabited α] {n : ℕ} :
(range n).map (xs[·]!) = xs.take n ++ replicate (n - xs.length) default := by
  by_cases h : n ≤ xs.length
  · simp [Nat.sub_eq_zero_of_le h, map_getElem!_range_of_le_length h]
  · rw [map_getElem!_range_of_length_le # by omega]; simp; omega

theorem foldr_apply {f : α → β → β} {z : β}
(g₁ : β → γ) (g₂ : γ → β) (h : ∀ ⦃x⦄, g₂ (g₁ x) = x) :
xs.foldr f z = g₂ (xs.foldr (λ x acc => g₁ # f x # g₂ acc) (g₁ z)) := by
  induction xs <;> grind

theorem foldl_apply {f : β → α → β} {z : β}
(g₁ : β → γ) (g₂ : γ → β) (h : ∀ ⦃x⦄, g₂ (g₁ x) = x) :
xs.foldl f z = g₂ (xs.foldl (λ acc x => g₁ # f (g₂ acc) x) (g₁ z)) := by
  simp_rw [foldl_eq_foldr_reverse, foldr_apply _ _ h]

@[simp]
theorem take_take_same {n : ℕ} : (xs.take n).take n = xs.take n := by
  rw [take_take]; simp