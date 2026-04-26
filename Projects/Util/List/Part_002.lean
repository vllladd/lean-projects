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