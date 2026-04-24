import Projects.Util.List.Defs

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

theorem init_cons_of_ne_nil {α : Type*} {x : α} {xs : List α}
(h : xs ≠ []) : (x :: xs).init = x :: xs.init := by
  cases xs; simp at h; rfl

@[simp]
theorem init_snoc {x : α} : (xs ++ [x]).init = xs := by
  induction xs; rfl
  nm y xs ih
  rw [List.cons_append, init_cons_of_ne_nil # by simp, ih]

@[simp]
theorem snoc_inj {α : Type*} {xs ys : List α} {x y : α} :
xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
  symm; constructor; rintro ⟨rfl, rfl⟩; rfl
  intro h
  replace h := congrArg reverse h
  simp at h
  exact h.symm

@[simp]
theorem not_mem_failure {α : Type*} {x : α} : x ∉ (failure : List α) := by
  classical exact List.count_eq_zero.mp rfl

@[simp]
theorem unit_mem_guard_iff {P : Prop} [Decidable P] :
() ∈ (guard P : List Unit) ↔ P := by
  by_cases h : P <;> simp [h]

theorem eq_of_prefix_and_length_eq (hx : xs <+: zs) (hy : ys <+: zs)
(hn : xs.length = ys.length) : xs = ys := by
  induction ys generalizing xs zs
  · simp at hn; exact hn
  nm y ys ih
  cases xs
  · simp at hn
  nm x xs
  simp at hn ⊢
  cases zs
  · simp at hx
  nm z zs
  simp at hx hy
  constructor
  · rw [hx.1, hy.1]
  exact ih hx.2 hy.2 hn

theorem eq_of_suffix_and_length_eq (hx : xs <:+ zs) (hy : ys <:+ zs)
(hn : xs.length = ys.length) : xs = ys := by
  suffices : xs.reverse = ys.reverse; simpa
  apply List.eq_of_prefix_and_length_eq (zs := zs.reverse) <;> grind

theorem prefix_of_prefix_snoc_and_ne {α : Type*} {xs ys : List α} {y : α}
(h₁ : xs <+: ys ++ [y]) (h₂ : xs ≠ ys ++ [y]) : xs <+: ys := by
  induction ys generalizing xs y
  · cases xs; rfl
    nm x xs
    simp at h₁ h₂
    tauto
  nm z zs ih
  cases xs
  · simp
  nm x xs
  simp at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₂
  simp
  exact ih h₁ h₂

@[simp]
theorem append_prefix_left_iff {α : Type*} {xs ys : List α} :
xs ++ ys <+: xs ↔ ys = [] := by
  symm
  constructor
  · rintro rfl; simp
  rintro ⟨zs, h⟩
  simp at h
  exact h.1

@[simp]
theorem prefix_snoc_iff {α : Type*} {xs ys : List α} {y : α} :
xs <+: ys ++ [y] ↔ xs <+: ys ∨ xs = ys ++ [y] := by
  induction xs generalizing ys y
  · simp
  nm x xs ih
  cases ys
  · simp
  nm z ys
  simp
  by_cases h : x = z <;> simp [h]
  exact ih

theorem prefix_antisymm {α : Type*} {xs ys : List α}
(h₁ : xs <+: ys) (h₂ : ys <+: xs) : xs = ys := by
  obtain ⟨ys, rfl⟩ := h₁
  obtain ⟨zs, h₂⟩ := h₂
  simp at h₂
  simp [h₂]

theorem take_length_eq_of_prefix {α : Type*} {xs ys : List α}
(h₁ : ys <+: xs) : xs.take ys.length = ys := by
  obtain ⟨xs, rfl⟩ := h₁; simp

@[simp]
theorem nodup_inits : xs.inits.Nodup := by
  induction xs
  · simp
  nm x xs ih
  simp
  rwa [List.nodup_map_iff]
  simp

theorem length_takeWhile_le {α : Type*} {P : α → Bool} {xs : List α} :
(xs.takeWhile P).length ≤ xs.length := by
  induction xs
  · simp
  nm x xs ih
  simp [takeWhile]
  split; simpa; simp

theorem not_apply_of_takeWhile_append_cons_eq_self
{α : Type*} {xs ys : List α} {P : α → Bool} {y}
(h : xs.takeWhile P ++ y :: ys = xs) : P y = false := by
  induction xs using reverseRecOn generalizing y ys
  · simp at h
  nm xs x ih
  rw [takeWhile_append] at h
  split_ifs at h with h₁
  · simp [takeWhile_cons] at h
    split_ifs at h with h₂ <;> simp at h
    simp [←h] at h₂
    exact h₂
  suffices h₂ : xs.takeWhile P ++ [y] <+: xs
    by
      obtain ⟨zs, h₂⟩ := h₂
      simp at h₂
      exact ih h₂
  rw [append_cons] at h
  induction ys using reverseRecOn
  · rw [append_nil, snoc_inj] at h
    simp [h.1] at h₁
  nm ys z x; clear x
  rw [←append_assoc, snoc_inj] at h
  rcases h with ⟨h, rfl⟩
  use ys

theorem exists_takeWhile_eq {α : Type*} (xs : List α) (P : α → Bool) :
∃ k ≤ xs.length, xs.takeWhile P = xs.take k ∧ (∀ x ∈ xs.take k, P x) ∧
((h : k < xs.length) → P xs[k] = false) := by
  use (xs.takeWhile P).length
  use length_takeWhile_le
  use by rw [take_length_eq_of_prefix # takeWhile_prefix _]
  constructor
  · intro x hx
    induction xs using reverseRecOn
    · simp at hx
    nm xs y ih
    rw [takeWhile_append] at hx
    split_ifs at hx with h₁
    · simp [take_append, take_add] at hx
      simp [h₁] at ih
      rcases hx with h₂ | h₂
      · exact ih h₂
      rw [takeWhile_cons] at h₂
      split_ifs at h₂ with h₃
      · simp at h₂
        rwa [h₂]
      simp at h₂
    rw [take_append] at hx
    simp at hx
    rcases hx with h₂ | h₂
    · exact ih h₂
    have h₃ : (takeWhile P xs).length - xs.length = 0 :=
      by
        exact Nat.sub_eq_zero_of_le length_takeWhile_le
    simp [h₃] at h₂
  have h₁ : takeWhile P xs <+: xs := takeWhile_prefix P
  obtain ⟨ys, h₁⟩ := h₁
  rw [←h₁]
  cases ys
  · simp at h₁ ⊢
    rw [←takeWhile_eq_self_iff] at h₁
    simp [h₁]
  nm y ys
  have h₂ := not_apply_of_takeWhile_append_cons_eq_self h₁
  rw [append_cons, takeWhile_append, takeWhile_append, takeWhile_idem]
  simp [h₂]

theorem suffix_cons_of_suffix {α : Type*} {xs ys : List α} {y}
(h : xs <:+ ys) : xs <:+ y :: ys := by
  simp [List.suffix_cons_iff, h]

@[simp]
theorem not_cons_suffix {x} : ¬(x :: xs <:+ xs) := by
  rintro ⟨ys, h⟩
  replace h := congrArg (·.length) h
  simp at h
  linarith

theorem perm_swap_left {α : Type*} {xs ys : List α} {x y} :
(x :: y :: xs).Perm ys ↔ (y :: x :: xs).Perm ys := by
  constructor <;> intro h
  · trans x :: y :: xs
    rotate_left; exact h
    apply List.Perm.swap
  · trans y :: x :: xs
    rotate_left; exact h
    apply List.Perm.swap

theorem perm_swap_right {α : Type*} {xs ys : List α} {x y} :
xs.Perm (x :: y :: ys) ↔ xs.Perm (y :: x :: ys) := by
  rw [List.perm_comm]
  nth_rw 2 [List.perm_comm]
  exact perm_swap_left

@[simp]
theorem count_mergeSort {α : Type*} [ha : DecidableEq α]
{xs : List α} {x r} : (xs.mergeSort r).count x = xs.count x := by
  have h₁ := mergeSort_perm xs r
  rw [perm_iff_count] at h₁
  apply h₁

theorem count_eq_count_unattach {α : Type*} [ha : DecidableEq α]
{xs : List α} {ys : List {x // x ∈ xs}} {x} :
count x ys = count x.1 ys.unattach := by
  rcases x with ⟨x, hx⟩
  dsimp
  induction ys generalizing x
  · rfl
  nm y ys ih
  simp only [unattach_cons, count_cons]
  split_ifs with h₁ h₂ h₂ <;> simp at h₁ h₂ <;>
    (try contradiction) <;> simp <;> apply ih

theorem count_unattach_eq_ite {α : Type*} [ha : DecidableEq α]
{xs : List α} {ys : List {x // x ∈ xs}} {x : α} :
count x ys.unattach = if h : x ∈ xs then count ⟨x, h⟩ ys else 0 := by
  split_ifs with h₁
  · rw [count_eq_count_unattach]
  · simp [count_eq_zero, h₁]

theorem mergeSort_attach_perm {r} :
(xs.attach.mergeSort (r ·.1 ·.1)).unattach.Perm (xs.mergeSort r) := by
  classical
  rw [perm_iff_count]
  intro a
  simp
  rw [count_unattach_eq_ite]
  split_ifs with ha
  · convert @List.count_mergeSort {x // x ∈ xs} _ xs.attach
      ⟨a, ha⟩ (r ·.1 ·.1)
    convert (@count_attach α _ xs ⟨a, ha⟩).symm
  symm; rwa [count_eq_zero]

@[simp]
theorem pairwise_unattach {α : Type*}
{xs : List α} {ys : List {x // x ∈ xs}} {r : α → α → Prop} :
ys.unattach.Pairwise r ↔ ys.Pairwise (r ·.1 ·.1) := by
  induction ys <;> simp
  nm y ys ih
  intro h
  exact ih

theorem mergeSort_attach {r} :
(xs.attach.mergeSort (r ·.1 ·.1)).unattach = xs.mergeSort r := by
  rw [unattach, map_mergeSort (s := (r · ·))] <;> simp

theorem eq_of_perm_of_pairwise {α : Type*} {xs ys : List α} {r}
(hp : xs.Perm ys) (hx : xs.Pairwise r) (hy : ys.Pairwise r)
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a)
(h_ant : ∀ a b, a ∈ xs → b ∈ xs → r a b → r b a → a = b) : xs = ys := by
  induction xs generalizing ys
  · simp at hp
    rw [hp]
  nm x xs ih
  cases ys
  · simp at hp
  nm y ys
  simp at ⊢
  rw [pairwise_cons] at hx hy
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  apply and_of
  · by_contra hxy
    change x ≠ y at hxy
    have h₁ := @hp.mem_iff
    have h₂ := h₁ x; simp [hxy] at h₂
    have h₃ := h₁ y; simp [hxy.symm] at h₃
    specialize hx₁ y h₃
    specialize hy₁ x h₂
    specialize h_ant x y
    simp [hxy.symm, h₃, hx₁, hy₁] at h_ant
    contradiction
  rintro rfl
  simp at hp
  apply @ih ys hp hx₂ hy₂
  · intro a b c ha hb hc h₁ h₂
    apply h_tra a b c <;> simp [ha, hb, hc, h₁, h₂]
  · intro a b ha hb
    apply h_tot a b <;> simp [ha, hb]
  · intro a b ha hb h₁ h₂
    apply h_ant <;> simp [ha, hb, h₁, h₂]

theorem pairwise_mergeSort_loc' {r : α → α → Bool}
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a) :
(xs.mergeSort r).Pairwise (r · ·) := by
  rw [←@mergeSort_attach α xs r]
  simp
  apply pairwise_mergeSort
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    apply h_tra <;> assumption
  · rintro ⟨a, ha⟩ ⟨b, hb⟩; simp
    apply h_tot <;> assumption

theorem pairwise_mergeSort_loc
{r : α → α → Prop} [hr : DecidableRel r]
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a) :
(xs.mergeSort (r · ·)).Pairwise r := by
  have h₁ := pairwise_mergeSort_loc' (xs := xs) (r := (r · ·))
    (by simpa using h_tra) (by simpa using h_tot)
  simp at h₁; exact h₁

theorem eq_iff_of_nodup_and_pairwise {α : Type*}
(r : α → α → Prop) {xs ys : List α} (hx₁ : xs.Nodup) (hy₁ : ys.Nodup)
(h_ant : ∀ a b, a ∈ xs → b ∈ xs → r a b → r b a → a = b)
(hx₂ : xs.Pairwise r) (hy₂ : ys.Pairwise r) :
xs = ys ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  refine' ⟨λ h => by simp [h], λ h => _⟩
  induction xs generalizing ys
  · cases ys
    · rfl
    nm y ys
    specialize h y
    simp at h
  nm x xs ih
  cases ys
  · specialize h x
    simp at h
  nm y ys
  simp at h ⊢
  simp at hx₁ hx₂ hy₁ hy₂
  rcases hx₁ with ⟨hx₁, hx₃⟩
  rcases hy₁ with ⟨hy₁, hy₃⟩
  rcases hx₂ with ⟨hx₂, hx₄⟩
  rcases hy₂ with ⟨hy₂, hy₄⟩
  apply and_of
  · by_contra! h₁
    have h₂ := h x
    have h₃ := h y
    simp [h₁, h₁.symm] at h₂ h₃
    specialize hx₂ _ h₃
    specialize hy₂ _ h₂
    apply h₁
    apply h_ant <;> simp [h₃, hx₂, hy₂]
  rintro rfl
  apply ih hx₃ hy₃
  · intro a b ha hb h₁ h₂
    apply h_ant <;> simp [ha, hb, h₁, h₂]
  any_goals assumption
  intro z
  specialize h z
  by_cases hz : z = x
  · subst hz
    tauto
  · simp [hz] at h
    exact h

theorem eq_iff_of_nodup_and_pairwise' {α : Type*} [ha : LinearOrder α]
{xs ys : List α} (hx₁ : xs.Nodup) (hy₁ : ys.Nodup)
(hx₂ : xs.Pairwise (· ≤ ·)) (hy₂ : ys.Pairwise (· ≤ ·)) :
xs = ys ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  apply eq_iff_of_nodup_and_pairwise (· ≤ ·) hx₁ hy₁ _ hx₂ hy₂
  intro _ _ _ _; exact le_antisymm

@[simp]
theorem take_length_add {n} : xs.take (xs.length + n) = xs := by
  simp [take_add]

@[simp]
theorem mergeSort_perm' {r : α → α → Bool} :
xs.mergeSort r ~ xs := by apply mergeSort_perm

@[simp]
theorem perm_mergeSort {r : α → α → Bool} :
xs ~ xs.mergeSort r := by symm; simp

theorem perm_of_mergeSort_perm_mergeSort {α : Type*}
{xs ys : List α} {r₁ r₂ : α → α → Bool}
(h : xs.mergeSort r₁ ~ ys.mergeSort r₂) : xs ~ ys := by
  trans xs.mergeSort r₁; simp
  apply h.trans; simp

theorem perm_of_mergeSort_eq_mergeSort {α : Type*}
{xs ys : List α} {r₁ r₂ : α → α → Bool}
(h : xs.mergeSort r₁ = ys.mergeSort r₂) : xs ~ ys := by
  trans xs.mergeSort r₁; simp; simp [h]

@[simp]
theorem mergeSort_eq_nil_iff {r : α → α → Bool} :
xs.mergeSort r = [] ↔ xs = [] := by
  cases xs <;> simp
  apply ne_of_congr List.length
  simp

attribute [simp] pairwise_map

theorem foldl_eq_foldl_of_perm {α β : Type*}
{f : β → α → β} {z : β} {xs ys : List α}
(h_assoc : ∀ {acc x y}, f (f acc x) y = f (f acc y) x)
(h : xs ~ ys) : xs.foldl f z = ys.foldl f z := by
  induction h generalizing z <;> clear xs ys
  · rfl
  · nm x xs ys h ih; simp [ih]
  · nm x y xs; simp [h_assoc]
  · nm xs ys zs h₁ h₂ ih₁ ih₂; rw [ih₁, ih₂]

open Classical in
theorem foldl_bool_to_prop {α : Type*}
{xs : List α} {f : Bool → α → Bool} {z : Bool} :
xs.foldl f z = @xs.foldl Prop α (λ acc x => f acc x) z := by
  induction xs generalizing z; simp
  nm x xs ih; simp [ih]

@[simp]
theorem snoc_perm_iff {α : Type*} {xs ys : List α} {x} :
xs ++ [x] ~ ys ↔ x :: xs ~ ys := by
  classical
  rw [←reverse_perm']
  simp [cons_perm_iff_perm_erase]

@[simp]
theorem perm_snoc_iff {α : Type*} {xs ys : List α} {y} :
xs ~ ys ++ [y] ↔ xs ~ y :: ys := by
  rw [perm_comm]; nth_rw 2 [perm_comm]; simp

@[simp]
theorem cons_reverse_perm_iff {α : Type*} {xs ys : List α} {x} :
x :: xs.reverse ~ ys ↔ x :: xs ~ ys := by
  classical simp [cons_perm_iff_perm_erase]

@[simp]
theorem perm_cons_reverse_iff {α : Type*} {xs ys : List α} {y} :
xs ~ y :: ys.reverse ↔ xs ~ y :: ys := by
  rw [perm_comm]; nth_rw 2 [perm_comm]; simp

theorem mem_iff_mem_iff_subset {α : Type*} {xs ys : List α} :
(∀ x, x ∈ xs ↔ x ∈ ys) ↔ xs ⊆ ys ∧ ys ⊆ xs := by
  unfold instHasSubset List.Subset
  constructor
  · intro h; simp [h]
  rintro ⟨h₁, h₂⟩ a
  constructor
  · apply h₁
  · apply h₂

theorem perm_iff_subset_of_nodup {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) : xs ~ ys ↔ xs ⊆ ys ∧ ys ⊆ xs := by
  rw [List.perm_ext_iff_of_nodup hx hy]
  exact mem_iff_mem_iff_subset

@[simp]
theorem nil_subset' : [] ⊆ xs := by
  apply nil_subset

theorem perm_of_nodup_and_subperm_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs <+~ ys) (h₂ : xs.length = ys.length) : ys ~ xs := by
  classical
  obtain ⟨zs, h₁, h₃⟩ := h₁
  trans zs
  rotate_left
  · exact h₁
  rw [h₁.symm.length_eq] at h₂
  clear! xs
  symm
  suffices zs = ys by rw [this]
  rwa [←h₃.length_eq]

theorem subset_iff_subperm_of_nodup {α : Type*} {xs ys : List α}
(h : xs.Nodup) : xs ⊆ ys ↔ xs <+~ ys := by
  use subperm_of_subset h
  rintro ⟨zs, h₁, h₂⟩
  apply Subset.trans (l₂ := zs)
  · exact h₁.symm.subset
  · exact h₂.subset

theorem nodup_of_nodup_and_subset_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs.Nodup) (h₂ : xs ⊆ ys)
(h₃ : xs.length = ys.length) : ys.Nodup := by
  classical
  rw [subset_iff_subperm_of_nodup h₁] at h₂
  have h₄ := perm_of_nodup_and_subperm_and_length_eq h₂ h₃
  rwa [h₄.nodup_iff]

theorem perm_iff_mem_iff_of_nodup {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) : xs ~ ys ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  rw [perm_iff_subset_of_nodup hx hy]
  change (∀ _, _) ∧ (∀ _, _) ↔ _
  use λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩
  intro h; simp [h]

theorem subset_iff_exi_get {α  : Type*} {xs ys : List α} :
xs ⊆ ys ↔ ∀ x ∈ xs, ∃ (i : ℕ) (_ : i < ys.length), ys[i] = x := by
  simp_rw [←mem_iff_getElem]; rfl

theorem exi_get_iff_subset {α  : Type*} {xs ys : List α} :
(∀ x ∈ xs, ∃ (i : ℕ) (_ : i < ys.length), ys[i] = x) ↔ xs ⊆ ys :=
  subset_iff_exi_get.symm

attribute [simp] take_prefix

instance {α : Type*} : IsEquiv (List α) List.Perm where
  refl := Perm.refl
  symm := λ _ _ => Perm.symm
  trans := λ _ _ _ => Perm.trans

@[simp]
theorem mergeSort_perm_mergeSort {α : Type*}
{r₁ r₂ : α → α → Bool} {xs ys : List α} :
xs.mergeSort r₁ ~ ys.mergeSort r₂ ↔ xs ~ ys := by
  apply iff_of_isEquiv <;> simp

@[simp]
theorem eq_nil_of_isEmpty {α : Type*} [ha : IsEmpty α]
{xs : List α} : xs = [] := by
  cases xs; rfl
  nm x xs
  simp
  exact ha.1 x

@[simp]
theorem atMostOne_nil : [].atMostOne = true := rfl

@[simp]
theorem atMostOne_singleton {b} : [b].atMostOne = true := by
  cases b <;> rfl

@[simp]
theorem atMostOne_true_succ {bs} :
(true :: bs).atMostOne = !bs.or := rfl

@[simp]
theorem atMostOne_false_succ {bs} :
(false :: bs).atMostOne = bs.atMostOne := rfl

@[simp]
theorem atMostOne_pair {b₁ b₂} :
[b₁, b₂].atMostOne = (!b₁ || !b₂) := by
  simp [atMostOne]

@[simp]
theorem nodup_snoc {x} : (xs ++ [x]).Nodup ↔ x ∉ xs ∧ xs.Nodup := by
  rw [←nodup_reverse]; simp

@[simp]
theorem pairwise_snoc {x p} : (xs ++ [x]).Pairwise p ↔
xs.Pairwise p ∧ (∀ y ∈ xs, p y x) := by simp [pairwise_append]

theorem filterMap_eq [hb : Inhabited β] {f : α → Option β} :
xs.filterMap f = (xs.map f |>.filter Option.isSome |>.map Option.get!) := by
  induction xs; rfl
  nm x xs ih
  simp [filterMap, filter]
  split <;> nm b h <;> simpa [h]

theorem foldl_some_some {f : α → α → α} {z} :
xs.foldl (λ acc x => some # acc.elim x (f · x)) (some z) = some (xs.foldl f z) := by
  induction xs using List.reverseRecOn; simp
  nm xs x ih; simp [ih]

theorem min?_eq_foldl [ha : LinearOrder α] :
xs.min? = xs.foldl (λ acc x => some # acc.elim x (min · x)) none := by
  cases xs; rfl; simp [foldl_some_some, min?]

theorem max?_eq_foldl [ha : LinearOrder α] :
xs.max? = xs.foldl (λ acc x => some # acc.elim x (max · x)) none := by
  cases xs; rfl; simp [foldl_some_some, max?]

theorem foldl_comm {f : β → α → β} {z x}
(h_assoc : ∀ {x y z}, f (f x y) z = f (f x z) y) :
xs.foldl f (f z x) = f (xs.foldl f z) x := by
  induction xs generalizing z; rfl; clear! xs; nm y xs ih
  simp [←ih, h_assoc]

theorem foldl_append_comm {f : β → α → β} {z}
(h_assoc : ∀ {x y z}, f (f x y) z = f (f x z) y) :
(xs ++ ys).foldl f z = (ys ++ xs).foldl f z := by
  simp; induction xs generalizing z ys; simp
  nm x xs ih; simp [ih, foldl_comm h_assoc]

theorem min?_append_comm [ha : LinearOrder α] {ys : List α} :
(xs ++ ys).min? = (ys ++ xs).min? := by
  simp only [min?_eq_foldl]; apply foldl_append_comm
  rintro (_ | x) y z <;> simp; apply min_comm; apply inf_right_comm

theorem max?_append_comm [ha : LinearOrder α] {ys : List α} :
(xs ++ ys).max? = (ys ++ xs).max? := by
  simp only [max?_eq_foldl]; apply foldl_append_comm
  rintro (_ | x) y z <;> simp; apply max_comm; apply sup_right_comm

@[simp]
theorem min?_reverse [ha : LinearOrder α] : xs.reverse.min? = xs.min? := by
  induction xs; rfl; clear! xs; nm x xs ih; simp [min?_append_comm, ih]

@[simp]
theorem max?_reverse [ha : LinearOrder α] : xs.reverse.max? = xs.max? := by
  induction xs; rfl; clear! xs; nm x xs ih; simp [max?_append_comm, ih]

theorem max?_eq_getLast? [ha : LinearOrder α]
(h : xs.SortedLE) : xs.max? = xs.getLast? := by
  have h₁ := @List.min?_eq_head?
  specialize @h₁ α ⟨max⟩ xs.reverse
  simp [pairwise_reverse] at h₁
  rw [←sortedLE_iff_pairwise] at h₁
  specialize h₁ h
  convert h₁ using 1
  symm; exact max?_reverse

@[simp]
theorem foldlWith_snoc {β : Sort*} {x : α} {f : β → (y : α) → y ∈ xs ++ [x] → β} {z : β} :
(xs ++ [x]).foldlWith f z = f (xs.foldlWith (λ acc y h => f acc y (by simp [h])) z)
x (by simp) := by induction xs generalizing z; rfl; nm y xs ih; simp [ih]

theorem foldl_eq_foldl_of_fn_congr {f g : β → α → β} {z : β}
(h : ∀ acc, ∀ x ∈ xs, f acc x = g acc x) : xs.foldl f z = xs.foldl g z := by
  induction xs using List.reverseRecOn; rfl
  clear! xs; nm xs x ih
  simp
  specialize ih _
  · intro acc y hy
    specialize h acc y
    simp  [hy] at h
    exact h
  rw [ih]
  apply h
  simp

theorem foldlWith_eq_foldl [ha : DecidableEq α] {f : β → (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith f z = xs.foldl (λ acc x => if h : x ∈ xs then f acc x h else z) z := by
  induction xs using List.reverseRecOn; rfl
  clear! xs; nm xs x ih
  simp [ih]
  congr 1
  apply foldl_eq_foldl_of_fn_congr
  intro acc y hy
  simp [hy]

theorem rec_eq_foldr {z : β} {f : α → β → β} :
@List.rec α (λ _ => β) z (λ x _ acc => f x acc) xs = xs.foldr f z := by
  induction xs <;> simp_all

theorem foldr_max_eq_max?_map [hb : LinearOrder β] {f : α → β} {z : β} :
xs.foldr (λ x => max (f x)) z = (xs.map f).max?.elim z (max z) := by
  induction xs; rfl
  nm x xs ih
  simp [ih]
  generalize (xs.map f).max? = r
  rcases r with _ | r <;> simp
  apply max_comm; apply max_left_comm

theorem foldr_max_eq_max?_map' [hb : LinearOrder β] {f : α → β} {z : β} :
xs.foldr (λ x => max (f x)) z = (z :: xs.map f).max?.getD z := by
  simp; exact foldr_max_eq_max?_map

theorem max?_eq_max?_of_perm [ha : LinearOrder α]
(h : xs.Perm ys) : xs.max? = ys.max? := by
  simp only [max?_eq_foldl]
  apply foldl_eq_foldl_of_perm; rotate_left; exact h
  rintro (_ | acc) x y <;> simp
  apply max_comm; apply sup_right_comm

theorem apply_of_pairwise_and_lt {p : α → α → Prop} {i j}
{hh₁ : i < xs.length} {hh₂ : j < xs.length}
(h₁ : xs.Pairwise p) (h₂ : i < j) : p xs[i] xs[j] := by
  rw [List.pairwise_iff_get] at h₁
  specialize h₁ ⟨i, hh₁⟩ ⟨j, hh₂⟩ h₂
  simp at h₁; exact h₁

theorem dfltMapWith_eq_dfltMapWith {f₁ f₂ : (x : α) → x ∈ xs → β}
{h : xs ≠ []} : dfltMapWith f₁ h = dfltMapWith f₂ h := by
  cases xs; simp at h; nm x xs; simp [dfltMapWith]

@[simp]
theorem dfltMapWith_eq_some_of_nonempty [hb : Nonempty β] {f : (x : α) → x ∈ xs → β}
{h : xs ≠ []} : dfltMapWith f h = hb.some := by
  cases xs; simp at h; simp [dfltMapWith]

theorem mapWith_eq_map [ha : DecidableEq α] {f : (x : α) → x ∈ xs → β} :
xs.mapWith f = if h : xs = [] then [] else
xs.map (λ x => if h₁ : x ∈ xs then f x h₁ else
dfltMapWith f h) := by
  induction xs; rfl
  clear! xs; nm x xs ih
  simp [ih]; clear ih
  split_ifs with h₁; simp [h₁]
  simp
  intro y hy
  simp [hy]

theorem foldl_max_eq_max?_map [hb : LinearOrder β] {f : α → β} {z : β} :
xs.foldl (λ acc x => max acc (f x)) z = (xs.map f).max?.elim z (max z) := by
  classical
  rw [foldl_eq_foldr_reverse]
  have h₁ : (λ x y => max y (f x)) = (λ x => max (f x))
  · ext x y; rw [max_comm]
  rw [h₁]; clear h₁
  rw [foldr_max_eq_max?_map]
  simp

theorem foldlWith_max_eq_max?_mapWith [hb : LinearOrder β]
{f : (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith (λ acc x h => max acc (f x h)) z =
(xs.mapWith f).max?.elim z (max z) := by
  classical
  generalize hn : xs.length = n
  induction n generalizing xs f z
  · simp at hn; subst hn; rfl
  nm n ih
  cases xs; simp at hn; nm x xs
  simp at hn ⊢
  rw [ih hn]; clear! n
  suffices h₁ : ∀ (m : Option β) x, m.elim (max z x) (max (max z x)) =
    max z (m.elim x (max x)); apply h₁
  rintro (_ | m) x; rfl
  apply max_assoc

theorem max?_eq_some_iff₁ [ha : LinearOrder α] {m} :
xs.max? = some m ↔ m ∈ xs ∧ ∀ b ∈ xs, b ≤ m :=
  @max?_eq_some_iff α m _ _ xs _ _

theorem le_of_max?_eq_some [ha : LinearOrder α] {x m}
(h₁ : x ∈ xs) (h₂ : xs.max? = some m) : x ≤ m := by
  rw [max?_eq_some_iff₁] at h₂
  exact h₂.2 x h₁

theorem le_getD_max?_of_mem [ha : LinearOrder α] {x y}
(h : x ∈ xs) : x ≤ xs.max?.getD y := by
  cases h₁ : xs.max?; simp at h₁; simp [h₁] at h
  exact le_of_max?_eq_some h h₁

theorem le_elim_max_max?_of_mem [ha : LinearOrder α] {x y z}
(h : x ∈ xs) : x ≤ xs.max?.elim y (max z) := by
  cases h₁ : xs.max?; simp at h₁; simp [h₁] at h
  simp; right; exact le_of_max?_eq_some h h₁

@[simp]
theorem mem_mapWith [ha : DecidableEq α] {f : (x : α) → x ∈ xs → β} {y} :
y ∈ xs.mapWith f ↔ ∃ (x : α) (h : x ∈ xs), f x h = y := by
  simp only [mapWith_eq_map, mem_dite_nil_left, mem_map]
  constructor
  · rintro ⟨h₁, x, hx, h₂⟩
    simp [hx] at h₂
    use x, hx
  · rintro ⟨x, hx, h₂⟩
    subst h₂
    use by rintro rfl; simp at hx
    use x, hx
    simp [hx]

theorem pairwise_of_pairwise_and_imp {r₁ r₂ : α → α → Prop}
(h₁ : xs.Pairwise r₁) (h₂ : ∀ {a b}, r₁ a b → r₂ a b) : xs.Pairwise r₂ := by
  induction xs; simp
  clear! xs; nm x xs ih
  simp at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  refine' ⟨_, ih h₃⟩
  intro y ys
  exact h₂ # h₁ _ ys

theorem pairwise_le_of_pairwise_lt [ha : LinearOrder α]
(h : xs.Pairwise (· < ·)) : xs.Pairwise (· ≤ ·) :=
  pairwise_of_pairwise_and_imp h le_of_lt

@[simp]
theorem flatMap_fn_singleton {f : α → β} : xs.flatMap ([f ·]) = xs.map f := by
  induction xs; rfl; simpa

theorem reverse_snoc {x} : (xs ++ [x]).reverse = x :: xs.reverse := by
  simp

theorem append_take_eq_of_suffix (h : ys <:+ xs) :
xs.take (xs.length - ys.length) ++ ys = xs := by
  rwa [←suffix_iff_eq_append]

theorem take_length_sub_append_eq_of_suffix (h : ys <:+ xs) :
xs.take (xs.length - ys.length) ++ ys = xs := by
  obtain ⟨xs, rfl⟩ := h; simp

@[simp]
theorem take_length_sub_append_eq_self_iff_suffix :
xs.take (xs.length - ys.length) ++ ys = xs ↔ ys <:+ xs :=
  ⟨λ h => ⟨_, h⟩, List.take_length_sub_append_eq_of_suffix⟩

@[simp]
theorem self_eq_take_length_sub_append_iff_suffix :
xs = xs.take (xs.length - ys.length) ++ ys ↔ ys <:+ xs := by
  rw [eq_comm]; simp

theorem mem_of_count_ne_zero [ha : DecidableEq α] {x} (h : xs.count x ≠ 0) : x ∈ xs := by
  simp [count_eq_zero] at h; exact h

theorem mem_of_count_pos [ha : DecidableEq α] {x} (h : 0 < xs.count x) : x ∈ xs :=
  count_pos_iff.mp h

theorem mem_of_lt_count [ha : DecidableEq α] {x n} (h : n < xs.count x) : x ∈ xs :=
  mem_of_count_pos # by linarith

@[simp]
theorem mem_toSet {x} : x ∈ xs.toSet ↔ x ∈ xs := by
  simp [toSet]

@[simp]
theorem toSet_nil : ([] : List α).toSet = ∅ := by simp [toSet]

@[simp]
theorem toSet_cons {x} : (x :: xs).toSet = insert x xs.toSet := by
  simp [toSet]; aesop

theorem Perm.toSet_eq (h : xs ~ ys) : xs.toSet = ys.toSet := by
  simp [List.toSet, h.mem_iff]

section linearIndep

variable [ha₁ : One α] [ha₂ : Mul α] [ha₃ : HPow α ℤ α]

theorem linearIndep_iff_toSet : linearIndep xs ↔ linearIndep xs.toSet := by
  simp only [linearIndep, ne_eq, Prod.forall, and_imp, mem_toSet]

@[simp]
theorem linearIndep_nil : linearIndep ([] : List α) := by
  simp [linearIndep_iff_toSet]

@[simp]
theorem linearIndep_singleton {x : α} : linearIndep [x] := by
  simp [linearIndep_iff_toSet]

theorem Perm.linearIndep_iff (h : xs ~ ys) : linearIndep xs ↔ linearIndep ys := by
  simp [linearIndep_iff_toSet, h.toSet_eq]

end linearIndep

theorem min?_eq_some_iff₁ {ha : LinearOrder α} {x} :
xs.min? = some x ↔ x ∈ xs ∧ ∀ y ∈ xs, x ≤ y := by
  induction xs generalizing x; simp; clear! xs; nm z xs ih
  simp; cases h : xs.min?; aesop; nm m; dsimp; simp [ih] at h
  rcases h with ⟨h₁, h₂⟩; constructor
  · rintro rfl; simp; constructor
    · rw [or_iff_not_imp_left]; intro h₃
      simp at h₃; rwa [min_eq_right_of_lt h₃]
    · intro b hb; specialize h₂ b hb; simp [h₂]
  rintro ⟨rfl | h₃, h₄, h₅⟩
  · simp; exact h₅ _ h₁
  · have h₆ := h₂ _ h₃; have h₇ := h₆.trans h₄
    rw [min_eq_right h₇]; have h₈ := h₅ _ h₁
    exact le_antisymm h₆ h₈

theorem mem_iff_append_of_nodup {x} (h : xs.Nodup) :
x ∈ xs ↔ ∃ ys zs, x ∉ ys ∧ x ∉ zs ∧ xs = ys ++ x :: zs := by
  rw [mem_iff_append]
  apply exists_congr; intro ys
  apply exists_congr; intro zs
  symm; constructor; simp
  rintro rfl; simp
  simp [nodup_append] at h
  rcases h with ⟨-, ⟨h₁, -⟩, h₂⟩
  refine ⟨?_, h₁⟩
  intro h₃
  specialize h₂ _ h₃
  simp at h₂

theorem mem_erase_iff_of_nodup [ha : DecidableEq α] {x y}
(h : xs.Nodup) : y ∈ xs.erase x ↔ y ≠ x ∧ y ∈ xs := by
  induction xs; simp
  clear! xs; nm z xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  simp [erase_cons]
  split_ifs with hp
  · subst hp; aesop
  · simp [ih]; clear ih; aesop

theorem erase_append_cons_eq_of_not_mem [ha : DecidableEq α] {x}
(h : x ∉ xs) : (xs ++ x :: ys).erase x = xs ++ ys := by
  induction xs; simp
  clear! xs; nm z xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  simp [ne_symm' h₁]
  exact ih h₂

@[simp]
theorem drop_length_reverse : xs.reverse.drop xs.length = [] := by
  simp [drop_reverse]

@[simp]
theorem drop_succ_length_reverse : xs.reverse.drop (xs.length + 1) = [] := by
  simp [drop_reverse]

@[simp]
theorem drop_succ_length_reverse_snoc {x} :
(xs.reverse ++ [x]).drop (xs.length + 1) = [] := by simp

@[simp]
theorem drop_reverse_append_cons_length_succ {x} :
(xs.reverse ++ x :: ys).drop xs.length = x :: ys := by simp

@[simp]
theorem drop_reverse_append_cons_succ_length_succ {x} :
(xs.reverse ++ x :: ys).drop (xs.length + 1) = ys := by
  rw [←length_reverse, drop_add_one_eq_tail_drop, drop_append]; simp

theorem pairwise_of_pairwise_and_sublist {r}
(h₁ : xs.Pairwise r) (h₂ : ys <+ xs) : ys.Pairwise r := by
  induction h₂ <;> clear! xs ys
  · exact h₁
  · nm xs ys x h₂ ih
    simp at h₁
    exact ih h₁.2
  · nm xs ys x h₂ ih
    simp at h₁ ⊢
    rcases h₁ with ⟨h₁, h₃⟩
    specialize ih h₃
    symm; use ih
    intro y hy
    apply h₁
    exact h₂.mem hy

theorem find?_cons' {p : α → Bool} {x xs} :
(x :: xs).find? p = if p x then some x else xs.find? p := by
  simp [find?_cons]; split
  · simp_all only [↓reduceIte]
  · simp_all only [Bool.false_eq_true, ↓reduceIte]

theorem find?_eq_some_equiv_iff {e : α ≃ α} {p : α → Bool} {x} :
xs.find? p = some (e x) ↔ (xs.map e.symm).find? (p ∘ e) = some x := by
  simp [find?_eq_some_iff_append]; constructor
  · rintro ⟨h₁, xs, ⟨ys, rfl⟩, h₂⟩; use e x; simp [h₁]; use xs; simpa
  · rintro ⟨x, ⟨h₁, xs, ⟨h₂, rfl⟩, h₃⟩, rfl⟩; simp [h₁]; use xs; simpa

theorem cons_eq_append {x} : x :: xs = [x] ++ xs := rfl

attribute [simp] List.nodup_range

theorem getElem?_eq_of_getElem_eq
{i j} {hi : i < xs.length} {hj : j < ys.length} (h : xs[i] = ys[j]) : xs[i]? = ys[j]? := by
  rw [getElem?_eq_getElem hi, getElem?_eq_getElem hj, h]

theorem getElem_eq_of_getElem?_eq
{i j} {hi : i < xs.length} {hj : j < ys.length} (h : xs[i]? = ys[j]?) : xs[i] = ys[j] := by
  simp_rw [getElem_eq_getElem?_get, h]

theorem getElem_eq_iff_getElem?_eq
{i j} {hi : i < xs.length} {hj : j < ys.length} : xs[i] = ys[j] ↔ xs[i]? = ys[j]? :=
  ⟨getElem?_eq_of_getElem_eq, getElem_eq_of_getElem?_eq⟩

theorem nodup_iff_getElem_ne_getElem :
xs.Nodup ↔ ∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j] := by
  rw [nodup_iff_getElem?_ne_getElem?]
  apply forall_congr'; intro i
  apply forall_congr'; intro j
  constructor
  · intro h h₁ h₂ h₃
    specialize h h₃ h₂
    contrapose! h
    exact getElem?_eq_of_getElem_eq h
  · intro h h₁ h₂
    specialize h (by linarith) h₂ h₁
    contrapose! h
    exact getElem_eq_of_getElem?_eq h

theorem nodup_flatMap_flatMap_pair [ha : LinearOrder α]
{r : α → α → Prop} [hp : DecidableRel r]
(hxs : xs.Nodup) (hys : ys.Nodup) :
(xs.flatMap (λ x => ys.flatMap # λ y =>
if x < y ∧ r x y then [(x, y)] else [])).Nodup := by
  classical
  by_cases h₀ : IsEmpty α; simp; push_neg at h₀; replace h₀ := h₀.inhabited
  rw [nodup_flatMap]
  symm; split_ands
  · unfold Function.onFun Disjoint
    simp
    induction xs
    · simp
    nm x xs ih
    simp at hxs ⊢
    rcases hxs with ⟨h₁, h₂⟩
    specialize ih h₂
    simp [ih]; clear ih
    intros; simp_all only
  intro x hx
  rw [nodup_flatMap]
  symm; split_ands
  · unfold Function.onFun Disjoint
    simp
    induction ys
    · simp
    nm y hy ih
    simp at hys ⊢
    rcases hys with ⟨h₁, h₂⟩
    specialize ih h₂
    simp [ih]; clear ih
    intros; rintro rfl; simp_all only
  intro y hy
  split_ifs <;> simp

theorem nodup_flatMap_flatMap_upair [ha : LinearOrder α]
{r : α → α → Prop} [hp : DecidableRel r]
(hxs : xs.Nodup) (hys : ys.Nodup) :
(xs.flatMap (λ x => ys.flatMap # λ y =>
if x < y ∧ r x y then [({x, y} : Set α)] else [])).Nodup := by
  classical
  by_cases h₀ : IsEmpty α; simp; push_neg at h₀; replace h₀ := h₀.inhabited
  generalize hA : (λ x => ys.flatMap # λ y =>
    if x < y ∧ r x y then [({x, y} : Set α)] else []) = A
  symm at hA
  rw [funext_iff] at hA
  generalize hf : (λ (s : Set α) =>
    ( Classical.epsilon # λ x => x ∈ s ∧ ∀ y ∈ s, x ≤ y
    , Classical.epsilon # λ x => x ∈ s ∧ ∀ y ∈ s, y ≤ x
    )) = f
  generalize hB : (xs.flatMap A).map f = B
  suffices h : B.Nodup
  · subst hB; exact Nodup.of_map _ h
  replace hB : B = xs.flatMap (λ x => ys.flatMap # λ y =>
    if x < y ∧ r x y then [(x, y)] else [])
  · subst hB
    rw [map_flatMap]
    congr
    ext x :1
    rw [hA]
    rw [map_flatMap]
    clear! hA
    congr
    ext y :1
    rw [apply_ite (f := map f)]
    simp
    split_ifs with h₁ <;> simp
    replace h₁ := h₁.1
    subst hf
    simp
    have h₂ := le_of_lt h₁
    rw [epsilon_eq_of (x := x), epsilon_eq_of (x := y)] <;> simp [h₂]
    all_goals intro h₃; apply le_antisymm <;> assumption
  subst hB; exact nodup_flatMap_flatMap_pair hxs hys

theorem getElem_scanl' {f : β → α → β} {z i} {hi : i < (xs.scanl f z).length} :
(xs.scanl f z)[i] = (xs.take i).foldl f z :=
  getElem_scanl hi

theorem take_scanl' {f : β → α → β} {z n} :
(xs.scanl f z).take (n + 1) = (xs.take n).scanl f z :=
  take_scanl _ _ _

theorem drop_scanl {f : β → α → β} {z n} (hn : n ≤ xs.length) :
(xs.scanl f z).drop n = (xs.drop n).scanl f (xs.take n |>.foldl f z) := by
  induction xs generalizing z n; simp at hn; simp [hn]
  rename_i x xs ih; cases n <;> simp; rename_i n; simp at hn; apply ih; exact hn

theorem mem_scanl_iff_exists_prefix {f : β → α → β} {z x} :
x ∈ xs.scanl f z ↔ ∃ ys, ys <+: xs ∧ ys.foldl f z = x := by
  induction xs generalizing z; simp [eq_comm]; rename_i y xs ih; simp [ih]; constructor
  · rintro (rfl | ⟨ys, h₁, h₂⟩); use []; simp; use y :: ys; simp [h₁, h₂]
  · rintro ⟨ys, h₁, rfl⟩; cases ys; simp; rename_i y' ys; right
    simp at h₁; rcases h₁ with ⟨rfl, h₁⟩; use ys; simpa

@[simp]
theorem mem_scanl_iff_exists_take {f : β → α → β} {z x} :
x ∈ xs.scanl f z ↔ ∃ n, (xs.take n).foldl f z = x := by
  simp_rw [mem_scanl_iff_exists_prefix, prefix_iff_eq_take]; constructor
  · rintro ⟨ys, h₁, rfl⟩; generalize ys.length = n at h₁; simp [h₁]
  · rintro ⟨n, rfl⟩; use xs.take n; simp

@[simp]
theorem foldl_add_length {L : List (List α)} {z} :
L.foldl (· + ·.length) z = (L.map length).sum + z := by
  induction L generalizing z <;> simp; rename_i xs L ih; rw [ih]; omega

theorem findIdx_le_of_getElem {i} {hi : i < xs.length} {p : α → Bool}
(h : p xs[i]) : xs.findIdx p ≤ i := by
  induction xs generalizing i; simp at hi; rename_i x xs ih; simp [findIdx_cons, cond]
  split <;> rename_i x h₁; simp; cases i; simp [h₁] at h; simp at h ⊢; exact ih h

theorem getElem_eq_getElem_zero_drop {i} {hi : i < xs.length} :
xs[i] = (xs.drop i)[0]'(by simpa) := by simp

theorem drop_add {n m} : xs.drop (n + m) = (xs.drop n).drop m :=
  drop_drop.symm

theorem drop_add' {n m} : xs.drop (n + m) = (xs.drop m).drop n := by
  rw [add_comm, drop_drop]

theorem lt_length_of_getElem?_eq_some {i x} (h : xs[i]? = some x) : i < xs.length := by
  rw [getElem?_eq_some_iff] at h; tauto

theorem eq_append_getElem {i} (h : i < xs.length) :
xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by simp

theorem take_eq_self_of_le {n} (h : xs.length ≤ n) : xs.take n = xs := by
  simpa

theorem sum_take_le_sum {xs : List ℕ} {n} : (xs.take n).sum ≤ xs.sum := by
  induction xs generalizing n <;> simp; rename_i x xs ih; cases n <;> simp [ih]

theorem findIdx_eq_zero_iff {p : α → Bool} :
xs.findIdx p = 0 ↔ xs = [] ∨ ∃ (h : 0 < xs.length), p xs[0] := by
  cases xs <;> simp; rw [findIdx_eq] <;> simp

theorem max?_eq_max?_of_mem_iff [ha : LinearOrder α]
(h : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.max? = ys.max? := by
  ext; simp [max?_eq_some_iff, h]

@[simp]
theorem getD_getElem?_replicate {n i : ℕ} {x : α} : (replicate n x)[i]?.getD x = x := by
  rw [getElem?_def]; split_ifs <;> simp

@[simp]
theorem getD_getElem?_append_replicate {n i : ℕ} {x : α} :
(xs ++ replicate n x)[i]?.getD x = xs[i]?.getD x := by
  rw [getElem?_append]; split_ifs with h <;> simp
  push_neg at h
  rw [getElem?_eq_none h]
  rfl

-----

theorem foldl_bool_iff_foldl_prop {f : Bool → α → Bool} {z : Bool} :
xs.foldl f z ↔ xs.foldl (α := Prop) (λ acc x => f (acc = true) x) z := by
  induction xs generalizing z; simp; nm x xs ih; simp [ih]

theorem foldl_prop_iff_foldl_bool [H : ∀ P, Decidable P] {f : Prop → α → Prop} {z : Prop} :
xs.foldl f z ↔ xs.foldl (α := Bool) (λ acc x => f acc x) z := by
  induction xs generalizing z; simp; nm x xs ih; simp [ih]

theorem foldl_bool_and_eq_all {p : α → Bool} :
xs.foldl (λ a x => a && p x) true = xs.all p := by
  induction xs using List.reverseRecOn; simp; nm x xs ih; simp [ih]

theorem foldl_bool_and_iff_forall {p : α → Bool} :
xs.foldl (λ a x => a && p x) true ↔ ∀ x ∈ xs, p x := by
  simp [foldl_bool_and_eq_all]

theorem foldl_and_iff_forall {p : α → Prop} :
xs.foldl (λ a x => a ∧ p x) True ↔ ∀ x ∈ xs, p x := by
  classical simp [foldl_prop_iff_foldl_bool, foldl_bool_and_eq_all]

section foldlWith

theorem foldlWith_bool_iff_foldlWith_prop {f : Bool → (x : α) → x ∈ xs → Bool} {z : Bool} :
xs.foldlWith f z ↔ xs.foldlWith (β := Prop) (λ acc x h => f (acc = true) x h) z := by
  induction xs generalizing z; simp; nm x xs ih; simp [ih]

theorem foldlWith_prop_iff_foldlWith_bool [H : ∀ P, Decidable P]
{f : Prop → (x : α) → x ∈ xs → Prop} {z : Prop} :
xs.foldlWith f z ↔ xs.foldlWith (β := Bool) (λ acc x h => f acc x h) z := by
  induction xs generalizing z; simp; nm x xs ih; simp [ih]

theorem foldlWith_bool_and_iff_forall {p : (x : α) → x ∈ xs → Bool} :
xs.foldlWith (λ a x h => a && p x h) true ↔ ∀ (x : α) (h : x ∈ xs), p x h := by
  induction xs using List.reverseRecOn; simp; nm x xs ih; simp [ih]
  apply Iff.intro
  · intro a x_1 h
    obtain ⟨left, right⟩ := a
    cases h with
    | inl h_1 => simp_all only
    | inr h_2 =>
      subst h_2
      simp_all only
  · intro a
    simp_all only [true_or, implies_true, or_true, and_self]

theorem foldlWith_and_iff_forall {p : (x : α) → x ∈ xs → Prop} :
xs.foldlWith (λ a x h => a ∧ p x h) True ↔ ∀ (x : α) (h : x ∈ xs), p x h := by
  classical simp [foldlWith_prop_iff_foldlWith_bool, foldlWith_bool_and_iff_forall]

end foldlWith

theorem getElem!_eq_getElem [ha : Inhabited α] {i} (h : i < xs.length) : xs[i]! = xs[i] :=
  getElem!_pos xs i h

theorem nodup_of_pairwise {p : α → α → Prop} (h₁ : xs.Pairwise p)
(h₂ : ∀ {x y}, x ∈ xs → y ∈ xs → p x y → x ≠ y) : xs.Nodup :=
  Pairwise.imp_of_mem h₂ h₁

@[simp]
theorem nodup_append_self_iff : (xs ++ xs).Nodup ↔ xs = [] := by
  cases xs <;> simp

theorem nodup_flatMap_of {f : α → List β} (h₁ : xs.Nodup)
(h₂ : ∀ x ∈ xs, (f x).Nodup ∧ ∀ y ∈ xs, ∀ z, z ∈ f x → z ∈ f y → x = y) :
(xs.flatMap f).Nodup := by
  induction xs <;> simp; grind

theorem flatMap_fn_replicate_guard {p : α → Prop} [hp : DecidablePred p] :
xs.flatMap (λ x => List.replicate (length # guard # p x) x) = xs.filter p := by
  simp [guard, failure]; induction xs <;> simp; grind

theorem find?_eq_some_iff_of_at_most_one {p : α → Bool} {x}
(h : ∀ {x y}, x ∈ xs → y ∈ xs → p x → p y → x = y) :
xs.find? p = some x ↔ x ∈ xs ∧ p x := by
  induction xs <;> simp; grind

theorem forall_of_find?_eq_some_imp {p₁ : α → Bool} {p₂ : α → Prop}
(h₁ : ∀ x, xs.find? p₁ = some x → p₂ x) (h₂ : ∀ x, p₂ x ↔ p₁ x = false) :
∀ x ∈ xs, p₂ x := by
  intro x hx
  replace h₂ : p₂ = λ x => p₁ x = false; ext; simp [h₂]
  subst h₂
  specialize h₁ # (xs.find? p₁).getD x
  simp at h₁
  cases h₂ : xs.find? p₁ <;> grind

theorem eq_of_getElem_and_nodup {i j : ℕ} {hi hj}
(h₁ : xs[i]'hi = xs[j]'hj) (h₂ : xs.Nodup) : i = j := by
  rwa [←h₂.getElem_inj_iff]

theorem sum_eq_sum_toFinset [ha₁ : DecidableEq α] [ha₂ : Ring α]
(h : xs.Nodup) : xs.sum = ∑ x ∈ xs.toFinset, x := by
  rw [List.sum_toFinset _ h]; simp

theorem sum_map_eq_sum_toFinset [ha : DecidableEq α] [hb : Ring β] {f : α → β}
(h : xs.Nodup) : (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  rw [List.sum_toFinset _ h]

theorem sum_map_eq_sum_getElem_finset_range [hb : Ring β] {f : α → β} :
(xs.map f).sum = ∑ i ∈ Finset.range xs.length, if h : i < xs.length then f xs[i] else 0 := by
  induction xs using List.reverseRecOn <;> simp
  clear! xs; nm xs x ih
  rw [ih]; clear ih
  simp [Finset.range_add_one]
  rw [add_comm (a := f x)]
  congr 1
  apply Finset.sum_congr rfl
  intro i h₁
  simp at h₁
  simp [h₁]
  omega

@[simp]
theorem take_length_sub_one : xs.take (xs.length - 1) = xs.init := by
  induction xs using List.reverseRecOn <;> simp

@[simp]
theorem length_init : xs.init.length = xs.length - 1 := by
  induction xs using List.reverseRecOn <;> simp

theorem nodup_of_pairwise_lt [ha : LinearOrder α] (h : xs.Pairwise (· < ·)) : xs.Nodup := by
  induction h
  · simp
  clear! xs; nm x xs h₁ h₂ ih
  simp [ih]
  intro hx
  specialize h₁ x hx
  simp at h₁

theorem foldl_apply_comm {f : β → α → β} {z x}
(h : ∀ ⦃x y z⦄, f (f x y) z = f (f x z) y) :
xs.foldl f (f z x) = f (xs.foldl f z) x := by
  induction xs generalizing z; simp; nm y xs ih; simp; rw [←ih, h]

@[simp]
theorem perm_comm_simp : (xs ~ ys ↔ ys ~ xs) ↔ True := by
  simp [perm_comm]

@[simp]
theorem equivalence_perm : Equivalence # @Perm α where
  refl := Perm.refl
  symm := Perm.symm
  trans := Perm.trans

theorem perm_iff_perm_of_left (h : xs ~ ys) : xs ~ zs ↔ ys ~ zs :=
  Equivalence.iff_of_left (by simp) h

theorem perm_iff_perm_of_right (h : xs ~ ys) : zs ~ xs ↔ zs ~ ys :=
  Equivalence.iff_of_right (by simp) h

@[simp]
theorem mergeSort_perm_iff {p} : xs.mergeSort p ~ ys ↔ xs ~ ys := by
  constructor; all_goals intro h; symm at h ⊢; apply h.trans; simp

@[simp]
theorem perm_mergeSort_iff {p} : xs ~ ys.mergeSort p ↔ xs ~ ys := by
  nth_rw 1 [perm_comm]; simp

@[simp]
theorem cons_mergeSort_perm_iff {p x} : x :: xs.mergeSort p ~ ys ↔ x :: xs ~ ys := by
  apply perm_iff_perm_of_left; trans (x :: xs).mergeSort p <;> simp

@[simp]
theorem perm_cons_mergeSort_iff {p y} : xs ~ y :: ys.mergeSort p ↔ xs ~ y :: ys := by
  apply perm_iff_perm_of_right; trans (y :: ys).mergeSort p <;> simp

@[simp]
theorem modify_length_append {f} : (xs ++ ys).modify xs.length f = xs ++ ys.modify 0 f := by
  induction xs; simp; simpa

theorem pairwise_lt_of_pairwise_le [ha : LinearOrder α]
(h₁ : xs.Pairwise (· ≤ ·)) (h₂ : xs.Nodup) : xs.Pairwise (· < ·) := by
  rw [←sortedLT_iff_pairwise]
  rw [←sortedLE_iff_pairwise] at h₁
  exact h₁.sortedLT_of_nodup h₂

theorem eq_and_eq_of_append_cons_eq {xs' ys' x} (h₁ : xs ++ x :: ys = xs' ++ x :: ys')
(h₂ : x ∉ xs) (h₃ : x ∉ xs') : xs = xs' ∧ ys = ys' := by
  induction xs generalizing xs' <;> cases xs' <;> grind

theorem map_modify_eq_of {i} {f : α → α} {g : α → β}
(h : ∀ x ∈ xs, g (f x) = g x) : (xs.modify i f).map g = xs.map g := by
  induction xs generalizing i
  · simp
  clear! xs; nm x xs ih
  simp [modify_cons]
  cases i <;> simp
  · apply h; simp
  nm i
  apply ih
  grind

theorem nodup_take {n} (h : xs.Nodup) : (xs.take n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp
  nm n
  simp
  split_ands
  · contrapose! h₁
    exact mem_of_mem_take h₁
  exact ih h₂

theorem nodup_drop {n} (h : xs.Nodup) : (xs.drop n).Nodup := by
  induction xs generalizing n
  · simp
  clear! xs; nm x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  cases n
  · simp [h₁, h₂]
  nm n
  simp
  exact ih h₂

theorem take_take_append {k} (h : k ≤ xs.length) :
(xs.take k ++ ys).take k = xs.take k := by
  induction k generalizing xs ys
  · simp
  nm k ih
  cases xs
  · simp at h
  nm x xs
  simp
  simp at h
  exact ih h

theorem sum_nonpos [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
(h : ∀ x ∈ xs, x ≤ 0) : xs.sum ≤ 0 := by
  induction xs <;> simp; nm x xs ih
  specialize ih # by grind
  specialize h x (by simp)
  exact add_nonpos h ih

@[simp]
theorem sum_map_neg [ha : Ring α] : (xs.map (-·)).sum = -xs.sum := by
  induction xs; simp; grind

theorem sum_take_le_of_nonneg [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
{k} (h₁ : ∀ x ∈ xs, 0 ≤ x) : (xs.take k).sum ≤ xs.sum := by
  wlog h₂ : k ≤ xs.length with ih
  · push_neg at h₂
    specialize @ih α xs _ _ _ xs.length h₁ (by rfl)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le # le_of_lt h₂
    simp
  nm x y; clear! x y
  choose ys h₃ using show take k xs <+: xs by simp
  rw [←h₃, take_take_append h₂]
  simp
  apply List.sum_nonneg
  intro y hy
  rw [←h₃] at h₁
  apply h₁
  simp [hy]

theorem le_sum_take_of_nonpos [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : AddLeftMono α]
{k} (h₁ : ∀ x ∈ xs, x ≤ 0) : xs.sum ≤ (xs.take k).sum := by
  generalize hy : xs.map (-·) = ys
  replace h₁ : ∀ y ∈ ys, 0 ≤ y
  · subst hy
    simp
    intro y hy
    specialize h₁ _ hy
    simp at h₁
    exact h₁
  replace h₁ := sum_take_le_of_nonneg h₁ (k := k)
  simp [←hy] at h₁
  rw [le_neg] at h₁
  apply h₁.trans
  rw [←map_take, sum_map_neg]
  simp

@[simp]
theorem combinations_zero : xs.combinations 0 = [[]] := rfl

@[simp]
theorem sequence_nil_cons : sequence ([] :: L) = [] := rfl

theorem sequence_cons : sequence (xs :: L) = xs.flatMap (λ x => sequence L |>.map (x :: ·)) := by
  simp [sequence, traverse, List.traverse]; change flatMap _ _ = _; rw [flatMap_map]

@[simp]
theorem sequence_snoc_nil : sequence (L ++ [[]]) = [] := by
  induction L; simp; nm xs L ih; rw [cons_append, sequence_cons, ih]; simp

@[simp]
theorem combinations_nil_succ {n} : ([] : List α).combinations (n + 1) = [] := by
  simp [combinations, replicate_succ]

@[simp]
theorem sequence_nil : sequence ([] : List (List α)) = [[]] := rfl

@[simp]
theorem sequence_eq_nil_iff : sequence L = [] ↔ [] ∈ L := by
  constructor <;> intro h
  · induction L
    · simp at h
    clear! L; nm xs L ih
    simp
    rw [sequence_cons] at h
    cases h₁ : sequence L
    · simp [ih h₁]
    nm ys L₁
    simp [h₁] at h
    left
    rwa [eq_nil_iff_forall_not_mem]
  · rw [mem_iff_append] at h
    obtain ⟨L₁, L₂, rfl⟩ := h
    induction L₁
    · simp
    nm xs L₁ ih
    simp [sequence_cons, ih]

attribute [simp] instSingletonList