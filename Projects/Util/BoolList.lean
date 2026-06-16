import Projects.Util.Finset

namespace List

@[simp]
def incBoolList' (xs : List Bool) (c : Bool) : List Bool :=
  match xs with
  | [] => []
  | x :: xs => (!(x == c)) :: incBoolList' xs (x && c)

def incBoolList (xs : List Bool) : List Bool :=
  incBoolList' xs true

@[simp]
def decideBoolList' (p : List Bool → Bool) (xs : List Bool) (n : ℕ) : Bool :=
  bif !p xs then false else match n with
  | 0 => true
  | n + 1 => decideBoolList' p xs.incBoolList n

def decideBoolList (p : List Bool → Bool) (n : ℕ) : Bool :=
  decideBoolList' p (List.replicate n false) (2 ^ n)

@[simp]
def BoolListFinset' (xs : List Bool) (n : ℕ) : Finset (List Bool) :=
  insert xs # match n with
  | 0 => ∅
  | n + 1 => BoolListFinset' xs.incBoolList n

def BoolListFinset (n : ℕ) : Finset (List Bool) :=
  BoolListFinset' (List.replicate n false) (2 ^ n)

-----

@[simp]
theorem length_incBoolList' {xs : List Bool} {c} : (xs.incBoolList' c).length = xs.length := by
  induction xs generalizing c; rfl; nm x xs ih; simp [ih]

@[simp]
theorem length_incBoolList {xs : List Bool} : xs.incBoolList.length = xs.length :=
  length_incBoolList'

theorem decideBoolList_of {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ}
(h : ∀ (xs : List Bool), xs.length = n → p xs) : decideBoolList p n := by
  unfold decideBoolList
  generalize h₁ : replicate n false = xs
  replace h₁ : xs.length = n; simp [←h₁]
  generalize 2 ^ n = k
  induction k generalizing xs <;> simp
  · exact h _ h₁
  nm k hk
  use h _ h₁
  rw [hk]
  simpa

@[simp]
theorem incBoolList_nil : [].incBoolList = [] := rfl

@[simp]
theorem decideBoolList_zero {p : List Bool → Prop} [hp : DecidablePred p] :
decideBoolList p 0 = decide (p []) := by
  simp [decideBoolList]

@[simp]
theorem BoolListFinset_zero : BoolListFinset 0 = {[]} := rfl

theorem of_mem_BoolListFinset {xs n} (h : xs ∈ BoolListFinset n) : xs.length = n := by
  unfold BoolListFinset at h
  generalize 2 ^ n = k at h
  generalize h₁ : replicate n false = zs at h
  replace h₁ : zs.length = n; simp [←h₁]
  induction k generalizing zs
  · simp at h
    rwa [h]
  nm k ih
  simp at h
  rcases h with rfl | h
  · exact h₁
  apply ih _ h
  simpa

theorem self_mem_BoolListFinset' {xs : List Bool} {n} : xs ∈ xs.BoolListFinset' n := by
  cases n <;> simp

theorem BoolListFinset'_add {xs : List Bool} {n k} : xs.BoolListFinset' (n + k) =
xs.BoolListFinset' n ∪ (incBoolList^[n] xs).BoolListFinset' k := by
  induction n generalizing xs k
  · simp [self_mem_BoolListFinset']
  nm n ih; simp [Nat.add_one_add, ih]

theorem mem_BoolListFinset'_iff_exi_iter {zs xs : List Bool} {n} :
xs ∈ zs.BoolListFinset' n ↔ ∃ k ≤ n, xs = incBoolList^[k] zs := by
  induction n generalizing zs <;> simp
  nm n ih
  rw [ih]; clear ih
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · use 0
      simp
    use k + 1
    simp [hk]
  · rintro ⟨k, hk, rfl⟩
    cases k <;> simp
    nm k; right
    simp at hk
    use k

theorem incBoolList'_prefix_of_prefix {xs ys : List Bool} {c}
(h : xs <+: ys) : xs.incBoolList' c <+: ys.incBoolList' c := by
  induction xs generalizing ys c <;> simp
  nm x xs ih
  cases ys
  · simp at h
  nm y ys
  simp at h
  rcases h with ⟨rfl, h⟩
  simp [ih h]

theorem incBoolList_prefix_of_prefix {xs ys : List Bool}
(h : xs <+: ys) : xs.incBoolList <+: ys.incBoolList :=
  incBoolList'_prefix_of_prefix h

theorem iter_incBoolList_prefix_of_prefix {xs ys : List Bool} {k}
(h : xs <+: ys) : incBoolList^[k] xs <+: incBoolList^[k] ys := by
  induction k generalizing xs ys
  · simpa
  nm k ih
  rw [Function.iterate_succ']
  exact incBoolList_prefix_of_prefix # ih h

@[simp]
theorem incBoolList'_false {xs : List Bool} : xs.incBoolList' false = xs := by
  induction xs <;> simp_all

@[simp]
theorem incBoolList_false_cons {xs : List Bool} :
(false :: xs).incBoolList = true :: xs := by
  simp [incBoolList]

@[simp]
theorem incBoolList_true_cons {xs : List Bool} :
(true :: xs).incBoolList = false :: xs.incBoolList := by
  simp [incBoolList]

@[simp]
theorem incBoolList_incBoolList_cons {x : Bool} {xs : List Bool} :
(x :: xs).incBoolList.incBoolList = x :: xs.incBoolList := by
  cases x <;> simp

@[simp]
theorem iter_incBoolList_cons_mul_two {x : Bool} {xs : List Bool} {k} :
incBoolList^[k * 2] (x :: xs) = x :: incBoolList^[k] xs := by
  induction k generalizing xs
  · simp
  nm k ih
  simp_rw [Nat.succ_mul]
  simp [ih]

@[simp]
theorem iter_incBoolList_nil {k} : incBoolList^[k] [] = [] := by
  induction k <;> simp_all

@[simp]
theorem iter_incBoolList_two_pow {xs : List Bool} {k} :
incBoolList^[2 ^ k] xs = xs.take k ++ (xs.drop k).incBoolList := by
  induction k generalizing xs
  · simp
  nm n ih
  cases xs; simp
  nm x xs
  simp_rw [Nat.pow_succ, iter_incBoolList_cons_mul_two, take_succ_cons, drop_succ_cons]
  simp [ih]

theorem mem_BoolListFinset_of {xs n} (h : xs.length = n) : xs ∈ BoolListFinset n := by
  rw [BoolListFinset, mem_BoolListFinset'_iff_exi_iter]
  induction xs generalizing n
  · simp at h; simp [←h, Nat.le_one_iff]
  nm x xs ih
  simp at h
  cases n <;> simp at h; nm n
  specialize ih h
  choose k hk ih using ih
  rw [List.replicate_succ]
  generalize h₁ : replicate n false = zs at ih ⊢
  replace h₁ : zs.length = n; simp [←h₁]
  cases x
  ·
    use k * 2, by omega
    simpa
  ·
    rw [le_iff_eq_or_lt] at hk
    rcases hk with rfl | hk
    · rw [iter_incBoolList_two_pow] at ih
      rw [drop_eq_nil_of_le # by omega] at ih
      simp at ih
      rw [take_eq_self_of_le # by omega] at ih
      subst ih
      use 1, Nat.one_le_two_pow
      simp
    use k * 2 + 1, by omega
    simpa

theorem mem_BoolListFinset_iff_length_eq {xs n} : xs ∈ BoolListFinset n ↔ xs.length = n :=
  ⟨of_mem_BoolListFinset, mem_BoolListFinset_of⟩

theorem mem_BoolListFinset_iff_exi_iter {xs : List Bool} {n} :
xs ∈ BoolListFinset n ↔ ∃ k ≤ (2 ^ n), xs = incBoolList^[k] (List.replicate n false) :=
  mem_BoolListFinset'_iff_exi_iter

theorem decideBoolList_iff_forall_mem_BoolListFinset {p : List Bool → Prop} [hp : DecidablePred p]
{n : ℕ} : decideBoolList p n ↔ ∀ xs, xs ∈ BoolListFinset n → p xs := by
  simp [mem_BoolListFinset_iff_exi_iter]
  unfold decideBoolList
  generalize replicate n false = zs at ⊢
  generalize 2 ^ n = m at ⊢
  induction m generalizing zs
  · simp
  nm m ih
  simp
  rw [ih]; clear ih
  constructor
  · rintro ⟨h₁, h₂⟩ xs k hk rfl
    cases k; simpa; nm k
    simp at hk
    exact h₂ _ _ hk rfl
  · intro h
    use h zs 0 (by simp) rfl
    intro xs k hk
    exact @h xs (k + 1) (by omega)

theorem of_decideBoolList {p : List Bool → Prop} [hp : DecidablePred p] {xs : List Bool} {n : ℕ}
(hn : xs.length = n) (h : decideBoolList p n) : p xs := by
  simp [decideBoolList_iff_forall_mem_BoolListFinset, mem_BoolListFinset_iff_length_eq] at h
  exact h _ hn

theorem decideBoolList_iff {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
decideBoolList p n ↔ ∀ (xs : List Bool), xs.length = n → p xs :=
  ⟨λ h₁ _ h₂ => of_decideBoolList h₂ h₁, decideBoolList_of⟩

instance {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
Decidable # ∀ (xs : List Bool), xs.length = n → p xs :=
  decidable_of_bool (decideBoolList p n) decideBoolList_iff