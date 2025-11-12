import AP.Util.Finset

namespace List

@[simp]
def incListBool' (xs : List Bool) (c : Bool) : List Bool :=
  match xs with
  | [] => []
  | x :: xs => (!(x == c)) :: incListBool' xs (x && c)

def incListBool (xs : List Bool) : List Bool :=
  incListBool' xs true

@[simp]
def decideListBool' (p : List Bool → Bool) (xs : List Bool) (n : ℕ) : Bool :=
  bif !p xs then false else match n with
  | 0 => true
  | n + 1 => decideListBool' p xs.incListBool n

def decideListBool (p : List Bool → Bool) (n : ℕ) : Bool :=
  decideListBool' p (List.replicate n false) (2 ^ n)

@[simp]
def listBoolFinset' (xs : List Bool) (n : ℕ) : Finset (List Bool) :=
  insert xs # match n with
  | 0 => ∅
  | n + 1 => listBoolFinset' xs.incListBool n

def listBoolFinset (n : ℕ) : Finset (List Bool) :=
  listBoolFinset' (List.replicate n false) (2 ^ n)

-----

@[simp]
theorem length_incListBool' {xs : List Bool} {c} : (xs.incListBool' c).length = xs.length := by
  induction xs generalizing c; rfl; nm x xs ih; simp [ih]

@[simp]
theorem length_incListBool {xs : List Bool} : xs.incListBool.length = xs.length :=
  length_incListBool'

theorem decideListBool_of {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ}
(h : ∀ (xs : List Bool), xs.length = n → p xs) : decideListBool p n := by
  unfold decideListBool
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
theorem incListBool_nil : [].incListBool = [] := rfl

@[simp]
theorem decideListBool_zero {p : List Bool → Prop} [hp : DecidablePred p] :
decideListBool p 0 = decide (p []) := by
  simp [decideListBool]

@[simp]
theorem listBoolFinset_zero : listBoolFinset 0 = {[]} := rfl

theorem of_mem_listBoolFinset {xs n} (h : xs ∈ listBoolFinset n) : xs.length = n := by
  unfold listBoolFinset at h
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

theorem self_mem_listBoolFinset' {xs : List Bool} {n} : xs ∈ xs.listBoolFinset' n := by
  cases n <;> simp

theorem listBoolFinset'_add {xs : List Bool} {n k} : xs.listBoolFinset' (n + k) =
xs.listBoolFinset' n ∪ (incListBool^[n] xs).listBoolFinset' k := by
  induction n generalizing xs k
  · simp [self_mem_listBoolFinset']
  nm n ih; simp [Nat.add_one_add, ih]

theorem mem_listBoolFinset'_iff_exi_iter {zs xs : List Bool} {n} :
xs ∈ zs.listBoolFinset' n ↔ ∃ k ≤ n, xs = incListBool^[k] zs := by
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

theorem incListBool'_prefix_of_prefix {xs ys : List Bool} {c}
(h : xs <+: ys) : xs.incListBool' c <+: ys.incListBool' c := by
  induction xs generalizing ys c <;> simp
  nm x xs ih
  cases ys
  · simp at h
  nm y ys
  simp at h
  rcases h with ⟨rfl, h⟩
  simp [ih h]

theorem incListBool_prefix_of_prefix {xs ys : List Bool}
(h : xs <+: ys) : xs.incListBool <+: ys.incListBool :=
  incListBool'_prefix_of_prefix h

theorem iter_incListBool_prefix_of_prefix {xs ys : List Bool} {k}
(h : xs <+: ys) : incListBool^[k] xs <+: incListBool^[k] ys := by
  induction k generalizing xs ys
  · simpa
  nm k ih
  rw [Function.iterate_succ']
  exact incListBool_prefix_of_prefix # ih h

@[simp]
theorem incListBool'_false {xs : List Bool} : xs.incListBool' false = xs := by
  induction xs <;> simp_all

@[simp]
theorem incListBool_false_cons {xs : List Bool} :
(false :: xs).incListBool = true :: xs := by
  simp [incListBool]

@[simp]
theorem incListBool_true_cons {xs : List Bool} :
(true :: xs).incListBool = false :: xs.incListBool := by
  simp [incListBool]

@[simp]
theorem incListBool_incListBool_cons {x : Bool} {xs : List Bool} :
(x :: xs).incListBool.incListBool = x :: xs.incListBool := by
  cases x <;> simp

@[simp]
theorem iter_incListBool_cons_mul_two {x : Bool} {xs : List Bool} {k} :
incListBool^[k * 2] (x :: xs) = x :: incListBool^[k] xs := by
  induction k generalizing xs
  · simp
  nm k ih
  simp_rw [Nat.succ_mul]
  simp [ih]

@[simp]
theorem iter_incListBool_nil {k} : incListBool^[k] [] = [] := by
  induction k <;> simp_all

@[simp]
theorem iter_incListBool_two_pow {xs : List Bool} {k} :
incListBool^[2 ^ k] xs = xs.take k ++ (xs.drop k).incListBool := by
  induction k generalizing xs
  · simp
  nm n ih
  cases xs; simp
  nm x xs
  simp_rw [Nat.pow_succ, iter_incListBool_cons_mul_two, take_succ_cons, drop_succ_cons]
  simp [ih]

theorem mem_listBoolFinset_of {xs n} (h : xs.length = n) : xs ∈ listBoolFinset n := by
  rw [listBoolFinset, mem_listBoolFinset'_iff_exi_iter]
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
    · rw [iter_incListBool_two_pow] at ih
      rw [drop_eq_nil_of_le # by omega] at ih
      simp at ih
      rw [take_eq_self_of_le # by omega] at ih
      subst ih
      use 1, Nat.one_le_two_pow
      simp
    use k * 2 + 1, by omega
    simpa

theorem mem_listBoolFinset_iff_length_eq {xs n} : xs ∈ listBoolFinset n ↔ xs.length = n :=
  ⟨of_mem_listBoolFinset, mem_listBoolFinset_of⟩

theorem mem_listBoolFinset_iff_exi_iter {xs : List Bool} {n} :
xs ∈ listBoolFinset n ↔ ∃ k ≤ (2 ^ n), xs = incListBool^[k] (List.replicate n false) :=
  mem_listBoolFinset'_iff_exi_iter

theorem decideListBool_iff_forall_mem_listBoolFinset {p : List Bool → Prop} [hp : DecidablePred p]
{n : ℕ} : decideListBool p n ↔ ∀ xs, xs ∈ listBoolFinset n → p xs := by
  simp [mem_listBoolFinset_iff_exi_iter]
  unfold decideListBool
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

theorem of_decideListBool {p : List Bool → Prop} [hp : DecidablePred p] {xs : List Bool} {n : ℕ}
(hn : xs.length = n) (h : decideListBool p n) : p xs := by
  simp [decideListBool_iff_forall_mem_listBoolFinset, mem_listBoolFinset_iff_length_eq] at h
  exact h _ hn

theorem decideListBool_iff {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
decideListBool p n ↔ ∀ (xs : List Bool), xs.length = n → p xs :=
  ⟨λ h₁ _ h₂ => of_decideListBool h₂ h₁, decideListBool_of⟩

instance {p : List Bool → Prop} [hp : DecidablePred p] {n : ℕ} :
Decidable # ∀ (xs : List Bool), xs.length = n → p xs :=
  decidable_of_bool (decideListBool p n) decideListBool_iff