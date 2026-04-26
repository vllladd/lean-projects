import Projects.Kolakoski.Defs
import Projects.Temp

namespace KolakoskiSequence

variable {α : Type*}

def f₁ (xs : List ℕ) : List ℕ :=
  xs.zip (.range xs.length) |>.flatMap fun (x, n) =>
  .replicate x # if Even n then 1 else 2

def f₂ (xs : List ℕ) (n k : ℕ) : List ℕ :=
  if k = 0 ∨ n ≤ xs.length then xs
  else f₂ (f₁ xs) n (k - 1)

def f₃ (n : ℕ) : List ℕ :=
  f₂ [1, 2] n n |>.take n

def kolakoski' (n : ℕ) : ℕ :=
  (f₃ # n + 1)[n]!

class KolIter (xs : List ℕ) : Prop where
  h : ∃ n, f₁^[n] [1, 2] = xs

class Diverse (a : ℕ → α) : Prop where
  h : ∀ N, ∃ n, N ≤ n ∧ a N ≠ a n

-- #check 0 #exit

-----

theorem kolIter_iff {xs} : KolIter xs ↔ ∃ n, f₁^[n] [1, 2] = xs :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp, instance]
theorem kolIter_zero : KolIter [1, 2] :=
  ⟨⟨0, rfl⟩⟩

@[simp, instance]
theorem kolIter_succ {xs} [h : KolIter xs] : KolIter (f₁ xs) := by
  rw [kolIter_iff] at h ⊢; obtain ⟨n, rfl⟩ := h
  use n + 1; rw [Function.iterate_succ']; rfl

@[simp, instance]
theorem kolIter_iterate {xs n} [h : KolIter xs] : KolIter (f₁^[n] xs) := by
  induction n; exact h; rw [Function.iterate_succ']; simp

@[simp]
theorem f₂_0 {xs n} : f₂ xs n 0 = xs := by
  simp [f₂]

@[simp]
theorem f₃_0 : f₃ 0 = [] := by
  simp [f₃]

@[simp]
theorem prefix_f₁ {xs} [h : KolIter xs] : xs <+: f₁ xs := by
  obtain ⟨⟨n, rfl⟩⟩ := h
  induction n; decide
  nm n ih
  rw [Function.iterate_succ']
  simp
  obtain ⟨ys, ih⟩ := ih
  rw [←ih]
  conv at ih => rhs; fun; unfold f₁
  conv => rhs; fun; unfold f₁
  simp at ih ⊢
  generalize h₁ : f₁^[n] [1, 2] = xs at ih ⊢
  generalize hg : (fun (x : ℕ × ℕ) => _) = g at ih ⊢
  rw [List.range_add]
  rw [List.zip_append # by simp]
  grind

@[simp]
theorem prefix_iterate_f₁ {xs n} [h : KolIter xs] : xs <+: f₁^[n] xs := by
  obtain ⟨⟨k, rfl⟩⟩ := h
  induction n; rfl
  nm n ih
  apply ih.trans; clear ih
  rw [Function.iterate_succ']
  simp

@[simp]
theorem length_f₁ {xs} : (f₁ xs).length = xs.sum := by
  simp [f₁]

@[simp]
theorem base_prefix_of_kolIter {xs} [h : KolIter xs] : [1, 2] <+: xs := by
  obtain ⟨⟨n, rfl⟩⟩ := h; simp

@[simp]
theorem not_kolIter_nil : ¬KolIter [] := by
  intro h; have h₁ := base_prefix_of_kolIter (h := h); simp at h₁

@[simp]
theorem ne_nil_of_kolIter {xs} [h : KolIter xs] : xs ≠ [] := by
  rintro rfl; simp at h

@[simp]
theorem length_pos_of_kolIter {xs} [h : KolIter xs] : 0 < xs.length := by
  simp [Nat.pos_iff_ne_zero]

@[simp]
theorem one_lt_length_of_kolIter {xs} [h : KolIter xs] : 1 < xs.length := by
  obtain ⟨xs, rfl⟩ : [1, 2] <+: xs <;> simp

@[simp]
theorem getElem_zero_of_kolIter {xs} [h : KolIter xs] : xs[0] = 1 := by
  obtain ⟨xs, rfl⟩ : [1, 2] <+: xs <;> simp

@[simp]
theorem getElem_one_of_kolIter {xs} [h : KolIter xs] : xs[1] = 2 := by
  obtain ⟨xs, rfl⟩ : [1, 2] <+: xs <;> simp

@[simp]
theorem mem_iff_of_kolIter {xs x} [h : KolIter xs] : x ∈ xs ↔ x = 1 ∨ x = 2 := by
  obtain ⟨⟨n, rfl⟩⟩ := h; induction n generalizing x; simp
  nm n ih; rw [Function.iterate_succ']; simp; nth_rw 1 [f₁]; simp
  generalize hx : f₁^[n] [1, 2] = xs at ih ⊢
  have h : KolIter xs; constructor; use n
  constructor; grind; rintro (rfl | rfl)
  · use 1, 0; simp
  · use 2, 1; simp

@[simp]
theorem length_lt_sum_of_kolIter {xs} [h : KolIter xs] : xs.length < xs.sum := by
  apply List.length_lt_sum_of <;> simp

theorem length_iterate_f₁_ge {n} : n ≤ (f₁^[n] [1, 2]).length := by
  induction n; simp; nm n ih; rw [Function.iterate_succ']
  simp; apply lt_of_le_of_lt ih; clear ih; simp

@[simp, instance]
theorem kolIter_f₂ {xs n k} [h : KolIter xs] : KolIter (f₂ xs n k) := by
  induction k using Nat.strong_induction_on generalizing xs
  nm k ih; unfold f₂; split_ifs with h₁; exact h; apply ih; omega

@[simp]
theorem prefix_f₂ {xs n k} [h : KolIter xs] : xs <+: f₂ xs n k := by
  induction k generalizing xs; simp
  nm k ih; unfold f₂; simp; split_ifs with h₁; rfl
  trans f₁ xs; simp; exact ih

@[simp]
theorem length_iterate_f₁_lt_iff {xs n m} [h : KolIter xs] :
(f₁^[n] xs).length < (f₁^[m] xs).length ↔ n < m := by
  wlog h₁ : n < m with ih
  · by_cases h₂ : n = m; grind
    specialize @ih xs m n h (by omega)
    omega
  simp [h₁]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₁; clear h₁
  rw [Nat.add_assoc]
  nth_rw 1 [add_comm]
  rw [Function.iterate_add]
  rw [Function.iterate_succ']; simp
  apply lt_of_lt_of_le (b := f₁^[n] xs |>.sum); simp
  apply List.sum_le_of_prefix; simp

@[simp]
theorem length_iterate_f₁_eq_iff {xs n m} [h : KolIter xs] :
(f₁^[n] xs).length = (f₁^[m] xs).length ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁
  by_contra! h₂
  wlog h₃ : n < m; grind
  contrapose h₁; clear h₁ h₂
  apply ne_of_lt
  simpa

@[simp]
theorem length_iterate_f₁_le_iff {xs n m} [h : KolIter xs] :
(f₁^[n] xs).length ≤ (f₁^[m] xs).length ↔ n ≤ m := by
  simp [le_iff_lt_or_eq]

@[simp]
theorem iterate_f₁_prefix_iterate_iff {xs n m} [h : KolIter xs] :
f₁^[n] xs <+: f₁^[m] xs ↔ n ≤ m := by
  by_cases h₁ : n = m; simp [h₁]
  wlog h₂ : n ≤ m with ih
  · specialize @ih xs m n h (by omega)
    simp [h₂]
    simp [show m ≤ n by omega] at ih
    intro h₃
    have h₄ := congrArg List.length # List.prefix_antisymm h₃ ih
    simp at h₄
    omega
  clear h₁
  simp [h₂]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₂; clear h₂
  rw [add_comm, Function.iterate_add]
  simp

@[simp]
theorem iterate_f₁_eq_iff {xs n m} [h : KolIter xs] :
f₁^[n] xs = f₁^[m] xs ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁
  replace h₁ := congrArg List.length h₁
  simp at h₁
  exact h₁

theorem le_length_f₂ {xs n k} [h : KolIter xs] (h₁ : n ≤ k) : n ≤ (f₂ xs n k).length := by
  replace h₁ : n ≤ xs.length + k; omega
  induction k generalizing xs
  · simpa
  nm k ih
  unfold f₂
  simp
  split_ifs with h₂
  · exact h₂
  push_neg at h₂
  apply ih
  suffices : xs.length < (f₁ xs).length; omega
  simp

@[simp]
theorem le_length_f₂_same {xs n} [h : KolIter xs] : n ≤ (f₂ xs n n).length := by
  apply le_length_f₂; rfl

@[simp]
theorem length_f₃ {n} : (f₃ n).length = n := by
  simp [f₃]

@[simp]
theorem f₃_succ_getElem! {n} : (f₃ # n + 1)[n]! = (f₃ # n + 1)[n] := by
  simp

@[simp]
theorem f₃_eq_iff {n m} : f₃ n = f₃ m ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h
  simp [f₃] at h
  replace h := congrArg List.length h
  simp at h
  exact h

theorem kolIter_prefix_or_prefix (xs ys : List ℕ)
[hx : KolIter xs] [hy : KolIter ys] : xs <+: ys ∨ ys <+: xs := by
  obtain ⟨⟨n, rfl⟩⟩ := hx; obtain ⟨⟨m, rfl⟩⟩ := hy; simp

@[simp]
theorem f₃_prefix_iff_le {n m} : f₃ n <+: f₃ m ↔ n ≤ m := by
  wlog h : n ≤ m with ih
  · by_cases h₁ : m = n; simp [h₁]
    specialize @ih m n (by omega)
    simp [h]
    simp [show m ≤ n by omega] at ih
    contrapose! h₁
    have h₂ : f₃ n = f₃ m; exact List.prefix_antisymm h₁ ih
    simp at h₂; exact h₂.symm
  simp [h]
  simp [f₃]
  obtain h₁ | h₁ := kolIter_prefix_or_prefix (f₂ [1, 2] n n) (f₂ [1, 2] m m); grind
  obtain ⟨xs, h₁⟩ := h₁
  rw [←h₁]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h; clear h
  nth_rw 3 [hk]
  rw [List.take_add]
  rw [List.take_append]
  simp; trans []; on_goal 2 => simp
  simp; left
  simp [Nat.sub_eq_zero_iff_le]
  trans m; omega; simp

@[simp]
theorem f₁_one : f₃ 1 = [1] := by
  simp [f₃, f₂]

@[simp]
theorem f₁_two : f₃ 2 = [1, 2] := by
  simp [f₃, f₂]

@[simp]
theorem mem_f₃_iff {n x} : x ∈ f₃ n ↔ (x = 1 ∧ 1 ≤ n) ∨ (x = 2 ∧ 2 ≤ n) := by
  constructor
  · intro h
    cases n
    · simp at h
    nm n; cases n
    · simp at h
      simp [h]
    nm n
    simp [f₃] at h
    replace h := List.mem_of_mem_take h
    simp at h
    simpa
  rw [f₃, List.mem_take_iff_getElem]
  rintro (⟨rfl, hn⟩ | ⟨rfl, hn⟩)
  · use 0; simp; omega
  · use 1; simp; omega

@[simp]
theorem range_kolakoski' : Set.range kolakoski' = {1, 2} := by
  ext n
  simp
  unfold kolakoski'
  simp
  constructor
  · rintro ⟨i, h⟩
    have h₁ : n ∈ f₃ (i + 1); grind
    simp at h₁
    omega
  rintro (rfl | rfl)
  · use 0; simp
  · use 1; simp

theorem diverse_iff {a : ℕ → α} : Diverse a ↔ ∀ N, ∃ n, N ≤ n ∧ a N ≠ a n :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]
theorem kolakoski'_zero : kolakoski' 0 = 1 := by
  simp [kolakoski']

@[simp]
theorem kolakoski'_one : kolakoski' 1 = 2 := by
  simp [kolakoski']

theorem exi_f₃_prefix_kolIter {i} : ∃ xs, KolIter xs ∧ f₃ i <+: xs := by
  use f₂ [1, 2] i i, inferInstance; simp [f₃]

-- #check 0 #exit

-- theorem le_two_replicate_of_infix_kolIter {xs c x} [H : KolIter xs]
-- (h : .replicate c x <:+: xs) : c ≤ 2 := by
--   obtain ⟨⟨n, rfl⟩⟩ := H
--   obtain ⟨xs, ys, h⟩ := h
--   
--   by_contra hc'
--   wlog hc : c = 3 with ih
--   ·
--     have h₁ : 3 ≤ c; omega
--     obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h₁
--     specialize @ih 3 x n xs (.replicate c x ++ ys)
--     grind
--   clear hc'
--   subst hc
--   
--   induction n generalizing xs ys x
--   ·
--     replace h := congrArg List.length h
--     simp at h
--     omega
--   nm n ih
--   
--   rw [Function.iterate_succ'] at h; simp at h ih
--   contrapose! ih; clear ih
--   
--   generalize h₁ : f₁^[n] [1, 2] = zs at h ⊢
--   have H : KolIter zs; simp [←h₁]
--   
--   have h' := h
--   simp [f₁] at h
--   
--   rw [List.ext_getElem_iff] at h
--   simp at h
--   choose h₂ h₃ using h
--   
--   simp [List.flatMap_def, List.getElem_flatten] at h₃
--   
--   replace h₃ := forall_spec (xs.length + ·) h₃
--   simp at h₃
--   
--   have H₁ : ∀ y, zs.partialSums.findIdx (fun x => xs.length + y < x) ≠ 0
--   ·
--     sorry
--   
--   -- have H₁ := h₃ xs.length (by omega) (by omega)
--   -- simp at H₁

-- #check 0 #exit

-- theorem le_two_replicate_of_infix_f₃ {i c x} (h₁ : .replicate c x <:+: f₃ i) : c ≤ 2 := by
--   obtain ⟨xs, H, h₂⟩ := @exi_f₃_prefix_kolIter i
--   have h₃ : .replicate c x <:+: xs; grind
--   exact le_two_replicate_of_infix_kolIter h₃

-- @[simp, instance]
-- theorem diverse_kolakoski' : Diverse kolakoski' := by
--   constructor; intro N
--   by_cases h₁ : kolakoski' (N + 1) ≠ kolakoski' N
--   ·
--     use N + 1; grind
--   push_neg at h₁
--   use N + 2, by omega
--   symm
--   intro h₂

-- #check 0 #exit

-- @[simp]
-- theorem runs_zero {xs : ℕ → α} : runs xs 0 = 0 := by
--   simp [runs]
--   unfold setToSeq
--   simp

-- theorem runs_kolakoski'_succ_sub {n} :
-- runs kolakoski' (n + 1) - runs kolakoski' n = kolakoski' n := by
--   induction n
--   ·
--     simp

-- #check 0 #exit

-- theorem lengths_runs_kolakoski' : lengths (runs kolakoski') = kolakoski' := by
--   ext n
--   simp [lengths]

-- #check 0 #exit

-- theorem isKolakoski_kolakoski' : IsKolakoski kolakoski' := by
--   constructor; simp

-- #check 0 #exit

-- theorem f₃_prefix_kolakoski

-- There are actually two sequences that fit this definition
-- with their only difference being a 1 at the beginning

-- Its first 16 terms are:
-- 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, ...