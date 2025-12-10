import AP.RealAnalysis.ConditionalConvergence

namespace RealAnalysis

def Rment (σ : ℕ → ℕ) : Prop :=
  σ.Bijective

noncomputable
def rinv (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon # λ k => σ k = n

noncomputable
def mkRmentList (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n + 1 =>
    let is := mkRmentList a L n
    -- consume the first unconsumed element `x` of `a+`
    let i := Nat.findRaw # λ i => i ∉ is ∧ 0 ≤ a i
    -- consume the first unconsumed element `y` of `a-`
    let j := Nat.findRaw # λ j => j ∉ is ∧ a j < 0
    -- add `x + y` to the current sum
    let is := is ++ [i, j]
    -- let the current sum be `s`
    let s := ∑ i ∈ is.toFinset, a i
    -- if `s <= L - 1 / (n + 2)`
    is ++ if s ≤ L - 1 / (n + 2) then
      -- let `N` be the index in `a+` after which all elements are smaller than `1 / (n + 2)`
      --   and all elements are unconsumed
      let N := Nat.findRaw # λ N => 0 ≤ a N ∧ ∀ n, N ≤ n → 0 ≤ a n → n ∉ is ∧ a n < 1 / (n + 2)
      -- consume the shortest prefix of `a+` starting from `N`
      --   whose sum is larger than `L - 1 / (n + 2)`
      let f (k : ℕ) := List.range k |>.map (N + ·) |>.filter (0 ≤ a ·)
      f # Nat.findRaw # λ k => L - 1 / (n + 2) < (f k |>.map a |>.sum)
      -- the new total sum will be between `L - 1 / (n + 2)` and `L` inclusively
    else if L + 1 / (n + 2) ≤ s then
      -- let `N` be the index in `a-` after which all elements are larger than `-1 / (n + 2)`
      --   and all elements are unconsumed
      let N := Nat.findRaw # λ N => a N < 0 ∧ ∀ n, N ≤ n → a n < 0 → n ∉ is ∧ -1 / (n + 2) < a n
      -- consume the shortest prefix of `a-` starting from `N`
      --   whose sum is smaller than `L + 1 / (n + 2)`
      let f (k : ℕ) := List.range k |>.map (N + ·) |>.filter (a · < 0)
      f # Nat.findRaw # λ k => (f k |>.map a |>.sum) < L + 1 / (n + 2)
      -- the new total sum will be between `L` and `L + 1 / (n + 2)` inclusively
    else []
    -- we now have `|s - L| < 1 / (n + 1)`

noncomputable
def mkRment (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  (mkRmentList a L (n + 1))[n]!

-----

theorem rment_eq_iff {σ n m} (h : Rment σ) : σ n = σ m ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  intro h₁; exact h.1 h₁

theorem rinv_cancel_left {σ n} (h : Rment σ) : rinv σ (σ n) = n := by
  simp [rinv, rment_eq_iff h]

theorem rinv_cancel_right {σ n} (h : Rment σ) : σ (rinv σ n) = n := by
  unfold rinv
  apply Classical.epsilon_spec (p := λ k => σ k = n)
  apply h.2

theorem rment_rinv {σ} (h : Rment σ) : Rment (rinv σ) := by
  constructor
  · intro n m h₁
    replace h₁ := congrArg σ h₁
    simp_rw [rinv_cancel_right h] at h₁
    exact h₁
  · intro n
    use σ n
    rw [rinv_cancel_left h]

theorem tendsTo_rment_of {a σ L} (h₁ : Rment σ)
(h₂ : tendsTo a L) : tendsTo (a # σ ·) L := by
  intro e he
  dsimp
  specialize h₂ e he
  choose N h₂ using h₂
  dsimp at h₂
  use ∑ i ∈ Finset.range N, rinv σ i + 1
  intro n hn
  apply h₂; clear h₂
  by_contra! h₃
  have h₄ : rinv σ (σ n) ≤ ∑ i ∈ Finset.range N, rinv σ i
  · apply Finset.le_sum_of_mem <;> simp [h₃]
  rw [rinv_cancel_left h₁] at h₄
  omega

theorem tendsTo_rment_iff {a σ L} (h₁ : Rment σ) :
tendsTo (a # σ ·) L ↔ tendsTo a L := by
  symm; use tendsTo_rment_of h₁
  intro h₂
  replace h₂ := tendsTo_rment_of (rment_rinv h₁) h₂
  simp_rw [rinv_cancel_right h₁] at h₂
  exact h₂

theorem converges_rment_of {a σ} (h₁ : Rment σ)
(h₂ : converges a) : converges (a # σ ·) := by
  choose L h₂ using h₂; use L, tendsTo_rment_of h₁ h₂

theorem converges_rment_iff {a σ} (h₁ : Rment σ) :
converges (a # σ ·) ↔ converges a := by
  apply exists_congr; simp [tendsTo_rment_iff h₁]

theorem subseq_nat_eq_subseq_iff {σ n m} (h : Subseq σ) : σ n = σ m ↔ n = m := by
  by_cases h₁ : n < m
  · simp [ne_of_lt h₁]
    apply ne_of_lt
    apply h
    exact h₁
  push_neg at h₁
  rw [le_iff_eq_or_lt] at h₁
  rcases h₁ with rfl | h₁
  · simp
  simp [ne_symm' # ne_of_lt h₁]
  apply ne_of_gt
  apply h
  exact h₁

theorem subseq_nat_lt_subseq_iff {σ n m} (h : Subseq σ) : σ n < σ m ↔ n < m := by
  by_cases h₁ : n = m; simp [h₁]
  simp [lt_iff_le_and_ne, subseq_nat_le_subseq_iff h, subseq_nat_eq_subseq_iff h, h₁]

theorem subseq_nat_succ_le {σ n} (h : Subseq σ) : σ n + 1 ≤ σ (n + 1) := by
  simp [Nat.add_one_le_iff, subseq_nat_lt_subseq_iff h]

theorem subseq_nat_eq_succ_of_subseq_eq_succ {σ n m}
(h₁ : Subseq σ) (h₂ : σ n = σ m + 1) : n = m + 1 := by
  have h₃ : m < n
  · apply lt_of_le_of_ne
    · contrapose! h₂
      apply ne_of_lt
      rw [Nat.lt_succ]
      apply le_of_lt
      apply h₁
      exact h₂
    rintro rfl
    simp at h₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₃; clear h₃
  suffices : n = 0; linarith
  contrapose! h₂
  apply ne_of_gt
  cases n; simp at h₂; clear h₂
  nm n
  suffices h : σ m + 1 < σ (m + n + 2); ring_nf at h ⊢; exact h
  apply lt_of_le_of_lt # subseq_nat_succ_le h₁
  apply h₁
  omega

theorem subseq_card_filter_range_eq {a : ℕ → ℝ} {p : ℝ → Prop} {σ : ℕ → ℕ} {n k : ℕ}
[hp : DecidablePred p] (h₁ : Subseq σ) (h₂ : ∀ n, p (a n) ↔ ∃ k, σ k = n)
(h₃ : σ k = n) : {k ∈ Finset.range n | p (a k)}.card = k := by
  induction k generalizing n
  · simp
    simp [h₂]
    rintro k hk r rfl
    subst h₃
    simp [subseq_nat_lt_subseq_iff h₁] at hk
  nm k ih
  have h₄ : σ k ≤ n
  · simp [←h₃, subseq_nat_le_subseq_iff h₁]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₄; clear h₄
  specialize ih rfl
  rw [Finset.card_filter_range_add, ih]; clear ih
  simp
  rw [Finset.card_eq_one_iff_exiu]
  use σ k
  simp
  split_ands
  · rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp [subseq_nat_eq_subseq_iff h₁] at h₃
  · rw [h₂]
    use k
  intro r h₄ h₅ h₆
  rw [←h₃] at h₅
  rw [h₂] at h₆
  obtain ⟨r, rfl⟩ := h₆
  rw [subseq_nat_le_subseq_iff h₁] at h₄
  rw [subseq_nat_lt_subseq_iff h₁] at h₅
  rw [subseq_nat_eq_subseq_iff h₁]
  omega

theorem exi_fn_series_of_subseq_cover {a : ℕ → ℝ} {p : ℝ → Prop} {σ₁ σ₂ : ℕ → ℕ}
{F : ℝ → ℝ}
(h₁ : Subseq σ₁) (h₂ : Subseq σ₂)
(h₃ : ∀ n, p (a n) ↔ ∃ k, σ₁ k = n)
(h₄ : ∀ n, ¬p (a n) ↔ ∃ k, σ₂ k = n) :
∃ (f g : ℕ → ℕ), (∀ n, f n + g n = n) ∧
(∀ i j, i ≤ j → f i ≤ f j) ∧ (∀ i j, i ≤ j → g i ≤ g j) ∧
(Infp a p → ∀ n, ∃ k, n ≤ f k) ∧ (Infp a (¬p ·) → ∀ n, ∃ k, n ≤ g k) ∧
(∀ n, series (F # a ·) n = series (F # a # σ₁ ·) (f n) + series (F # a # σ₂ ·) (g n)) := by
  classical
  use λ n => Finset.range n |>.filter (λ n => p (a n)) |>.card
  use λ n => Finset.range n |>.filter (λ n => ¬p (a n)) |>.card
  split_ands
  · intro n; convert Finset.card_filter_add_card_filter_not; simp
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · exact λ _ _ => Finset.card_filter_range_le_of_le
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | p (a i)}.card; linarith
    simp
    use k + r
    simpa
  · intro H n
    induction n; simp; nm n ih
    choose k ih using ih
    specialize H k
    choose r h₆ h₇ using H
    use r + 1
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
    dsimp
    rw [add_assoc, Finset.card_filter_range_add]
    suffices : 1 ≤ {i ∈ Finset.Ico k (k + (r + 1)) | ¬p (a i)}.card; linarith
    simp
    use k + r
    simpa
  intro n
  induction n
  · simp
  nm n ih
  simp_rw [series_succ, Finset.range_add_one, Finset.filter_insert]
  by_cases h : p (a n) <;> simp [h]
  · rw [series_succ]
    rw [h₃] at h
    choose k h using h
    suffices : F (a # σ₁ {n ∈ Finset.range n | p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq h₁ h₃ h
  · rw [series_succ]
    rw [h₄] at h
    choose k h using h
    suffices : F (a # σ₂ {n ∈ Finset.range n | ¬p (a n)}.card) = F (a n)
    · linarith
    conv_rhs => rw [←h]
    congr
    exact subseq_card_filter_range_eq (p := (¬p ·)) h₂ h₄ h

@[simp]
theorem le_length_mkRmentList {a L n} : n ≤ (mkRmentList a L n).length := by
  induction n; simp; rw [mkRmentList]; grind

theorem mkRmentList_prefix {a L k n} (h : k ≤ n) : mkRmentList a L k <+: mkRmentList a L n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n; rfl; rw [Nat.add_succ, mkRmentList]; grind

theorem getElem!_mkRmentList_eq_getElem {a L n k} (h : k < n) :
(mkRmentList a L n)[k]! = (mkRmentList a L n)[k]'(lt_of_lt_of_le h # by simp) := by
  rw [List.getElem!_eq_getElem]

@[simp]
theorem lt_length_mkRmentList_succ {a L n} : n < (mkRmentList a L (n + 1)).length := by
  apply lt_of_lt_of_le (b := n + 1) <;> simp

theorem mkRment_eq_getElem {a L n} :
mkRment a L n = (mkRmentList a L (n + 1))[n]'(by simp) := by
  rw [mkRment, getElem!_mkRmentList_eq_getElem]; simp

theorem getElem_mkRmentList_eq_of_lt {a L n m k} (h₁ : k < n) (h₂ : k < m) :
(mkRmentList a L n)[k]'(lt_of_lt_of_le h₁ # by simp) =
(mkRmentList a L m)[k]'(lt_of_lt_of_le h₂ # by simp) := by
  wlog h₃ : n < m; grind; apply List.IsPrefix.getElem # mkRmentList_prefix # le_of_lt h₃

theorem getElem!_mkRmentList_eq_of_lt {a L n m k} (h₁ : k < n) (h₂ : k < m) :
(mkRmentList a L n)[k]! = (mkRmentList a L m)[k]! := by
  rw [getElem!_mkRmentList_eq_getElem h₁, getElem!_mkRmentList_eq_getElem h₂]
  exact getElem_mkRmentList_eq_of_lt h₁ h₂

@[simp]
theorem mem_mkRmentList_succ {a L n} : n ∈ mkRmentList a L (n + 1) := by
  induction n using Nat.strong_induction_on
  nm n ih
  by_cases h₁ : n ∈ mkRmentList a L n
  · apply List.IsPrefix.mem h₁
    apply mkRmentList_prefix
    simp
  unfold mkRmentList
  generalize h_is : mkRmentList a L n = is at h₁ ⊢
  generalize hi : Nat.findRaw (λ i => i ∉ is ∧ 0 ≤ a i) = i
  generalize hj : Nat.findRaw (λ j => j ∉ is ∧ a j < 0) = j
  apply List.mem_append_left
  apply List.mem_append_right
  rw [hi, hj]
  simp
  have h₂ : ∀ k < n, k ∈ is
  ·
    intro k hk
    specialize ih k hk
    apply List.IsPrefix.mem ih
    rw [←h_is]
    apply mkRmentList_prefix
    omega
  by_cases h₃ : 0 ≤ a n
  · rw [Nat.findRaw_eq_iff, if_pos ⟨n, by grind⟩] at hi; grind
  · rw [Nat.findRaw_eq_iff, if_pos ⟨n, by grind⟩] at hj; grind

-- theorem ConvCond.tendsTo_series : tendsTo (series a) := H.2

-- #check 0 #exit

-- h : CondConv a
-- h₂ : ¬AbsConv a
-- M : ℝ
-- h₁ : tendsTo (series a) M
-- h₃ : Infp a fun x ↦ 0 ≤ x
-- h₄ : Infp a fun x ↦ x < 0
-- σp : ℕ → ℕ
-- hp₁ : Subseq σp
-- hp₂ : ∀ (n : ℕ), 0 ≤ a n ↔ ∃ k, σp k = n
-- ap : ℕ → ℝ
-- hp : (fun x ↦ a (σp x)) = ap
-- σn : ℕ → ℕ
-- hn₁ : Subseq σn
-- hn₂ : ∀ (n : ℕ), a n < 0 ↔ ∃ k, σn k = n
-- an : ℕ → ℝ
-- hn : (fun x ↦ a (σn x)) = an
-- h₅ : monoLe (series ap)
-- h₆ : monoGe (series an)
-- G₁ : 0 ≤ ap
-- G₂ : an ≤ 0
-- G₃ : |ap| = ap
-- G₄ : |an| = -an
-- G₅ : 0 ≤ series ap
-- G₆ : series an ≤ 0
-- f g : ℕ → ℕ
-- hfg : ∀ (n : ℕ), f n + g n = n
-- hf : ∀ (i j : ℕ), i ≤ j → f i ≤ f j
-- hg : ∀ (i j : ℕ), i ≤ j → g i ≤ g j
-- f' g' : ℕ → ℕ
-- hfg' : ∀ (n : ℕ), f' n + g' n = n
-- hf' : ∀ (i j : ℕ), i ≤ j → f' i ≤ f' j
-- hg' : ∀ (i j : ℕ), i ≤ j → g' i ≤ g' j
-- Hf : ∀ (n : ℕ), ∃ k, n ≤ f k
-- Hf' : ∀ (n : ℕ), ∃ k, n ≤ f' k
-- Hg : ∀ (n : ℕ), ∃ k, n ≤ g k
-- Hg' : ∀ (n : ℕ), ∃ k, n ≤ g' k
-- Hfg : ∀ (n : ℕ), series a n = series ap (f n) + series an (g n)
-- Hfg' : ∀ (n : ℕ), series |a| n = series |ap| (f' n) + series |an| (g' n)
-- h₇ : ¬converges (series ap)
-- h₈ : ¬converges (series an)
-- ⊢ ∃ σ, Rment σ ∧ tendsTo (series fun x ↦ a (σ x)) L

theorem mkRment_eq_iff {a L i j} (h : CondConv a) : mkRment a L i = mkRment a L j ↔ i = j := by
  symm; constructor; rintro rfl; rfl; intro h
  sorry

-- #check 0 #exit

theorem rment_mkRment {a L} (h : CondConv a) : Rment (mkRment a L) := by
  constructor
  · intro i j h₁; rw [mkRment_eq_iff h] at h₁; exact h₁
  intro j
  simp_rw [mkRment_eq_getElem]
  change ∃ i, _
  suffices h : ∃ i, (mkRmentList a L (j + i + 1))[i]'
    (by apply lt_of_lt_of_le (b := j + i + 1) (by omega) (by simp)) = j
  ·
    obtain ⟨i, h⟩ := h
    use i
    convert h using 1
    rw [getElem_mkRmentList_eq_of_lt] <;> omega
  suffices h : ∃ (i : ℕ) (h : _), (mkRmentList a L (j + 1))[i]'h = j
  ·
    choose i h₁ h₂ using h
    use i
    convert h₂ using 1
    symm
    apply List.IsPrefix.getElem
    apply mkRmentList_prefix
    omega
  rw [←List.mem_iff_getElem]
  simp

-- theorem nodup_mkRmentList {a L n} (h : CondConv a) : (mkRmentList a L n).Nodup := by
--   sorry

theorem series_mkRment_eq_sum {a L n} :
series (λ i => a # mkRment a L i) n = (mkRmentList a L n |>.take n |>.map a |>.sum) := by
  simp [mkRment_eq_getElem, series]
  induction n
  ·
    simp
  nm n ih
  simp
  rw [Finset.sum_range_succ, ih]; clear ih
  simp
  congr 1
  have h₁ : mkRmentList a L n <+: mkRmentList a L (n + 1)
  ·
    apply mkRmentList_prefix
    simp
  obtain ⟨ys, h₁⟩ := h₁
  rw [←h₁]
  clear h₁
  simp

theorem take_length_mkRmentList {a L n is} (h : mkRmentList a L n = is) :
(mkRmentList a L is.length).take is.length = is := by
  generalize h₁ : mkRmentList a L is.length = is₁
  have h₂ : n ≤ is.length
  · simp [←h]
  have h₃ : is <+: is₁
  · subst h h₁; exact mkRmentList_prefix h₂
  obtain ⟨xs, rfl⟩ := h₃
  simp

-- #check 0 #exit

theorem abs_series_mkRment_dif_lt {a L n} (h : CondConv a) :
|series (λ i => a # mkRment a L i) (mkRmentList a L n).length - L| < 1 / (n + 1) := by
  rw [series_mkRment_eq_sum, take_length_mkRmentList rfl]
  sorry

-- #check 0 #exit

theorem tendsTo_series_mkRment {a L} (h : CondConv a) :
tendsTo (series # λ i => a # mkRment a L i) L := by
  -- we now have `|s - L| < 1 / (n + 1)`
  
  -- let `f : N -> N` be a function that maps `n` to the index representing the
  --   end of the `n`-th generation
  -- for all `n`, sum of rearrangement of `a` up to `f n` (inclusively) is
  --   at distance from `L` at most `1 / (n + 1)`
  -- elements of series of rearrangement of `a` between `f n` and `f (n + 1)`
  --   are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
  -- moreover, all elements or series of rearrangement of `a` after `f n`
  --   are at distance from `L` at most `2 * |a n| + 1 / (n + 1)`
  -- since `a` tends to `0` and `1 / (n + 1)` also tends to `0`,
  --   the series of rearrangement of `a` tends to `L`
  
  rw [tendsTo_iff_eps_lt_one]
  intro ε hε hε'
  
  obtain ⟨N, hN⟩ : ∃ (N : ℕ), 1 / (N + 1) < ε
  ·
    obtain ⟨N, hN⟩ := exists_nat_ge ε⁻¹
    use N
    rw [div_lt_iff₀] <;> try positivity
    field_simp at hN
    grind
  
  generalize hN₁ : (mkRmentList a L N).length = N₁
  have h₁ : N ≤ N₁
  · simp [←hN₁]
  have h₂ : 1 / (N₁ + 1) < ε
  · apply lt_of_le_of_lt _ hN
    field_simp
    simpa
  
  use N₁
  intro n hn
  apply hN.trans'
  
  -- have h₃ := abs_series_mkRment_dif_lt h (L := L) (n := n)
  
  -- apply lt_of_lt_of_le # abs_series_mkRment_dif_lt h
  -- field_simp
  -- simpa
  
  sorry

-- #check 0 #exit

theorem exi_rment_tendsTo_of_condConv {a L} (h : CondConv a) :
∃ σ, Rment σ ∧ tendsTo (series (a # σ ·)) L := by
  -- suppose that series of `a` converges to `M`
  obtain ⟨⟨M, h₁⟩, h₂⟩ := id h
  -- infinitely many elements of `a` are nonnegative
  have h₃ := h.infp_nonneg
  -- infinitely many elements of `a` are negative
  have h₄ := h.infp_neg
  -- there exists a subsequence of `a` called `a+`
  -- that contains exactly positive elements of `a`
  obtain ⟨σp, hp₁, hp₂⟩ := exi_subseq_of_infp h₃
  generalize hp : (a # σp ·) = ap
  -- similarly applies for `a-`
  obtain ⟨σn, hn₁, hn₂⟩ := exi_subseq_of_infp h₄
  generalize hn : (a # σn ·) = an
  
  -- series of `a+` is monotone
  have h₅ : monoLe # series ap
  · subst hp; apply monoLe_series_of_nonneg; intro n; rw [hp₂]; use n
  -- series of `a-` is antitone
  have h₆ : monoGe # series an
  · subst hn; apply monoGe_series_of_nonpos; intro n; apply le_of_lt; rw [hn₂]; use n
  
  have G₁ : 0 ≤ ap
  · intro n
    subst hp
    simp
    rw [hp₂]
    use n
  
  have G₂ : an ≤ 0
  · intro n
    subst hn
    simp
    apply le_of_lt
    rw [hn₂]
    use n
  
  have G₃ : |ap| = ap := abs_of_nonneg G₁
  have G₄ : |an| = -an := abs_of_nonpos G₂
  
  have G₅ : 0 ≤ series ap
  · intro n
    apply Finset.sum_nonneg
    intro k hk
    apply G₁
  
  have G₆ : series an ≤ 0
  · intro n
    apply Finset.sum_nonpos
    intro k hk
    apply G₂
  
  obtain ⟨f, g, hfg, hf, hg, Hf, Hg, Hfg⟩ :=
    exi_fn_series_of_subseq_cover (F := id) hp₁ hn₁ hp₂ # by simpa
  obtain ⟨f', g', hfg', hf', hg', Hf', Hg', Hfg'⟩ :=
    exi_fn_series_of_subseq_cover (F := abs) hp₁ hn₁ hp₂ # by simpa
  
  specialize Hf h₃
  specialize Hf' h₃
  specialize Hg # by simpa
  specialize Hg' # by simpa
  
  replace Hfg : ∀ (n : ℕ), series a n = series ap (f n) + series an (g n)
  · simp [hp, hn] at Hfg; exact Hfg
  
  replace Hfg' : ∀ (n : ℕ), series |a| n = series |ap| (f' n) + series |an| (g' n)
  · simpa [←hp, ←hn]
  
  -- series of `a+` and series of `a-` cannot both converge
  have h₇ : ¬(converges (series ap) ∧ converges (series an))
  ·
    -- suppose that series of `a+` converges to `X`
    rintro ⟨⟨X, h₇⟩, ⟨Y', h₈⟩⟩
    -- suppose that series of `a-` converges to `-Y`
    generalize hY : -Y' = Y
    rw [neg_eq_iff_eq_neg] at hY
    subst hY
    
    have hX : 0 ≤ X := le_limit_of_forall_le h₇ G₅
    
    have hY : 0 ≤ Y
    · suffices : -Y ≤ 0; linarith
      exact limit_le_of_forall_le h₈ G₆
    
    -- absolute series of `a` is bounded above by `X + Y`
    have h₉ : ∀ n, series |a| n ≤ X + Y
    ·
      intro n
      have H₁ : monoLe # series |an|
      · apply monoLe_series_abs
      have H₂ : tendsTo |series an| Y
      · rw [show Y = |-Y| by rw [abs_neg, abs_of_nonneg hY]]
        exact tendsTo_abs h₈
      have H₃ : ∀ n, series |ap| n ≤ X
      ·
        rw [abs_of_nonneg]; exact le_limit_of_monoLe h₅ h₇
        intro k
        subst hp
        simp
        rw [hp₂]
        use k
      have H₄ : ∀ n, series |an| n ≤ Y
      ·
        rw [abs_of_nonpos]
        rotate_left
        · subst hn
          intro k
          simp
          apply le_of_lt
          rw [hn₂]
          use k
        intro k
        rw [←neg_series']
        apply neg_le_of_neg_le
        apply limit_le_of_monoGe h₆ h₈
      rw [Hfg']
      linarith [H₃ (f' n), H₄ (g' n)]
    
    -- since it is monotone and bounded above, it converges
    have H : converges # series |a|
    · apply converges_of_monoLe_and_bounded_top # by simp
      use X + Y, h₉
    -- contradiction
    exact h₂ H
  
  rw [not_and_iff_or] at h₇
  
  -- series of `a+` diverges
  replace h₇ : ¬converges (series ap)
  ·
    by_contra h₈
    simp [h₈] at h₇
    choose X h₈ using h₈
    have H₁ : 0 ≤ X := le_limit_of_forall_le h₈ G₅
    
    obtain ⟨N₁, hN₁⟩ := exi_lt_of_monoGe_and_not_converges h₆ h₇ # M - (X + 1)
    
    specialize h₁ 1 (by norm_num)
    choose N₃ h₁ using h₁
    dsimp at h₁
    
    specialize Hg # N₁ + N₃
    obtain ⟨N₂, hN₂⟩ := Hg
    replace hN₁ : series an (g N₂) < M - (X + 1)
    · apply lt_of_le_of_lt _ hN₁
      apply h₆
      omega
    
    have H₃ : ∀ n, series ap n ≤ X
    · intro n; apply le_limit_of_monoLe h₅ h₈
    
    have H₄ : g N₂ ≤ N₂
    ·
      specialize hfg N₂
      omega
    
    specialize h₁ N₂ # by linarith
    rw [abs_sub_lt_iff'] at h₁
    replace h₁ := h₁.1
    
    rw [Hfg] at h₁
    contrapose! h₁; clear h₁
    
    suffices : series ap (f N₂) ≤ (X + 1) - 1; linarith
    apply H₃ _ |>.trans
    linarith
  
  -- similarly `a-` diverges
  have h₈ : ¬converges (series an)
  ·
    by_contra h₈
    choose Y' h₈ using h₈
    
    generalize hY : -Y' = Y
    rw [neg_eq_iff_eq_neg] at hY
    subst hY
    
    have H₁ : 0 ≤ Y
    ·
      suffices : -Y ≤ 0; linarith
      apply limit_le_of_forall_le h₈ G₆
    
    obtain ⟨N₁, hN₁⟩ := exi_gt_of_monoLe_and_not_converges h₅ h₇ # M + (Y + 1)
    
    specialize h₁ 1 (by norm_num)
    choose N₃ h₁ using h₁
    dsimp at h₁
    
    specialize Hf # N₁ + N₃
    obtain ⟨N₂, hN₂⟩ := Hf
    replace hN₁ : M + (Y + 1) < series ap (f N₂)
    · apply lt_of_lt_of_le hN₁
      apply h₅
      omega
    
    have H₃ : ∀ n, -Y ≤ series an n
    · intro n; apply limit_le_of_monoGe h₆ h₈
    
    have H₄ : f N₂ ≤ N₂
    ·
      specialize hfg N₂
      omega
    
    specialize h₁ N₂ # by linarith
    rw [abs_sub_lt_iff'] at h₁
    replace h₁ := h₁.2
    
    rw [Hfg] at h₁
    contrapose! h₁; clear h₁
    
    suffices : 1 - (Y + 1) ≤ series an (g N₂); linarith
    apply H₃ _ |>.trans'
    linarith
  
  use mkRment a L, rment_mkRment h, tendsTo_series_mkRment h