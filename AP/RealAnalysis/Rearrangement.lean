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

noncomputable
def mkRmentLen (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  mkRmentList a L n |>.length

-- #check 0 #exit

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

@[simp]
theorem le_length_mkRmentList {a L n} : n ≤ (mkRmentList a L n).length := by
  induction n; simp; rw [mkRmentList]; grind

@[simp]
theorem le_mkRmentLen {a L n} : n ≤ mkRmentLen a L n :=
  le_length_mkRmentList

theorem mkRmentList_prefix {a L k n} (h : k ≤ n) : mkRmentList a L k <+: mkRmentList a L n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n; rfl; rw [Nat.add_succ, mkRmentList]; grind

theorem getElem!_mkRmentList_eq_getElem {a L n k} (h : k < n) :
(mkRmentList a L n)[k]! = (mkRmentList a L n)[k]'(lt_of_lt_of_le h # by simp) := by
  rw [List.getElem!_eq_getElem]

@[simp]
theorem lt_length_mkRmentList_succ {a L n} : n < (mkRmentList a L (n + 1)).length := by
  apply lt_of_lt_of_le (b := n + 1) <;> simp

@[simp]
theorem lt_mkRmentLen_succ {a L n} : n < mkRmentLen a L (n + 1) :=
  lt_length_mkRmentList_succ

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

@[simp]
theorem take_mkRmentLen_mkRmentList {a L n} :
(mkRmentList a L # mkRmentLen a L n).take (mkRmentLen a L n) = mkRmentList a L n :=
  take_length_mkRmentList rfl

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

open CondConv in
theorem exi_rment_tendsTo_of_condConv {a L} (H : CondConv a) :
∃ σ, Rment σ ∧ tendsTo (series (a # σ ·)) L := by
  have h₁ := H.tendsTo_series
  have h₂ := H.not_absConv
  have h₃ := H.infp_nonneg
  have h₄ := H.infp_neg
  have hp₁ := CondConv.subseq_σp a
  have hn₁ := CondConv.subseq_σn a
  have hp₂ := @H.σp_spec'
  have hn₂ := @H.σn_spec'
  have h₅ := H.monoLe_series_ap
  have h₆ := H.monoGe_series_an
  have G₁ := H.ap_fn_nonneg
  have G₂ := H.an_fn_nonpos
  have G₃ := H.abs_ap_fn
  have G₄ := H.abs_an_fn
  have G₅ := H.series_ap_fn_nonneg
  have G₆ := H.series_an_fn_nonpos
  have hfg := @H.f_add_g
  have hf := @H.f_le_of_le
  have hg := @H.g_le_of_le
  have Hf := @H.exi_f_ge
  have Hg := @H.exi_g_ge
  have Hfg := @H.series_eq_f_add_g
  have hfg' := @H.f'_add_g'
  have hf' := @H.f'_le_of_le
  have hg' := @H.g'_le_of_le
  have Hf' := @H.exi_f'_ge
  have Hg' := @H.exi_g'_ge
  have Hfg' := @H.series_eq_f'_add_g'
  have h₇ := H.not_converges_series_ap
  have h₈ := H.not_converges_series_an
  use mkRment a L, rment_mkRment H, tendsTo_series_mkRment H