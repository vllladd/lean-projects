import AP.RealAnalysis.AlternatingInverse
import AP.Temp

namespace RealAnalysis

def Rment (σ : ℕ → ℕ) : Prop :=
  σ.Bijective

noncomputable
def rinv (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Classical.epsilon # λ k => σ k = n

noncomputable
def mkRmentP (a : ℕ → ℝ) (is : List ℕ) : ℕ :=
  Nat.find! # λ i => i ∉ is ∧ 0 ≤ a i

noncomputable
def mkRmentN (a : ℕ → ℝ) (is : List ℕ) : ℕ :=
  Nat.find! # λ j => j ∉ is ∧ a j < 0

noncomputable
def mkRmentList1 (a : ℕ → ℝ) (is : List ℕ) : List ℕ :=
  is ++ [mkRmentP a is, mkRmentN a is]

noncomputable
def mkRmentSum (a : ℕ → ℝ) (is : List ℕ) : ℝ :=
  is.map a |>.sum

def mkRmentLeNCnd (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (N : ℕ) : Prop :=
  0 ≤ a N ∧ ∀ r, N ≤ r → 0 ≤ a r → r ∉ is ∧ a r < 1 / (n + 2)

def mkRmentGeNCnd (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (N : ℕ) : Prop :=
  a N < 0 ∧ ∀ r, N ≤ r → a r < 0 → r ∉ is ∧ -1 / (n + 2) < a r

noncomputable
def mkRmentLeN (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! # mkRmentLeNCnd a n is

noncomputable
def mkRmentGeN (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! # mkRmentGeNCnd a n is

noncomputable
def mkRmentLeF (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : List ℕ :=
  List.range k |>.map (mkRmentLeN a n is + ·) |>.filter (0 ≤ a ·)

noncomputable
def mkRmentGeF (a : ℕ → ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : List ℕ :=
  List.range k |>.map (mkRmentGeN a n is + ·) |>.filter (a · < 0)

def mkRmentLeKCnd (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : Prop :=
  L - 1 / (n + 2) < mkRmentSum a is + (mkRmentLeF a n is k |>.map a |>.sum)

def mkRmentGeKCnd (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) (k : ℕ) : Prop :=
  mkRmentSum a is + (mkRmentGeF a n is k |>.map a |>.sum) < L + 1 / (n + 2)

noncomputable
def mkRmentLeK (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! # mkRmentLeKCnd a L n is

noncomputable
def mkRmentGeK (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : ℕ :=
  Nat.find! # mkRmentGeKCnd a L n is

noncomputable
def mkRmentLe (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  mkRmentLeF a n is # mkRmentLeK a L n is

noncomputable
def mkRmentGe (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  mkRmentGeF a n is # mkRmentGeK a L n is

noncomputable
def mkRmentIte (a : ℕ → ℝ) (L : ℝ) (n : ℕ) (is : List ℕ) : List ℕ :=
  is ++ if mkRmentSum a is ≤ L - 1 / (n + 2) then mkRmentLe a L n is
  else if L + 1 / (n + 2) ≤ mkRmentSum a is then mkRmentGe a L n is
  else []

noncomputable
def mkRmentList (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n + 1 => mkRmentIte a L n # mkRmentList1 a # mkRmentList a L n

noncomputable
def mkRment (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  (mkRmentList a L (n + 1))[n]!

noncomputable
def mkRmentLen (a : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℕ :=
  mkRmentList a L n |>.length

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
  induction n; simp; unfold mkRmentList mkRmentIte mkRmentList1; grind

@[simp]
theorem le_mkRmentLen {a L n} : n ≤ mkRmentLen a L n :=
  le_length_mkRmentList

theorem mkRmentList_prefix {a L k n} (h : k ≤ n) : mkRmentList a L k <+: mkRmentList a L n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n; rfl; rw [Nat.add_succ, mkRmentList]
  unfold mkRmentList1 mkRmentIte; grind

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

theorem mkRmentP_spec' {a is} (H : CondConv a) :
(mkRmentP a is ∉ is ∧ 0 ≤ a (mkRmentP a is)) ∧ ∀ k, k ∉ is ∧ 0 ≤ a k → mkRmentP a is ≤ k := by
  apply Nat.find!_spec' (p := λ i => i ∉ is ∧ 0 ≤ a i)
  choose n h₁ h₂ using H.infp_nonneg # is.sum + 1
  refine ⟨n, ?_, h₂⟩
  intro h₃
  replace h₄ := List.le_sum_of_mem h₃
  omega

theorem mkRmentN_spec' {a is} (H : CondConv a) :
(mkRmentN a is ∉ is ∧ a (mkRmentN a is) < 0) ∧ ∀ k, k ∉ is ∧ a k < 0 → mkRmentN a is ≤ k := by
  apply Nat.find!_spec' (p := λ i => i ∉ is ∧ a i < 0)
  choose n h₁ h₂ using H.infp_neg # is.sum + 1
  refine ⟨n, ?_, h₂⟩
  intro h₃
  replace h₄ := List.le_sum_of_mem h₃
  omega

theorem mkRmentP_spec {a is} (H : CondConv a) :
mkRmentP a is ∉ is ∧ 0 ≤ a (mkRmentP a is) := mkRmentP_spec' H |>.1

theorem mkRmentN_spec {a is} (H : CondConv a) :
mkRmentN a is ∉ is ∧ a (mkRmentN a is) < 0 := mkRmentN_spec' H |>.1

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
  apply List.mem_append_left
  apply List.mem_append_right
  simp
  have h₂ : ∀ k < n, k ∈ is
  · intro k hk
    specialize ih k hk
    apply List.IsPrefix.mem ih
    rw [←h_is]
    apply mkRmentList_prefix
    omega
  simp_rw [eq_comm (a := n)]
  by_cases h₃ : 0 ≤ a n
  · rw [mkRmentP, Nat.find!_eq_iff, if_pos ⟨n, by grind⟩]; grind
  · rw [mkRmentN, Nat.find!_eq_iff, if_pos ⟨n, by grind⟩]; grind

theorem getElem_mkRmentList_of_le.proof₁ {a L n₁ n₂ k} (h₁ : n₁ ≤ n₂)
(h₂ : k < (mkRmentList a L n₁).length) : k < (mkRmentList a L n₂).length :=
  lt_of_lt_of_le h₂ # List.IsPrefix.length_le # mkRmentList_prefix h₁

theorem getElem_mkRmentList_of_le {a L n₁ n₂ k} {hh : k < (mkRmentList a L n₁).length}
(h : n₁ ≤ n₂) : (mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k]'
(getElem_mkRmentList_of_le.proof₁ h hh) := by
  apply List.IsPrefix.getElem # mkRmentList_prefix h

theorem getElem_mkRmentList_eq {a L n₁ n₂ k}
{hh₁ : k < (mkRmentList a L n₁).length} {hh₂ : k < (mkRmentList a L n₂).length} :
(mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k] := by
  rcases lt_trichotomy n₁ n₂ with h₁ | rfl | h₁; on_goal 2 => rfl
  · exact getElem_mkRmentList_of_le # le_of_lt h₁
  · exact getElem_mkRmentList_of_le (le_of_lt h₁) |>.symm

@[simp]
theorem getElem_mkRmentList_eq_iff_true {a L n₁ n₂ k}
{hh₁ : k < (mkRmentList a L n₁).length} {hh₂ : k < (mkRmentList a L n₂).length} :
(mkRmentList a L n₁)[k] = (mkRmentList a L n₂)[k] ↔ True := by
  simp; exact getElem_mkRmentList_eq

@[simp]
theorem mkRmentList_zero {a L} : mkRmentList a L 0 = [] := rfl

theorem mkRmentP_notMem {a is} (H : CondConv a) : mkRmentP a is ∉ is :=
  mkRmentP_spec H |>.1

theorem mkRmentN_notMem {a is} (H : CondConv a) : mkRmentN a is ∉ is :=
  mkRmentN_spec H |>.1

theorem mkRmentP_nonneg {a is} (H : CondConv a) : 0 ≤ a (mkRmentP a is) :=
  mkRmentP_spec H |>.2

theorem mkRmentN_neg {a is} (H : CondConv a) : a (mkRmentN a is) < 0 :=
  mkRmentN_spec H |>.2

theorem mkRmentP_ne_mkRmentN {a is} (H : CondConv a) : mkRmentP a is ≠ mkRmentN a is := by
  have := @mkRmentP_nonneg a is H; have := @mkRmentN_neg a is H; grind

@[simp]
theorem nodup_mkRmentLe {a L n is} : (mkRmentLe a L n is).Nodup := by
  unfold mkRmentLe mkRmentLeF
  rw [←List.filterMap_eq_filter, List.filterMap_map]
  simp; rw [List.nodup_filterMap_iff]; grind

@[simp]
theorem nodup_mkRmentGe {a L n is} : (mkRmentGe a L n is).Nodup := by
  unfold mkRmentGe mkRmentGeF
  rw [←List.filterMap_eq_filter, List.filterMap_map]
  simp; rw [List.nodup_filterMap_iff]; grind

theorem mkRmentLeK_spec' {a L n is} (H : CondConv a) :
mkRmentLeKCnd a L n is (mkRmentLeK a L n is) ∧
∀ k, mkRmentLeKCnd a L n is k → mkRmentLeK a L n is ≤ k :=
  Nat.find!_spec' # H.exi_add_ap_map_range_drop_gt _ _ _

theorem mkRmentGeK_spec' {a L n is} (H : CondConv a) :
mkRmentGeKCnd a L n is (mkRmentGeK a L n is) ∧
∀ k, mkRmentGeKCnd a L n is k → mkRmentGeK a L n is ≤ k :=
  Nat.find!_spec' # H.exi_add_an_map_range_drop_lt _ _ _

theorem mkRmentLeK_spec {a L n is} (H : CondConv a) : L - 1 / (n + 2) < mkRmentSum a is +
(mkRmentLeF a n is (mkRmentLeK a L n is) |>.map a |>.sum) :=
  mkRmentLeK_spec' H |>.1

theorem mkRmentGeK_spec {a L n is} (H : CondConv a) : mkRmentSum a is +
(mkRmentGeF a n is (mkRmentGeK a L n is) |>.map a |>.sum) < L + 1 / (n + 2) :=
  mkRmentGeK_spec' H |>.1

theorem mkRmentLeN_spec' {a n is} (H : CondConv a) :
mkRmentLeNCnd a n is (mkRmentLeN a n is) ∧
∀ k, mkRmentLeNCnd a n is k → mkRmentLeN a n is ≤ k := by
  apply Nat.find!_spec'
  generalize hN₁ : is.sum + 1 = N₁
  choose N₂ h₁ using tendsTo_zero_of_converges_series H.converges_series
    (1 / (n + 2)) (by subst hN₁; positivity)
  simp at h₁
  choose N₃ h₂ h₃ using H.infp_nonneg (N₁ + N₂)
  use N₃, h₃
  intro r hr h₄
  split_ands
  · intro h₅
    replace h₅ := List.le_sum_of_mem h₅
    omega
  specialize h₁ r (by omega)
  rw [abs_of_nonneg h₄] at h₁
  apply lt_of_lt_of_le h₁
  simp

theorem mkRmentGeN_spec' {a n is} (H : CondConv a) :
mkRmentGeNCnd a n is (mkRmentGeN a n is) ∧
∀ k, mkRmentGeNCnd a n is k → mkRmentGeN a n is ≤ k := by
  apply Nat.find!_spec'
  generalize hN₁ : is.sum + 1 = N₁
  choose N₂ h₁ using tendsTo_zero_of_converges_series H.converges_series
    (1 / (n + 2)) (by subst hN₁; positivity)
  simp at h₁
  choose N₃ h₂ h₃ using H.infp_neg (N₁ + N₂)
  use N₃, h₃
  intro r hr h₄
  split_ands
  · intro h₅
    replace h₅ := List.le_sum_of_mem h₅
    omega
  specialize h₁ r (by omega)
  rw [abs_of_neg h₄, neg_lt] at h₁
  apply lt_of_le_of_lt _ h₁
  field_simp
  rfl

theorem mkRmentLeN_spec {a n is} (H : CondConv a) : 0 ≤ a (mkRmentLeN a n is) ∧
∀ r, mkRmentLeN a n is ≤ r → 0 ≤ a r → r ∉ is ∧ a r < 1 / (n + 2) :=
  mkRmentLeN_spec' H |>.1

theorem mkRmentGeN_spec {a n is} (H : CondConv a) : a (mkRmentGeN a n is) < 0 ∧
∀ r, mkRmentGeN a n is ≤ r → a r < 0 → r ∉ is ∧ -1 / (n + 2) < a r :=
  mkRmentGeN_spec' H |>.1

theorem notMem_mkRmentLe_of_mem {a L n is i} (H : CondConv a)
(h : i ∈ is) : i ∉ mkRmentLe a L n is := by
  simp [mkRmentLe, mkRmentLeF]
  rintro k h₁ rfl
  have h₂ := @mkRmentLeN_spec a n is H |>.2 (mkRmentLeN a n is + k) (by omega)
  simp [h] at h₂; exact h₂

theorem notMem_mkRmentGe_of_mem {a L n is i} (H : CondConv a)
(h : i ∈ is) : i ∉ mkRmentGe a L n is := by
  simp [mkRmentGe, mkRmentGeF]
  rintro k h₁ rfl
  have h₂ := @mkRmentGeN_spec a n is H |>.2 (mkRmentGeN a n is + k) (by omega)
  simp [h] at h₂; exact h₂

theorem nodup_mkRmentList {a L n} (H : CondConv a) : (mkRmentList a L n).Nodup := by
  induction n; simp
  nm n ih
  unfold mkRmentList
  generalize h₁ : mkRmentList a L n = is at ih ⊢
  unfold mkRmentList1
  have h₂ := @mkRmentP_notMem a is H
  have h₃ := @mkRmentN_notMem a is H
  generalize h₄ : is ++ [mkRmentP a is, mkRmentN a is] = is₁
  unfold mkRmentIte
  rw [List.nodup_append]
  apply and_of
  · subst h₄
    rw [List.nodup_append]
    use ih
    simp [mkRmentP_ne_mkRmentN H]
    intro i hi
    split_ands
    · contrapose! hi
      subst hi
      exact mkRmentP_notMem H
    · contrapose! hi
      subst hi
      exact mkRmentN_notMem H
  intro h₅
  split_ifs with h₆ h₇ <;> simp <;> intro i
  · exact notMem_mkRmentLe_of_mem H
  · exact notMem_mkRmentGe_of_mem H

theorem mkRment_eq_iff {a L i j} (H : CondConv a) : mkRment a L i = mkRment a L j ↔ i = j := by
  symm; constructor; rintro rfl; rfl; intro h
  by_contra! h₁
  wlog h₂ : i < j with ih
  · push_neg at h₂; apply ih H h.symm # ne_symm' h₁; grind
  clear h₁
  simp_rw [mkRment_eq_getElem] at h
  have h₃ : i + 1 ≤ j + 1; omega
  rw [getElem_mkRmentList_of_le h₃] at h
  have h₄ := List.eq_of_getElem_and_nodup h # nodup_mkRmentList H
  omega

theorem rment_mkRment {a L} (h : CondConv a) : Rment (mkRment a L) := by
  constructor
  · intro i j h₁; rw [mkRment_eq_iff h] at h₁; exact h₁
  intro j
  simp_rw [mkRment_eq_getElem]
  change ∃ i, _
  suffices h : ∃ i, (mkRmentList a L (j + i + 1))[i]'
    (by apply lt_of_lt_of_le (b := j + i + 1) (by omega) (by simp)) = j
  · obtain ⟨i, h⟩ := h
    use i
    convert h using 1
    rw [getElem_mkRmentList_eq_of_lt] <;> omega
  suffices h : ∃ (i : ℕ) (h : _), (mkRmentList a L (j + 1))[i]'h = j
  · choose i h₁ h₂ using h
    use i
    convert h₂ using 1
    symm
    apply List.IsPrefix.getElem
    apply mkRmentList_prefix
    omega
  rw [←List.mem_iff_getElem]
  simp

theorem series_mkRment_eq_sum {a L n} :
series (λ i => a # mkRment a L i) n = (mkRmentList a L n |>.take n |>.map a |>.sum) := by
  simp [mkRment_eq_getElem, series]
  induction n
  · simp
  nm n ih
  simp
  rw [Finset.sum_range_succ, ih]; clear ih
  simp
  congr 1
  have h₁ : mkRmentList a L n <+: mkRmentList a L (n + 1)
  · apply mkRmentList_prefix
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

@[simp]
theorem mkRmentLeF_zero {a n is} : mkRmentLeF a n is 0 = [] := rfl

@[simp]
theorem mkRmentGeF_zero {a n is} : mkRmentGeF a n is 0 = [] := rfl

theorem abs_map_sum_mkRmentLe_sub_lt {a L is} {n : ℕ} (H : CondConv a)
(h₁ : mkRmentSum a is ≤ L - (n + 2 : ℝ)⁻¹) :
|(is.map a |>.sum) + (mkRmentLe a L n is |>.map a |>.sum) - L| ≤ (n + 2 : ℝ)⁻¹ := by
  rw [←mkRmentSum, mkRmentLe]
  generalize hs : (mkRmentLeF a n is (mkRmentLeK a L n is) |>.map a).sum = s
  generalize hk : mkRmentLeK a L n is = k at hs
  choose h₂ h₃ using @mkRmentLeK_spec' a L n is H
  simp [mkRmentLeKCnd, hk, hs] at h₂
  rw [hk] at h₃
  change ∀ r, _ at h₃
  generalize hd : (n + 2 : ℝ)⁻¹ = d at h₁ h₂ ⊢
  generalize hs₀ : mkRmentSum a is = s₀ at h₁ ⊢
  have hd₁ : 0 < d; subst hd; positivity
  suffices h : L - d ≤ s₀ + s ∧ s₀ + s ≤ L
  · rw [abs_sub_le_iff]; split_ands <;> linarith
  split_ands; linarith
  rw [hs₀] at h₂
  cases k
  · simp at hs; linarith
  nm k
  specialize h₃ k
  simp [mkRmentLeKCnd, hs₀] at h₃
  simp [mkRmentLeF, List.range_succ] at hs
  rw [←mkRmentLeF] at hs
  generalize hs' : (mkRmentLeF a n is k |>.map a |>.sum) = s' at h₃ hs
  rw [hd] at h₃
  simp [List.filter_cons] at hs
  choose h₄ h₅ h₆ using @mkRmentLeN_spec a n is H
  generalize hN : mkRmentLeN a n is = N at hs h₄ h₅ h₆
  split_ifs at hs with h₇
  rotate_left
  · simp at hs; linarith
  suffices h : a (N + k) ≤ d
  · simp at hs; linarith
  specialize h₆ (N + k) (by omega) h₇
  simp [hd] at h₆
  exact le_of_lt h₆

theorem abs_map_sum_mkRmentGe_sub_lt {a L is} {n : ℕ} (H : CondConv a)
(h₁ : L + (n + 2 : ℝ)⁻¹ ≤ mkRmentSum a is) :
|(is.map a |>.sum) + (mkRmentGe a L n is |>.map a |>.sum) - L| ≤ (n + 2 : ℝ)⁻¹ := by
  rw [←mkRmentSum, mkRmentGe]
  generalize hs : (mkRmentGeF a n is (mkRmentGeK a L n is) |>.map a).sum = s
  generalize hk : mkRmentGeK a L n is = k at hs
  choose h₂ h₃ using @mkRmentGeK_spec' a L n is H
  simp [mkRmentGeKCnd, hk, hs] at h₂
  rw [hk] at h₃
  change ∀ r, _ at h₃
  generalize hd : (n + 2 : ℝ)⁻¹ = d at h₁ h₂ ⊢
  generalize hs₀ : mkRmentSum a is = s₀ at h₁ ⊢
  have hd₁ : 0 < d; subst hd; positivity
  suffices h : L ≤ s₀ + s ∧ s₀ + s ≤ L + d
  · rw [abs_sub_le_iff]; split_ands <;> linarith
  symm; split_ands; linarith
  rw [hs₀] at h₂
  cases k
  · simp at hs; linarith
  nm k
  specialize h₃ k
  simp [mkRmentGeKCnd, hs₀] at h₃
  simp [mkRmentGeF, List.range_succ] at hs
  rw [←mkRmentGeF] at hs
  generalize hs' : (mkRmentGeF a n is k |>.map a |>.sum) = s' at h₃ hs
  rw [hd] at h₃
  simp [List.filter_cons] at hs
  choose h₄ h₅ h₆ using @mkRmentGeN_spec a n is H
  generalize hN : mkRmentGeN a n is = N at hs h₄ h₅ h₆
  split_ifs at hs with h₇
  rotate_left
  · simp at hs; linarith
  suffices h : -d < a (N + k)
  · simp at hs; linarith
  specialize h₆ (N + k) (by omega) h₇
  simp [neg_div, hd] at h₆
  exact h₆

theorem abs_map_sum_mkRmentIte_sub_lt {a L n is} (H : CondConv a) :
|(mkRmentIte a L n is |>.map a |>.sum) - L| ≤ 1 / (n + 2) := by
  rw [mkRmentIte]; simp; split_ifs with h₁ h₂
  · exact abs_map_sum_mkRmentLe_sub_lt H h₁
  · exact abs_map_sum_mkRmentGe_sub_lt H h₂
  · simp [mkRmentSum] at h₁ h₂; simp [abs_le]; split_ands <;> linarith

theorem abs_map_sum_mkRmentList_sub_lt {a L n} (H : CondConv a) (hn : n ≠ 0) :
|(mkRmentList a L n |>.map a |>.sum) - L| ≤ 1 / (n + 1) := by
  cases n; simp at hn
  simp [mkRmentList]
  convert abs_map_sum_mkRmentIte_sub_lt H using 1
  grind

theorem abs_series_mkRment_mkRmentLen_sub_lt {a L n} (H : CondConv a) (hn : n ≠ 0) :
|series (a # mkRment a L ·) (mkRmentLen a L n) - L| ≤ 1 / (n + 1) := by
  convert @abs_map_sum_mkRmentList_sub_lt a L n H hn using 3
  dsimp [series, mkRmentLen]
  rw [List.sum_map_eq_sum_getElem_finset_range]
  apply Finset.sum_congr rfl
  intro i h₁
  simp at h₁
  simp [h₁]
  rw [mkRment_eq_getElem]
  congr 1
  simp

theorem subseq_exi_ge {σ n} (h : Subseq σ) : ∃ k, n ≤ σ k :=
  ⟨n, nat_le_of_subseq h⟩

theorem subseq_exi_gt {σ n} (h : Subseq σ) : ∃ k, n < σ k := by
  choose k hk using subseq_exi_ge h (n := n)
  use σ # k + 1
  apply lt_of_le_of_lt hk
  apply lt_of_le_of_lt # nat_le_of_subseq h
  simp [subseq_lt_iff h]

theorem subseq_exi_ge_and_between_of_le {σ n i} (h₁ : Subseq σ) (h₂ : σ n ≤ i) :
∃ k, n ≤ k ∧ σ k ≤ i ∧ i < σ (k + 1) := by
  have h₃ : ∃ k, i < σ k
  · apply subseq_exi_gt
    intro i j h₃
    simpa [subseq_lt_iff h₁]
  generalize hk : Nat.find! (λ k => i < σ k) = k
  choose h₄ h₅ using Nat.find!_spec' h₃
  rw [hk] at h₄ h₅
  clear h₃ hk
  cases k
  · have h₆ : σ n < σ 0; linarith
    simp [subseq_lt_iff h₁] at h₆
  nm k
  have h₆ := h₅ k
  simp at h₆
  refine ⟨k, ?_, h₆, h₄⟩
  by_contra! h₃
  rw [←Nat.add_one_le_iff, ←subseq_le_iff h₁] at h₃
  linarith

@[simp]
theorem mkRmentLen_lt_succ {a L n} : mkRmentLen a L n < mkRmentLen a L (n + 1) := by
  simp [mkRmentLen]; rw [mkRmentList, mkRmentIte]
  simp; apply Nat.lt_add_right; simp [mkRmentList1]

@[simp]
theorem subseq_mkRmentLen {a L} : Subseq (mkRmentLen a L) := by
  intro i j h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h; clear h
  induction j
  · simp
  nm n ih
  apply ih.trans; clear ih
  rw [←Nat.add_assoc]
  simp

@[simp]
theorem take_mkRmentLen_mkRmentList_add {a L n k} :
(mkRmentList a L # n + k).take (mkRmentLen a L n) = mkRmentList a L n := by
  choose xs h using @mkRmentList_prefix a L n (n + k) (by omega); simp [←h, mkRmentLen]

theorem mem_mkRmentList_of_lt {a L n k} (h : k < n) : k ∈ mkRmentList a L n := by
  rw [←Nat.add_one_le_iff] at h
  have h₁ := @mem_mkRmentList_succ a L k
  apply List.IsPrefix.mem h₁
  exact mkRmentList_prefix h

theorem le_mkRmentP_mkRmentList {a L n} (H : CondConv a) :
n ≤ mkRmentP a (mkRmentList a L n) := by
  have h := @mkRmentP_spec a (mkRmentList a L n) H |>.1
  contrapose! h; exact mem_mkRmentList_of_lt h

theorem le_mkRmentN_mkRmentList {a L n} (H : CondConv a) :
n ≤ mkRmentN a (mkRmentList a L n) := by
  have h := @mkRmentN_spec a (mkRmentList a L n) H |>.1
  contrapose! h; exact mem_mkRmentList_of_lt h

theorem nonneg_of_mem_mkRmentLe {a L n is i} (h : i ∈ mkRmentLe a L n is) : 0 ≤ a i := by
  simp [mkRmentLe, mkRmentLeF] at h; exact h.2

theorem neg_of_mem_mkRmentGe {a L n is i} (h : i ∈ mkRmentGe a L n is) : a i < 0 := by
  simp [mkRmentGe, mkRmentGeF] at h; exact h.2

theorem abs_series_add_sum_mkRmentList_sub_lt.aux₁ {a L n N k i j s₀ s s₁ is is₁ d}
(H : CondConv a)
(h₂ : mkRmentSum a (mkRmentList a L n) = s₀)
(h₁ : mkRmentList a L n = is)
(_hN : is.length = N)
(h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹)
(ha : tendsTo a 0)
(hi : mkRmentP a is = i)
(hj : mkRmentN a is = j)
(h₄ : is ++ [i, j] = is₁)
(hs : mkRmentSum a is₁ = s)
(hd : (n + 2 : ℝ)⁻¹ = d)
(hs₁ : (mkRmentLe a L n is₁ |>.map a |>.take k |>.sum) = s₁)
(H₂ : s ≤ L - d) : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹ := by
  rw [abs_of_nonneg]
  rotate_left
  · rw [←hs₁]
    apply List.sum_nonneg
    intro r hr
    replace hr := List.mem_of_mem_take hr
    simp at hr
    rcases hr with ⟨x, hr, rfl⟩
    exact nonneg_of_mem_mkRmentLe hr
  rw [←hs₁]
  apply List.sum_take_le_of_nonneg _ |>.trans _
  · simp
    intro y hy
    exact nonneg_of_mem_mkRmentLe hy
  clear! s₁ k
  have hN' : mkRmentLen a L n = N
  · rwa [mkRmentLen, h₁]
  have H₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L (n + 1) H (by simp)
  rw [series_mkRment_eq_sum] at H₃
  rw [take_mkRmentLen_mkRmentList] at H₃
  rw [mkRmentList, h₁, mkRmentIte] at H₃
  rw [mkRmentList1, hi, hj, h₄, hs] at H₃
  simp at H₃
  rw [hd, if_pos H₂, ←mkRmentSum, hs] at H₃
  rw [show (n + 1 + 1 : ℝ) = n + 2 by ring_nf, hd] at H₃
  generalize hs₁ : (mkRmentLe a L n is₁ |>.map a).sum = s₁ at H₃ ⊢
  rw [abs_le] at H₃
  replace H₃ := H₃.2
  have H₄ : s₀ + a i + a j = s
  · rw [←hs, mkRmentSum, ←h₄]
    simp
    rw [←h₂, h₁, mkRmentSum, add_assoc]
  have H₅ : L - (n + 1 : ℝ)⁻¹ ≤ s₀
  · rw [abs_le] at h₃; linarith
  have H₆ : L - 2 * bounds a n - (n + 1 : ℝ)⁻¹ ≤ s
  · rw [←H₄]
    suffices : -bounds a n + -bounds a n ≤ a i + a j; linarith
    apply add_le_add
    · rw [neg_le]
      trans bounds a i
      · rw [←bounds_neg]
        change (-a) i ≤ _
        apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo # tendsTo_neg ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hi, ←h₁]
      exact le_mkRmentP_mkRmentList H
    · rw [neg_le]
      trans bounds a j
      · rw [←bounds_neg]
        change (-a) j ≤ _
        apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo # tendsTo_neg ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hj, ←h₁]
      exact le_mkRmentN_mkRmentList H
  linarith

theorem abs_series_add_sum_mkRmentList_sub_lt.aux₂ {a L n N k i j s₀ s s₁ is is₁ d}
(H : CondConv a)
(h₂ : mkRmentSum a (mkRmentList a L n) = s₀)
(h₁ : mkRmentList a L n = is)
(_hN : is.length = N)
(h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹)
(ha : tendsTo a 0)
(hi : mkRmentP a is = i)
(hj : mkRmentN a is = j)
(h₄ : is ++ [i, j] = is₁)
(hs : mkRmentSum a is₁ = s)
(hd : (n + 2 : ℝ)⁻¹ = d)
(hs₁ : (mkRmentGe a L n is₁ |>.map a |>.take k |>.sum) = s₁)
(H₂ : L + d ≤ s) : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹ := by
  rw [abs_of_nonpos]
  rotate_left
  · rw [←hs₁]
    apply List.sum_nonpos
    intro r hr
    replace hr := List.mem_of_mem_take hr
    simp at hr
    rcases hr with ⟨x, hr, rfl⟩
    exact le_of_lt # neg_of_mem_mkRmentGe hr
  rw [neg_le, ←hs₁]
  apply List.le_sum_take_of_nonpos _ |>.trans' _
  · simp
    intro y hy
    exact le_of_lt # neg_of_mem_mkRmentGe hy
  clear! s₁ k
  have hN' : mkRmentLen a L n = N
  · rwa [mkRmentLen, h₁]
  have H₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L (n + 1) H (by simp)
  rw [series_mkRment_eq_sum] at H₃
  rw [take_mkRmentLen_mkRmentList] at H₃
  rw [mkRmentList, h₁, mkRmentIte] at H₃
  rw [mkRmentList1, hi, hj, h₄, hs] at H₃
  simp at H₃
  rw [hd] at H₃
  have hd₀ : 0 < d
  · rw [←hd]; positivity
  rw [if_neg # by linarith] at H₃
  rw [if_pos H₂] at H₃
  rw [←mkRmentSum, hs] at H₃
  rw [show (n + 1 + 1 : ℝ) = n + 2 by ring_nf, hd] at H₃
  generalize hs₁ : (mkRmentGe a L n is₁ |>.map a).sum = s₁ at H₃ ⊢
  rw [abs_le] at H₃
  replace H₃ := H₃.1
  have H₄ : s₀ + a i + a j = s
  · rw [←hs, mkRmentSum, ←h₄]
    simp
    rw [←h₂, h₁, mkRmentSum, add_assoc]
  have H₅ : s₀ ≤ L + (n + 1 : ℝ)⁻¹
  · rw [abs_le] at h₃; linarith
  have H₆ : s ≤ L + 2 * bounds a n + (n + 1 : ℝ)⁻¹
  · rw [←H₄]
    suffices : a i + a j ≤ bounds a n + bounds a n; linarith
    apply add_le_add
    · trans bounds a i
      · apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hi, ←h₁]
      exact le_mkRmentP_mkRmentList H
    · trans bounds a j
      · apply le_of_abs_le
        exact abs_le_bounds_of_tendsTo ha
      apply bounds_le_bounds_of_tendsTo ha
      rw [←hj, ←h₁]
      exact le_mkRmentN_mkRmentList H
  linarith

theorem abs_series_add_sum_mkRmentList_sub_lt {a L n N k}
(H : CondConv a) (hN : mkRmentLen a L n = N) (hn : n ≠ 0) :
|series (a # mkRment a L ·) N + (mkRmentList a L (n + 1) |>.drop N |>.take k
|>.map a |>.sum) - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  generalize hs₀ : series (a # mkRment a L ·) N = s₀
  have h₂ : mkRmentSum a (mkRmentList a L n) = s₀
  · subst hs₀ hN
    rw [series_mkRment_eq_sum, mkRmentSum]
    congr
    rw [take_mkRmentLen_mkRmentList]
  rw [mkRmentLen] at hN
  generalize h₁ : mkRmentList a L n = is at hN hs₀
  rw [mkRmentList, h₁]
  have h₃ : |s₀ - L| ≤ (n + 1 : ℝ)⁻¹
  · have h₃ := @abs_series_mkRment_mkRmentLen_sub_lt a L n H hn
    simp [mkRmentLen, h₁, hN, hs₀] at h₃
    exact h₃
  rw [mkRmentIte, mkRmentList1, ←hN]
  simp
  have ha := H.tendsTo_zero
  have hb₀ : 0 ≤ bounds a n
  · exact bounds_nonneg_of_tendsTo H.tendsTo_zero
  have hb₁ : |s₀ - L + a (mkRmentP a is)| ≤ |s₀ - L| + bounds a n
  · apply abs_add_le _ _ |>.trans
    simp
    obtain ⟨⟨h₄, h₅⟩, h₆⟩ := @mkRmentP_spec' a is H
    apply abs_le_bounds_of_tendsTo ha |>.trans
    apply bounds_le_bounds_of_tendsTo ha
    rw [←h₁]; exact le_mkRmentP_mkRmentList H
  have hb₂ : |s₀ - L + a (mkRmentP a is) + a (mkRmentN a is)| ≤ |s₀ - L| + 2 * bounds a n
  · apply abs_add_le _ _ |>.trans
    suffices : |a # mkRmentN a is| ≤ bounds a n; linarith
    obtain ⟨⟨h₄, h₅⟩, h₆⟩ := @mkRmentN_spec' a is H
    apply abs_le_bounds_of_tendsTo ha |>.trans
    apply bounds_le_bounds_of_tendsTo ha
    rw [←h₁]; exact le_mkRmentN_mkRmentList H
  have H₁ : 0 ≤ (n + 1 : ℝ)⁻¹; positivity
  cases k
  · simp
    linarith
  nm k
  cases k
  · simp; ring_nf at H₁ h₃ hb₁ ⊢; linarith
  nm k
  simp
  generalize hx : mkRmentP a is = i at hb₁ hb₂ ⊢
  generalize hy : mkRmentN a is = j at hb₂ ⊢
  generalize h₄ : is ++ [i, j] = is₁
  generalize hs : mkRmentSum a is₁ = s
  generalize hd : (n + 2 : ℝ)⁻¹ = d
  generalize hs₁ : ((if s ≤ L - d then mkRmentLe a L n is₁ else if L + d ≤ s
    then mkRmentGe a L n is₁ else []) |>.map a |>.take k |>.sum) = s₁
  suffices h : |s₀ - L + a i + a j + s₁| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹
  · ring_nf at h ⊢; exact h
  apply abs_add_le _ _ |>.trans
  suffices : |s₁| ≤ 4 * bounds a n + 2 * (n + 1 : ℝ)⁻¹; linarith
  split_ifs at hs₁ with H₂ H₃
  · exact abs_series_add_sum_mkRmentList_sub_lt.aux₁
      H h₂ h₁ hN h₃ ha hx hy h₄ hs hd hs₁ H₂
  · apply abs_series_add_sum_mkRmentList_sub_lt.aux₂
      H h₂ h₁ hN h₃ ha hx hy h₄ hs hd hs₁ H₃
  simp at hs₁; subst hs₁; simp; positivity

theorem abs_series_mkRment_sub_lt_of_between {a L n i} (H : CondConv a)
(hn : n ≠ 0) (h₁ : mkRmentLen a L n ≤ i) (h₂ : i < mkRmentLen a L (n + 1)) :
|series (a # mkRment a L ·) i - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  rw [series_add]
  generalize hN : mkRmentLen a L n = N at h₂ ⊢
  apply @abs_series_add_sum_mkRmentList_sub_lt a L n N i H hN hn |>.trans'
  apply le_of_eq
  congr
  rw [series, List.sum_map_eq_sum_toFinset]
  rotate_left
  · apply List.nodup_take
    apply List.nodup_drop
    exact nodup_mkRmentList H
  induction i
  · simp [←hN]
  nm i ih
  specialize ih # by omega
  rw [Finset.sum_range_succ, ih]
  clear ih
  rw [List.take_succ]
  simp
  rw [Finset.sum_union]
  rotate_left
  · simp
    intro j h₃
    simp_rw [Option.toList]
    split; simp
    nm x k h₄; clear x
    simp
    rintro rfl
    rw [List.mem_take_iff_getElem] at h₃
    choose r₁ hr₁ h₃ using h₃
    rw [min_eq_left # by grind] at hr₁
    rw [List.getElem?_eq_some_iff] at h₄
    choose h₅ h₄ using h₄
    rw [←h₃] at h₄
    rw [List.getElem_drop] at h₄
    have h₅ : mkRmentList a L (n + 1) |>.Nodup; exact nodup_mkRmentList H
    rw [h₅.getElem_inj_iff] at h₄
    omega
  simp
  simp_rw [Option.toList]
  split
  · nm x h₁; clear x
    exfalso
    suffices : N + i < (mkRmentList a L # n + 1).length; grind
    clear h₁
    rw [mkRmentLen] at h₂
    omega
  nm x j h₁; clear x
  simp
  congr
  rw [mkRment_eq_getElem]
  rw [List.getElem?_eq_some_iff] at h₁
  choose h₃ h₁ using h₁
  subst h₁
  rw [mkRmentLen] at h₂
  symm
  apply List.IsPrefix.getElem
  apply mkRmentList_prefix
  have : n ≤ N; simp [←hN];
  omega

theorem abs_series_mkRment_sub_lt_of_le {a L n i} (H : CondConv a)
(hn : n ≠ 0) (h : mkRmentLen a L n ≤ i) :
|series (a # mkRment a L ·) i - L| ≤ 8 * bounds a n + 4 * (n + 1 : ℝ)⁻¹ := by
  choose k hk h₁ h₂ using subseq_exi_ge_and_between_of_le (by simp) h
  apply abs_series_mkRment_sub_lt_of_between H (by omega) h₁ h₂ |>.trans
  apply add_le_add
  · simp; exact bounds_le_bounds_of_tendsTo H.tendsTo_zero hk
  field_simp; norm_cast; simp
  exact hk

theorem tendsTo_series_mkRment {a L} (H : CondConv a) :
tendsTo (series # λ i => a # mkRment a L i) L := by
  rw [tendsTo_iff_eps_lt_one]
  intro ε hε hε'
  obtain ⟨N₁, hN₁⟩ : ∃ (N : ℕ), ∀ n, N ≤ n → 1 / (n + 1) < ε / 16
  · obtain ⟨N, hN⟩ := exists_nat_ge (ε / 16)⁻¹
    use N
    intro n hn
    rw [div_lt_iff₀] <;> try positivity
    field_simp at hN ⊢
    apply lt_of_le_of_lt hN
    rw [mul_lt_mul_iff_right₀ hε]
    norm_cast; omega
  choose N₂ hN₂ using H.bounds_tendsTo_zero (ε / 32) (by positivity)
  simp at hN₂
  generalize hn₁ : N₁ + N₂ + 1 = n₁
  use mkRmentLen a L n₁
  intro n hn
  have h₁ : n₁ ≤ n
  · apply hn.trans'; simp
  specialize hN₁ n₁ (by omega)
  specialize hN₂ n₁ (by omega)
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  apply abs_series_mkRment_sub_lt_of_le H (by omega) hn |>.trans
  rw [abs_bounds_of_tendsTo H.tendsTo_zero] at hN₂
  simp at hN₁; linarith

open CondConv in
theorem exi_rment_tendsTo_of_condConv {a L} (H : CondConv a) :
∃ σ, Rment σ ∧ tendsTo (series (a # σ ·)) L :=
  ⟨_, rment_mkRment H, tendsTo_series_mkRment H⟩