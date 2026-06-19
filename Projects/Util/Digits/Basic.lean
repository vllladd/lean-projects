import Projects.Util.Digits.Defs

namespace Nat

theorem base_iff {b} : Base b ↔ 2 ≤ b := ⟨(·.1), (⟨·⟩)⟩

theorem base_iff_decide {b} : Base b ↔ Base.decide b := by
  simp [base_iff, Base.decide]

instance {b} : Decidable # Base b :=
  decidable_of_iff' _ base_iff_decide

@[simp] instance : Base 2 := by decide
@[simp] instance : Base 10 := by decide

variable {b : ℕ} [hb : Base b]

@[simp] theorem Base.two_le : 2 ≤ b := hb.1
@[simp] theorem Base.one_lt : 1 < b := hb.1
@[simp] theorem Base.one_le : 1 ≤ b := by linarith [hb.one_lt]
@[simp] theorem Base.pos : 0 < b := by linarith [hb.two_le]
@[simp] theorem Base.ne_zero : b ≠ 0 := by linarith [hb.one_le]

theorem Base.div_lt {n} (h : b ≤ n) : n / b < n := by
  calc
  _ < n / b + n / b * (b - 1) := by simp [h]
  _ = n / b * (b - 1 + 1) := by ring_nf
  _ = n / b * b := by rw [Nat.sub_add_cancel # by simp]
  _ ≤ _ := by simp

@[simp]
theorem Base.not_le_one : ¬(b ≤ 1) := by
  simp

@[simp]
theorem Base.one_mod : 1 % b = 1 := by
  rw [Nat.mod_eq_of_lt]; simp

@[simp]
theorem Base.one_div : 1 / b = 0 := by
  rw [Nat.div_eq_of_lt]; simp

theorem Base.sub_div_mul_sub_one_succ_lt {n} : n - n / b * (b - 1) + 1 < n + b := by
  rw [←Nat.sub_add_comm # Nat.div_mul_le_of_le # by simp]
  apply Nat.add_sub_lt_add_of_sub_lt; calc
  _ ≤ 1 := by simp
  _ < _ := by simp

@[simp]
theorem toDigList_zero : toDigList b 0 = [0] := by
  simp [toDigList]

@[simp]
theorem toDigList_one : toDigList b 1 = [1] := by
  simp [toDigList]; iterate 2 unfold toDigList'; simp

theorem lt_pow_digsNum {n} : n < b ^ digsNum b n := by
  unfold digsNum toDigList
  simp
  split_ifs with h₁
  · simp [h₁]
  fun_induction toDigList'
  · nm k h; simp at h
  · omega
  nm n h₂ h₃ ih
  simp at ih ⊢
  clear h₁ h₂
  by_cases h₁ : n < b
  · clear ih
    simp [pow_succ]
    rw [mul_comm]
    apply lt_mul_of_lt_of_one_le h₁
    apply Nat.one_le_pow
    omega
  simp at h₁
  specialize ih h₁
  rw [Nat.div_lt_iff_lt_mul (by simp)] at ih
  simp [pow_succ]
  omega

theorem lt_pow_of_digsNum_eq {n k : ℕ}
(h : digsNum b n = k) : n < b ^ k := by
  subst h; exact lt_pow_digsNum

@[simp]
theorem sum_toDigList'_zero {b} : (toDigList' b 0).sum = 0 := by
  unfold toDigList'; simp

@[simp]
theorem sum_toDigList'_le {b n} : (toDigList' b n).sum ≤ n := by
  fun_induction toDigList' <;> simp
  nm n h₁ h₂ ih
  by_cases h₃ : n < b
  · simp [div_eq_of_lt h₃]
  simp at h₃
  rw [Nat.le_div_iff_mul_le (by omega)] at ih
  generalize (toDigList' b (n / b)).sum = k at ih ⊢
  cases k; simp; nm k
  apply ih.trans'; clear ih
  cases b; simp at h₁; nm b
  rw [mul_succ]
  simp
  trans b
  on_goal 2 => grind
  rw[←Nat.lt_add_one_iff]
  apply mod_lt
  simp

@[simp]
theorem sum_toDigList_le {b n} : (toDigList b n).sum ≤ n := by
  unfold toDigList; split_ifs <;> simp

@[simp]
theorem digSum_le {b n} : digSum b n ≤ n := by
  simp [digSum]

@[simp]
theorem not_lt_sum_toDigList' {b n} : ¬(n < (toDigList' b n).sum) := by
  simp

@[simp]
theorem not_lt_sum_toDigList {b n} : ¬(n < (toDigList b n).sum) := by
  simp

@[simp]
theorem not_lt_digSum {b n} : ¬(n < digSum b n) := by
  simp

@[simp]
theorem toDigList_base_zero_succ {n} : toDigList 0 (n + 1) = [] := by
  unfold toDigList toDigList'; simp

@[simp]
theorem toDigList_base_one_succ {n} : toDigList 1 (n + 1) = [] := by
  unfold toDigList toDigList'; simp

@[simp]
theorem digSum_base_zero {n} : digSum 0 n = 0 := by
  simp [digSum]; cases n <;> simp [toDigList]

@[simp]
theorem digSum_base_one {n} : digSum 1 n = 0 := by
  simp [digSum]; cases n <;> simp [toDigList]

theorem toDigList'_of_lt_base {b n} (hn : n ≠ 0) (h : n < b) : toDigList' b n = [n] := by
  rw [toDigList', if_neg (by omega)]
  simp [hn, div_eq_of_lt h]
  unfold toDigList'
  rw [if_neg (by omega)]
  simp [mod_eq_of_lt h]

theorem toDigList_of_lt_base {n} (h : n < b) : toDigList b n = [n] := by
  unfold toDigList; split_ifs with hn; simp at hn; grind
  rw [toDigList'_of_lt_base] <;> grind

@[simp]
theorem digSum_zero {b} : digSum b 0 = 0 := by
  simp [digSum, toDigList]; split_ifs <;> rfl

@[simp]
theorem digSum_one : digSum b 1 = 1 := by
  simp [digSum]

theorem digSum_of_lt_base {b n} (h : n < b) : digSum b n = n := by
  by_cases h₁ : b ≤ 1; simp [show n = 0 by omega]
  have hb : Base b := ⟨by omega⟩
  rw [digSum, toDigList_of_lt_base h]; rfl

theorem digSum_lt_iff_base_le {n} : digSum b n < n ↔ b ≤ n := by
  have hb' := hb.1
  constructor <;> intro h₁
  · contrapose! h₁
    rw [digSum_of_lt_base h₁]
  unfold digSum toDigList
  simp
  split_ifs with hn <;> simp; omega
  clear hn
  induction n using Nat.strong_induction_on
  nm n ih
  rw [toDigList', if_neg (by omega)]
  split_ifs with hn
  · simp [hn]; omega
  have h₀ : n % b + n / b < n
  · conv => rhs; rw [eq_div_mod n b, add_comm]
    rw [add_lt_add_iff_left]
    rw [Nat.lt_mul_iff_one_lt_right (by simp; omega)]; omega
  by_cases h₃ : n / b < b
  · rw [toDigList'_of_lt_base (by simp; omega) h₃]
    simp [h₀]
  simp at h₃
  have h₂ : n / b < n
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  specialize ih _ h₂ h₃
  simp
  linarith

theorem digSum_of_base_le_one {b n} (hb : b ≤ 1) : digSum b n = 0 := by
  unfold digSum toDigList; simp [hb]

@[simp]
theorem digSum_eq_self_iff {n} : digSum b n = n ↔ n = 0 ∨ n < b := by
  symm; constructor
  · rintro (rfl | h)
    · simp
    rw [digSum_of_lt_base h]
  intro h
  by_cases hb : b ≤ 1
  · rw [digSum_of_base_le_one hb] at h
    omega
  replace hb : 2 ≤ b; omega
  replace h : ¬(b.digSum n < n); omega
  rw [digSum_lt_iff_base_le] at h
  omega

theorem digSum_step {n} : digSum b n = n % b + digSum b (n / b) := by
  have hb' := hb.1
  nth_rw 1 [digSum, toDigList]
  simp
  split_ifs with hn
  · simp [hn]
  simp
  rw [toDigList', if_neg (by omega), if_neg hn]
  simp
  rw [digSum, toDigList]
  split_ifs with h h₁; omega
  · simp [h₁]
  simp

@[simp]
theorem digSum_base : digSum b b = 1 := by
  rw [digSum_step]; simp

theorem digSum_add_base_of_lt_base {n}
(h : n < b) : digSum b (n + b) = n + 1 := by
  have hb' := hb.1
  rw [digSum, toDigList, if_neg (by omega)]; simp
  rw [toDigList', if_neg (by omega), if_neg (by omega)]; simp
  rw [div_eq_of_lt h, mod_eq_of_lt h]; simp
  rw [toDigList'_of_lt_base] <;> simp

@[simp]
theorem digSum_eq_zero_iff {b n} : digSum b n = 0 ↔ b ≤ 1 ∨ n = 0 := by
  symm; constructor
  · rintro (h | rfl)
    · rw [digSum_of_base_le_one h]
    simp
  contrapose!; rintro ⟨hb', h⟩
  replace hb' : 2 ≤ b; omega
  have hb : Base b := ⟨hb'⟩
  cases n; simp at h; nm n; clear h
  induction n using ind_step b
  · nm n h
    rw [←Nat.add_one_le_iff] at h
    rw [Nat.le_iff_lt_or_eq] at h
    rcases h with h | rfl
    · rw [digSum_of_lt_base h]; simp
    · rw [digSum_base]; simp
  nm n ih
  rw [digSum_step]
  rw [show n + b + 1 = n + 1 + b by omega]
  simp
  intro h
  apply ih
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  nlinarith

@[simp]
theorem digSum_mul_base {b n} : digSum b (n * b) = digSum b n := by
  by_cases hb : b ≤ 1
  · cases b; simp; nm b; cases b; simp; simp at hb
  replace hb : Base b := ⟨by omega⟩
  rw [digSum_step]; simp

@[simp]
theorem digSum_base_mul {b n} : digSum b (b * n) = digSum b n := by
  rw [mul_comm]; simp

@[simp]
theorem digSum_mul_base_pow {b n k} : digSum b (n * b ^ k) = digSum b n := by
  induction k; simp; simpa [pow_succ, ←mul_assoc]

@[simp]
theorem digSum_base_mul_pow {b n k} : digSum b (b ^ k * n) = digSum b n := by
  rw [mul_comm]; simp

theorem digSum_mul_base_add {n k} (hk : k < b) :
digSum b (n * b + k) = digSum b n + k := by
  rw [digSum_step]
  rw [Nat.add_mod]; simp [Nat.mod_eq_of_lt hk]
  have h₁ : (n * b + k) / b = n
  · rw [Nat.div_eq_iff] <;> omega
  simp [h₁]; rw [add_comm k]

theorem digSum_base_add {n} (hk : n < b) : digSum b (b + n) = n + 1 := by
  nth_rw 2 [show b = 1 * b by simp]
  rw [digSum_mul_base_add (by omega)]
  rw [add_comm]; simp

theorem digSum_add_base {n} (hk : n < b) : digSum b (n + b) = n + 1 := by
  rw [add_comm n, digSum_base_add hk]

theorem ind_dig (b : ℕ) [hb : Base b] {p : ℕ → Prop} (h₁ : ∀ c < b, p c)
(h₂ : ∀ k c, k ≠ 0 → c < b → (∀ m < k * b + c, p m) → p (k * b + c)) : ∀ n, p n := by
  replace hb := hb.1
  intro n
  induction n using Nat.strong_induction_on
  nm n ih
  obtain ⟨k, c, hc, rfl⟩ := n.exi_mul_add b (by omega)
  cases k
  · simp
    exact h₁ _ hc
  nm k
  apply h₂ _ _ _ hc ih; simp

theorem digSum_mod_base_pred {n} : digSum b n % (b - 1) = n % (b - 1) := by
  have hb' := hb.1
  induction n using ind_dig b
  · nm n h; rw [digSum_of_lt_base h]
  nm k c hk hc ih
  rw [digSum_mul_base_add hc]
  rw [add_mod, ih k (by simp [lt_self_mul_add_iff]; omega)]
  have h : k * b = k * (b - 1) + k
  · cases b; simp at hb'; nm b
    simp [mul_add]
  rw [h]; clear h
  rw [add_assoc]
  nth_rw 2 [add_mod]
  simp

@[simp]
theorem ofDigList_singleton {b n} : ofDigList b [n] = n := by
  simp [ofDigList]

theorem toDigList'_mul_base_add {k c} (hk : k ≠ 0) (hc : c < b) :
toDigList' b (k * b + c) = c :: toDigList' b k := by
  nth_rw 1 [toDigList']
  simp [hk, Nat.mod_eq_of_lt hc]
  rw [Nat.add_div (by simp)]
  simp [Nat.mod_eq_of_lt hc]
  simp [Nat.not_le_of_lt hc]
  simp [Nat.div_eq_of_lt hc]

theorem toDigList_mul_base_add {k c} (hk : k ≠ 0) (hc : c < b) :
toDigList b (k * b + c) = toDigList b k ++ [c] := by
  unfold toDigList; simp [hk]; rw [toDigList'_mul_base_add hk hc]

@[simp]
theorem Base.ne_one : b ≠ 1 := by
  cases hb; omega

@[simp]
theorem ofDigList_toDigList {n} : ofDigList b (toDigList b n) = n := by
  induction n using ind_dig b
  · nm n h
    rw [toDigList_of_lt_base h]
    simp
  nm k c hk hc ih
  rw [toDigList_mul_base_add hk hc]
  nth_rw 1 [ofDigList]
  simp
  rw [←ofDigList]
  apply ih
  rw [Nat.lt_self_mul_add_iff]
  simp [hk]

@[simp]
theorem toDigList'_zero : toDigList' b 0 = [] := by
  unfold toDigList'; simp

@[simp]
theorem toDigList'_eq_nil_iff {n} : toDigList' b n = [] ↔ n = 0 := by
  unfold toDigList'; simp

@[simp]
theorem toDigList_ne_nil {n} : toDigList b n ≠ [] := by
  simp [toDigList]; split_ifs with hn <;> simp [hn]

theorem digRev_of_lt_base {n} (h : n < b) : digRev b n = n := by
  rw [digRev, toDigList_of_lt_base h]; simp

omit hb in @[simp]
theorem ofDigList_nil : ofDigList b [] = 0 := rfl

@[simp]
theorem ofDigList_snoc {c cs} : ofDigList b (cs ++ [c]) = ofDigList b cs * b + c := by
  rw [ofDigList, List.foldl_append]; simp; rfl

omit hb in @[simp]
theorem ofDigList_cons {c cs} :
ofDigList b (c :: cs) = c * b ^ cs.length + ofDigList b cs := by
  simp [ofDigList]; induction cs generalizing c <;> simp; grind

theorem toDigList_mul_base {k} (hk : k ≠ 0) :
toDigList b (k * b) = toDigList b k ++ [0] := by
  rw [←toDigList_mul_base_add hk (by simp)]; rfl

@[simp]
theorem digRev_mul_base {k} : digRev b (k * b) = digRev b k := by
  by_cases hk : k = 0
  · simp [hk]
  unfold digRev
  rw [toDigList_mul_base hk]
  simp

theorem digRev_mul_base_add {k c} (hk : k ≠ 0) (hc : c < b) :
digRev b (k * b + c) = c * b ^ (digsNum b k) + digRev b k := by
  unfold digsNum digRev; simp [toDigList_mul_base_add hk hc]

example : ¬∀ (b n : ℕ) [Base b], digRev b (digRev b n) = n := by
  simp; use 2, by simp, 2; decide_cbv

theorem digsNum_eq_iff {n k} : digsNum b n = k ↔
(n = 0 ∧ k = 1) ∨ (k ≠ 0 ∧ b ^ (k - 1) ≤ n ∧ n < b ^ k) := by
  unfold digsNum
  induction n using ind_dig b generalizing k
  · nm n hn
    rw [toDigList_of_lt_base hn]
    simp
    constructor
    · rintro rfl
      simp [hn]
      omega
    rintro (⟨rfl, rfl⟩ | ⟨h₁, h₂, h₃⟩); rfl
    cases k; simp at h₁; nm k
    cases k; rfl; nm k
    clear h₁ h₃; exfalso
    simp at h₂
    simp [pow_add] at h₂
    contrapose! hn; clear hn
    apply h₂.trans'
    cases k <;> simp
    nm k
    rw [one_le_pow_iff] <;> simp
  nm n c hn hc ih
  rw [toDigList_mul_base_add hn hc]
  simp
  cases k <;> simp
  nm k
  simp at ih
  specialize @ih n _ k
  · simp [lt_self_mul_add_iff]
    omega
  rw [ih]; clear ih
  have hb' := hb.1
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨h₁, h₂, h₃⟩)
    · simp at hn
    cases k; simp at h₁; nm k
    simp at h₂ ⊢
    clear h₁
    simp [pow_succ] at h₃ ⊢
    split_ands <;> nlinarith
  · rintro (⟨⟨rfl, rfl⟩, rfl⟩ | ⟨h₁, h₂⟩)
    · simp at hn
    cases k
    · simp at h₁ h₂
      exfalso
      cases n; simp at hn; nm n
      simp [add_mul] at h₂
      omega
    nm k
    simp [hn]
    simp [pow_succ] at h₁ h₂ ⊢
    split_ands <;> nlinarith

theorem digRev_eq_of_digsNum_eq_two {n} (h : digsNum b n = 2) :
digRev b n = n % b * b + n / b := by
  have hb' := hb.1
  unfold digRev
  simp [digsNum_eq_iff] at h
  rcases h with ⟨h₁, h₂⟩
  induction n using ind_dig b
  · omega
  nm n c h₃ h₄ ih; clear ih
  simp [toDigList_mul_base_add h₃ h₄]
  induction n using ind_dig b
  rotate_left
  · nm n d h₅ h₆ ih
    clear ih h₁ h₃
    exfalso
    contrapose! h₂; clear h₂
    simp [pow_two, add_mul]
    cases n
    · simp at h₅
    nm n
    simp [add_mul]
    omega
  nm d h₅
  simp [toDigList_of_lt_base h₅]
  rw [Nat.add_div (by simp)]
  simpa [mod_eq_of_lt h₄, div_eq_of_lt h₄]

@[simp]
theorem digsNum_zero : digsNum b 0 = 1 := by
  simp [digsNum]

theorem digsNum_of_lt_base {n} (hn : n < b) : digsNum b n = 1 := by
  simp [digsNum, toDigList_of_lt_base hn]

theorem digsNum_base_mul_add {k c} (hk : k ≠ 0) (hc : c < b) :
digsNum b (k * b + c) = digsNum b k + 1 := by
  unfold digsNum; simp [toDigList_mul_base_add hk hc]

theorem digsNum_base_mul {k} (hk : k ≠ 0) :
digsNum b (k * b) = digsNum b k + 1 := by
  rw [←digsNum_base_mul_add (c := 0) hk (by simp)]; rfl

def digSumAlt₁ (b n : ℕ) : ℕ :=
  if ¬b.Base then 0 else
  if n < b then n else
  n % b + digSumAlt₁ b (n / b)
decreasing_by nm hb h; simp_all; exact hb.div_lt h

@[csimp]
theorem digSum_eq_digSumAlt₁ : digSum = digSumAlt₁ := by
  symm; ext b n
  by_cases hb : b ≤ 1
  · symm; rw [digSumAlt₁]
    simp [base_iff, hb]
  have hb' := hb
  replace hb : Base b := ⟨by omega⟩
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSumAlt₁ Nat.digSum
  simp [hb]
  split_ifs with h₁
  · rw [toDigList_of_lt_base h₁]; rfl
  simp at hb h₁
  have h₂ : n / b < n
  · rw [Nat.div_lt_iff_lt_mul (by simp)]
    rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  specialize ih _ h₂
  rw [ih]; clear ih
  rw [Nat.toDigList, if_neg (by omega)]
  rw [Nat.toDigList', if_neg (by omega), if_neg (by omega)]
  rw [add_comm, Nat.digSum, Nat.toDigList]
  simp [Nat.not_lt_of_le h₁, show n ≠ 0 by omega]