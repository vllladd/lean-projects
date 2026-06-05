import Projects.Util

namespace Function

variable {α β γ : Type*}

def fixNCnd (f : α → α) (x : α) (k : ℕ) : Prop :=
  f.IsFixedPt # f^[k] x

open Classical in noncomputable
def fixN (f : α → α) (x : α) : ℕ :=
  epsilon # f.fixNCnd x

open Classical in noncomputable
def fix (f : α → α) (x : α) : α :=
  f^[f.fixN x] x

def fixCnd (f : α → α) (x : α) (k : ℕ) : Prop :=
  f.fix x = f^[k] x ∧ f (f.fix x) = f.fix x

-- #check 0 #exit

-----

theorem iterate_add' {f : α → α} {n m : ℕ} : f^[n + m] = f^[m] ∘ f^[n] := by
  rw [add_comm, iterate_add]

theorem fixCnd_spec {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixNCnd x (f.fixN x) := by
  unfold fixNCnd fixN; apply Classical.epsilon_spec (p := f.fixNCnd x)
  unfold fixNCnd; use k

theorem fix_spec {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixCnd x k := by
  unfold fixCnd fix fixN fixNCnd
  generalize hp : (λ k => f.IsFixedPt # f^[k] x) = p
  generalize hm : Classical.epsilon p = m
  have h₁ := Classical.epsilon_spec (p := p) (by subst hp; use k)
  nth_rw 1 [←hp] at h₁
  simp [hm] at h₁
  have h₂ : ∀ ⦃r⦄, f^[k + r] x = f^[k] x
  · intro r; simp [Function.iterate_add']; rwa [Function.iterate_fixed]
  have h₃ : ∀ ⦃r⦄, f^[m + r] x = f^[m] x
  · intro r; simp [Function.iterate_add']; rwa [Function.iterate_fixed]
  symm; use h₁; obtain h₂ | h₂ := le_total k m
  all_goals obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le h₂; grind

theorem fix_spec' {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixCnd x (f.fixN x) :=
  fix_spec _ # fixCnd_spec k h

theorem fixCnd_fixN_of_fixCnd {f : α → α} {x : α} {k : ℕ}
(h : f.fixCnd x k) : f.fixCnd x (f.fixN x) := by
  rcases h with ⟨h₁, h₂⟩; rw [h₁] at h₂; exact fix_spec' _ h₂

theorem fixCnd_apply {f : α → α} {x : α} {k : ℕ} (h : f.fixCnd x k) : f.fixCnd (f x) k := by
  rcases h with ⟨h₁, h₂⟩
  rw [h₁] at h₂
  apply fix_spec
  change _ = _
  replace h₂ : f^[k + 1] x = f^[k] x
  · rwa [iterate_succ']
  change f (f^[k + 1] x) = f^[k + 1] x
  nth_rw 1 [h₂]; rw [iterate_succ']; rfl

theorem fix_apply {f : α → α} {x : α} {k : ℕ} (h : f.fixCnd x k) : f.fix (f x) = f.fix x := by
  choose h₃ h₄ using fixCnd_apply h
  choose h₁ h₂ using h
  rw [h₁] at h₂
  rw [h₃] at h₄
  rw [h₁, h₃]
  clear h₁ h₃ h₄
  replace h₂ : f^[k + 1] x = f^[k] x
  · rwa [iterate_succ']
  exact h₂

-- #check 0 #exit

end Function

namespace Nat

def digSum (b n : ℕ) : ℕ :=
  toDigList b n |>.sum

-- #check 0 #exit

-----

attribute [simp] mod_le

@[simp]
theorem sum_toDigList'_zero {b} : (toDigList' b 0).sum = 0 := by
  unfold toDigList'; simp

@[simp]
theorem sum_toDigList'_le {b n} : (toDigList' b n).sum ≤ n := by
  fun_induction toDigList' <;> simp
  nm n h₁ h₂ ih
  simp at ih
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
theorem toDigList_zero_succ {n} : toDigList 0 (n + 1) = [] := by
  unfold toDigList toDigList'; simp

@[simp]
theorem toDigList_one_succ {n} : toDigList 1 (n + 1) = [] := by
  unfold toDigList toDigList'; simp

@[simp]
theorem digSum_base_zero {n} : digSum 0 n = 0 := by
  simp [digSum]; cases n <;> simp

@[simp]
theorem digSum_base_one {n} : digSum 1 n = 0 := by
  simp [digSum]; cases n <;> simp

theorem toDigList'_of_lt_base {b n}
(hb : 2 ≤ b) (hn : n ≠ 0) (h : n < b) : toDigList' b n = [n] := by
  rw [toDigList', if_neg (by omega)]
  simp [hn, div_eq_of_lt h]
  unfold toDigList'
  rw [if_neg (by omega)]
  simp [mod_eq_of_lt h]

theorem toDigList_of_lt_base {b n} (hb : 2 ≤ b) (h : n < b) : toDigList b n = [n] := by
  unfold toDigList; split_ifs with hn; simp [hn]
  simp [toDigList'_of_lt_base hb hn h]

theorem digSum_of_lt_base {b n} (hb : 2 ≤ b) (h : n < b) : digSum b n = n := by
  rw [digSum, toDigList_of_lt_base hb h]; rfl

theorem eq_div_mod (n k : ℕ) : n = n / k * k + n % k := by
  simp

theorem eq_mod_div (n k : ℕ) : n = n % k + n / k * k := by
  simp

theorem digSum_lt_iff_base_le {b n} (hb : 2 ≤ b) : digSum b n < n ↔ b ≤ n := by
  constructor <;> intro h₁
  · contrapose! h₁
    rw [digSum_of_lt_base hb h₁]
  unfold digSum toDigList
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
  · rw [toDigList'_of_lt_base hb (by simp; omega) h₃]
    simp [h₀]
  simp at h₃
  have h₂ : n / b < n
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  specialize ih _ h₂ h₃
  simp
  linarith

@[simp]
theorem digSUm_zero {b} : digSum b 0 = 0 := by
  simp [digSum]

theorem digSum_of_base_le_one {b n} (hb : b ≤ 1) : digSum b n = 0 := by
  unfold digSum toDigList
  split_ifs with hn <;> simp
  unfold toDigList'; simp [hb]

-- #check 0 #exit

end Nat

namespace DigitalRoot

noncomputable
def digRoot (b n : ℕ) : ℕ :=
  Nat.digSum b |>.fix n

def digRootComp' (b n g : ℕ) : ℕ :=
  match g with
  | 0 => n
  | g + 1 => if n < b then n else digRootComp' b (Nat.digSum b n) g

def digRootComp (b n : ℕ) : ℕ :=
  digRootComp' b n n