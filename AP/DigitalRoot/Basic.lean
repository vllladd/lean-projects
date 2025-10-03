import AP.Util

namespace DigitalRoot

class Base (b : ℕ) : Prop where
  h : 2 ≤ b

theorem base_iff {b} : Base b ↔ 2 ≤ b := ⟨(·.1), (⟨·⟩)⟩

instance {b} : Decidable # Base b :=
  match h : decide # 2 ≤ b with
  | true => .isTrue # by simp_all [base_iff]
  | false => .isFalse # by simp_all [base_iff]

instance : Base 2 := ⟨by norm_num⟩

variable {b} [hb : Base b]

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

def digSum (b n : ℕ) : ℕ :=
  if ¬Base b then 0 else
  if n < b then n else
  n % b + digSum b (n / b)
decreasing_by
  nm hb h; push_neg at hb h; exact hb.div_lt h

@[simp]
theorem digSum_le {n} : digSum b n ≤ n := by
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSum
  split_ifs with h₁; rfl
  push_neg at h₁
  specialize ih (n / b) # hb.div_lt h₁
  have h₂ := hb.two_le
  generalize digSum b (n / b) = k at ih ⊢
  calc
  _ ≤ n % b + n / b := by linarith
  _ ≤ n % b + n / b * b := by simp [-Nat.mod_add_div₂]
  _ = n := by simp

theorem Base.sub_div_mul_sub_one_succ_lt {n} : n - n / b * (b - 1) + 1 < n + b := by
  rw [←Nat.sub_add_comm # Nat.div_mul_le_of_le # by simp]
  apply Nat.add_sub_lt_add_of_sub_lt; calc
  _ ≤ 1 := by simp
  _ < _ := by simp

@[simp]
theorem digSum_lt_iff_base_le {n} : digSum b n < n ↔ b ≤ n := by
  constructor <;> intro h; contrapose! h; simp [digSum, h, hb]
  unfold digSum; simp [hb]; rw [←ite_not]; simp [h]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h; simp; calc
  _ ≤ n % b + n / b + 1 := by simp [add_assoc]
  _ = n % b + n / b * b - n / b * (b - 1) + 1 := by
    rw [Nat.add_right_cancel_iff, Nat.add_sub_assoc (by simp), Nat.add_left_cancel_iff,
      Nat.mul_sub, mul_one, tsub_tsub_assoc (by simp) (by simp), tsub_self, zero_add]
  _ = n - n / b * (b - 1) + 1 := by simp
  _ < _ := by rw [add_comm b]; exact hb.sub_div_mul_sub_one_succ_lt

def digRoot (b n : ℕ) : ℕ :=
  if ¬Base b then 0 else
  if n < b then n else
  digRoot b # digSum b n
decreasing_by
  nm hb h; push_neg at hb h; rwa [digSum_lt_iff_base_le]

def digRoot' (b n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % (b - 1) = 0 then b - 1
  else n % (b - 1)

@[simp]
theorem digRoot_zero : digRoot b 0 = 0 := by
  unfold digRoot; simp [hb]

omit hb in @[simp]
theorem digRoot'_zero : digRoot' b 0 = 0 := rfl

omit hb in
theorem digRoot'_eq_of_lt_base {n} (h : n < b) : digRoot' b n = n := by
  unfold digRoot'
  split_ifs with h₁ h₂
  · exact h₁.symm
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h₂; clear h₂
    cases b; simp; nm b
    simp_all
    rcases h₁ with ⟨h₁, h₂⟩
    cases k; simp at h₂; nm k
    cases k; simp; nm k
    simp [Nat.mul_add] at h
    cases b; simp at h₁; nm b
    ring_nf at h
    contrapose! h
    simp [Nat.add_assoc]
    trans b * 2 <;> simp
  · cases b; simp at h; nm b
    simp_all only [add_tsub_cancel_right]
    rw [Nat.lt_succ, le_iff_eq_or_lt] at h
    rcases h with rfl | h; simp at h₂
    rw [Nat.mod_eq_of_lt h]

@[simp]
theorem digSum_zero : digSum b 0 = 0 := by
  simp [digSum]

@[simp]
theorem digSum_eq_zero_iff {n} : digSum b n = 0 ↔ n = 0 := by
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSum
  simp [hb]
  split_ifs with h; rfl
  push_neg at h
  simp
  symm; constructor; rintro rfl; simp
  rintro ⟨h₁, h₂⟩
  rw [ih _ # hb.div_lt h] at h₂
  simp at h₂
  linarith

omit hb in @[simp]
theorem digRoot'_digRoot' {n} : digRoot' b (digRoot' b n) = digRoot' b n := by
  cases n; simp; nm n
  unfold digRoot'; simp
  split_ifs <;> simp_all

theorem Base.eq_two_or_three_le : b = 2 ∨ 3 ≤ b := by
  cases hb; omega

@[simp]
theorem digRoot'_base_two {n} : digRoot' 2 n = if n = 0 then 0 else 1 := by
  simp [digRoot']; split_ifs with h₁ h₂ <;> omega

theorem digRoot'_add_base {n} : digRoot' b (n + b) = digRoot' b (n + 1) := by
  rcases hb.eq_two_or_three_le with rfl | h₁; simp; nth_rw 1 [digRoot']
  simp; rw [Nat.add_mod, Nat.mod_self_sub_one_eq_one h₁]; simp; rfl

theorem digRoot'_add_base_sub_one {n} (h : n ≠ 0) :
digRoot' b (n + (b - 1)) = digRoot' b n := by
  cases n; simp at h; nm n; simp [digRoot'_add_base]

omit hb in @[simp]
theorem digRoot'_base_sub_one : digRoot' b (b - 1) = b - 1 := by
  unfold digRoot'; simp [eq_comm]

@[simp]
theorem Base.sub_one_ne_zero : b - 1 ≠ 0 := by
  cases hb; omega

theorem digRoot'_base_sub_one_add {n} (h : n ≠ 0) :
digRoot' b (b - 1 + n) = digRoot' b n := by
  rw [add_comm]; exact digRoot'_add_base_sub_one h

theorem digRoot'_add {n m} :
digRoot' b (n + m) = digRoot' b (digRoot' b n + digRoot' b m) := by
  cases n; simp; nm n; cases m; simp; nm m
  nth_rw 1 [digRoot']; iterate 2 nth_rw 2 [digRoot']; simp
  split_ifs with h₁ h₂ h₃ h₃ h₂ h₃ h₃
  · rw [digRoot'_add_base_sub_one] <;> simp
  · rw [Nat.add_mod, h₂] at h₁; simp at h₁; contradiction
  · rw [Nat.add_mod, h₃] at h₁; simp at h₁; contradiction
  · unfold digRoot'; simp [h₁, h₂]
  · rw [Nat.add_mod, h₂] at h₁; simp at h₁; contradiction
  · rw [digRoot'_base_sub_one_add h₃, Nat.add_mod, h₂]; simp
    rw [digRoot'_eq_of_lt_base]; trans b - 1; apply Nat.mod_lt; simp; simp
  · rw [digRoot'_add_base_sub_one h₂, Nat.add_mod, h₃]; simp
    rw [digRoot'_eq_of_lt_base]; trans b - 1; apply Nat.mod_lt; simp; simp
  · unfold digRoot'; simp [h₁, h₂]

@[simp]
theorem digRoot'_le_base {n} : digRoot' b n ≤ b := by
  unfold digRoot'; split_ifs with h₁ h₂; iterate 2 simp
  trans b - 1; apply le_of_lt; apply Nat.mod_lt; simp; simp

theorem digRoot'_mul_base_sub_one_add {n k} (h : n ≠ 0) :
digRoot' b (k * (b - 1) + n) = digRoot' b n := by
  induction k; simp; nm k hk
  rwa [Nat.succ_mul, add_assoc, add_comm (b - 1), ←add_assoc,
    digRoot'_add_base_sub_one (by omega)]

@[simp]
theorem not_base_zero : ¬Base 0 := by
  rintro ⟨h⟩; omega

@[simp]
theorem digRoot'_digSum {n} : digRoot' b (digSum b n) = digRoot' b n := by
  induction n using Nat.strong_induction_on
  nm n ih
  unfold digSum
  simp [hb]
  split_ifs with h; rfl
  push_neg at h
  have h₁ := ih _ # hb.div_lt h
  rw [digRoot'_add, h₁, ←digRoot'_add]
  have h₂ : n % b + n / b = n - n / b * (b - 1)
  · rw [Nat.mul_sub, tsub_tsub_assoc (by simp) (by simp)]
    simp [Nat.mod_eq_sub_div_mul]
  rw [h₂]; clear h₂
  have h₂ : n / b * (b - 1) ≤ n
  · rw [Nat.mul_sub]; simp; trans n <;> simp
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h₂
  nth_rw 1 [hk]; simp
  rw [hk, digRoot'_mul_base_sub_one_add]
  rintro rfl; simp at hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  simp at hk; contrapose! hk; clear h hk h₁ h₂ ih
  apply ne_symm'; apply ne_of_lt
  rw [add_comm b, Nat.mul_sub, Nat.add_mul]; simp
  have h : n / b + 1 ≤ n / b * b + b
  · apply Nat.succ_le_of_lt
    cases b; simp at hb; nm b
    rw [Nat.mul_succ]; omega
  suffices h₁ : n / b * b + b < n + b + (n / b + 1)
  · exact Nat.sub_lt_right_of_lt_add h h₁
  clear h; cases b; simp; nm b; rw [Nat.mul_succ]
  suffices h : n / (b + 1) * b ≤ n; linarith
  change _ / _ * (b + 1 - 1) ≤ _
  generalize b + 1 = k at hb ⊢
  trans n / k * k <;> simp
  
theorem digRoot_eq_digRoot' {n} : digRoot b n = digRoot' b n := by
  induction n using Nat.strong_induction_on; nm n ih
  unfold digRoot; split_ifs with h₁; rw [digRoot'_eq_of_lt_base h₁]
  push_neg at h₁; rw [ih]; simp; rwa [digSum_lt_iff_base_le]

theorem digRoot_eq_of_lt_base {n} (h : n < b) : digRoot b n = n := by
  simp [digRoot_eq_digRoot', digRoot'_eq_of_lt_base h]

@[simp]
theorem digRoot_digRoot {n} : digRoot b (digRoot b n) = digRoot b n := by
  simp [digRoot_eq_digRoot']

@[simp]
theorem digRoot_base_two {n} : digRoot 2 n = if n = 0 then 0 else 1 := by
  simp [digRoot_eq_digRoot']

theorem digRoot_add_base {n} : digRoot b (n + b) = digRoot b (n + 1) := by
  simp [digRoot_eq_digRoot', digRoot'_add_base]

theorem digRoot_add_base_sub_one {n} (h : n ≠ 0) :
digRoot b (n + (b - 1)) = digRoot b n := by
  simp [digRoot_eq_digRoot', digRoot'_add_base_sub_one h]

@[simp]
theorem digRoot_base_sub_one : digRoot b (b - 1) = b - 1 := by
  simp [digRoot_eq_digRoot']

theorem digRoot_base_sub_one_add {n} (h : n ≠ 0) :
digRoot b (b - 1 + n) = digRoot b n := by
  simp [digRoot_eq_digRoot', digRoot'_base_sub_one_add h]

theorem digRoot_add {n m} :
digRoot b (n + m) = digRoot b (digRoot b n + digRoot b m) := by
  simp [digRoot_eq_digRoot']; exact digRoot'_add

@[simp]
theorem digRoot_le_base {n} : digRoot b n ≤ b := by
  simp [digRoot_eq_digRoot']

theorem digRoot_mul_base_sub_one_add {n k} (h : n ≠ 0) :
digRoot b (k * (b - 1) + n) = digRoot b n := by
  simp [digRoot_eq_digRoot', digRoot'_mul_base_sub_one_add h]

@[simp]
theorem digRoot_digSum {n} : digRoot b (digSum b n) = digRoot b n := by
  simp [digRoot_eq_digRoot']

instance : Base 10 := ⟨by norm_num⟩