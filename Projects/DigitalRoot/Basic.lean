import Projects.DigitalRoot.Defs

namespace DigitalRoot

variable {b : ℕ} [hb : b.Base]

theorem digRoot_spec {b n} : digRoot b n = (Nat.digSum b)^[n] n ∧
Nat.digSum b (digRoot b n) = digRoot b n := by
  unfold digRoot
  apply Function.fix_spec n
  generalize hg : n = g
  nth_rw 2 [←hg]
  replace hg : n ≤ g; rw [hg]
  unfold Function.IsFixedPt
  induction g generalizing n
  · simp at hg; simp [hg]
  nm g ih
  rw [Function.iterate_succ, Function.comp_apply]
  by_cases h₂ : n < b
  · suffices h₃ : b.digSum (b.digSum n) = b.digSum n
    · rwa [Function.iterate_fixed h₃]
    nth_rw 2 [Nat.digSum]
    rw [Nat.toDigList]
    split_ifs with hb hn
    · symm; simp [hb]
    · simp [hn]
    unfold Nat.toDigList'
    simp [hn]
    rw [if_neg (by omega)]
    simp [Nat.div_eq_of_lt h₂, Nat.mod_eq_of_lt h₂]
  apply ih; clear ih
  rw [Nat.digSum, Nat.toDigList]
  split_ifs with hb hn <;> simp
  rw [Nat.toDigList']
  simp [hb, hn]
  have h₁ : (Nat.toDigList' b (n / b)).sum ≤ n / b; simp
  suffices : n % b + n / b < n; omega; clear h₁
  rw [add_comm]
  conv_rhs => rw [n.eq_div_mod b]
  rw [Nat.add_lt_add_iff_right]
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have h₁ : n / b * b ≤ n; simp
  have h₃ : n < n * b
  · rw [Nat.lt_mul_iff_one_lt_right] <;> omega
  have h₄ := n.lt_div_mul_add (b := b) (by omega)
  apply lt_of_lt_of_le h₄
  by_cases h₅ : 2 ≤ n / b * b
  · apply add_le_mul h₅ (by omega)
  simp [Nat.le_one_iff] at h₅
  rcases h₅ with ((rfl | H₁) | rfl) | ⟨H₁, rfl⟩ <;> grind

theorem digRoot_eq_iterate {b n} : digRoot b n = (Nat.digSum b)^[n] n :=
  digRoot_spec.1

@[simp]
theorem digSum_digRoot {b n} : Nat.digSum b (digRoot b n) = digRoot b n :=
  digRoot_spec.2

@[simp]
theorem digRoot_digSum {b n} : digRoot b (Nat.digSum b n) = digRoot b n :=
  Function.fix_apply digRoot_spec

@[simp]
theorem digRootAlt₁'_gas_zero {b n} : digRootAlt₁' b n 0 = n := rfl

@[simp]
theorem digRootAlt₁'_zero {b g} : digRootAlt₁' b 0 g = 0 := by
  induction g <;> simp [digRootAlt₁']; tauto

theorem digRootAlt₁'_base_le_one {b n g}
(h₁ : b ≤ 1) (h₂ : g ≠ 0) : digRootAlt₁' b n g = 0 := by
  cases g; simp at h₂; nm g; simp [digRootAlt₁']
  split_ifs with h₃; omega; simp [Nat.digSum_of_base_le_one h₁]

theorem digRootAlt₁'_of_lt_base {b n g} (h : n < b) : digRootAlt₁' b n g = n := by
  induction g <;> simp [digRootAlt₁']; omega

@[simp]
theorem digRootAlt₁'_gas_succ {b n g} :
digRootAlt₁' b n (g + 1) = digRootAlt₁' b (Nat.digSum b n) g := by
  by_cases hb : b ≤ 1
  · rw [digRootAlt₁'_base_le_one hb (by simp)]
    simp [Nat.digSum_of_base_le_one hb]
  replace hb : 2 ≤ b; omega
  nth_rw 1 [digRootAlt₁']
  split_ifs with h; on_goal 2 => rfl
  rw [Nat.digSum_of_lt_base h, digRootAlt₁'_of_lt_base h]

theorem digRoot_eq_digRootAlt₁ : digRoot = digRootAlt₁ := by
  ext b n
  rw [@digRoot_eq_iterate b n, digRootAlt₁]
  generalize hg : n = g
  suffices : digRootAlt₁' b n g = (Nat.digSum b)^[g] n
  · grind
  clear hg
  by_cases hb : b ≤ 1
  · cases g; simp; nm g
    rw [digRootAlt₁'_base_le_one hb (by simp)]
    rw [Function.iterate_succ']
    simp [Nat.digSum_of_base_le_one hb]
  replace hb : 2 ≤ b; omega
  induction g generalizing n
  · simp
  nm g ih
  simp [digRootAlt₁']
  split_ifs with h₁
  on_goal 2 => apply ih
  clear ih
  rw [Nat.digSum_of_lt_base h₁]
  induction g
  · simp
  nm g ih
  rw [Function.iterate_succ']
  simp [←ih]
  rw [Nat.digSum_of_lt_base h₁]

theorem digRoot_of_lt_base {b n} (h : n < b) : digRoot b n = n := by
  rw [digRoot_eq_digRootAlt₁, digRootAlt₁, digRootAlt₁'_of_lt_base h]

theorem digRoot_step {b n} : digRoot b n = digRoot b (Nat.digSum b n) := by
  simp

@[simp]
theorem digRoot_zero {b} : digRoot b 0 = 0 := by
  rw [digRoot_eq_digRootAlt₁, digRootAlt₁]; simp

theorem digRoot_of_base_le_one {b n} (hb : b ≤ 1) : digRoot b n = 0 := by
  cases n; simp; rw [digRoot_eq_digRootAlt₁, digRootAlt₁, digRootAlt₁'_base_le_one hb]; simp

theorem digRoot_eq_digRootAlt₂ : digRoot = digRootAlt₂ := by
  ext b n
  induction n using Nat.strong_induction_on
  nm n ih
  by_cases h₁ : n < b
  · rw [digRoot_of_lt_base h₁]
    unfold digRootAlt₂
    simp [Nat.base_iff]
    split_ifs with hb
    · omega
    rfl
  rw [digRootAlt₂]
  simp [Nat.base_iff]
  split_ifs with hb
  · rw [digRoot_of_base_le_one hb]
  replace hb : b.Base := ⟨by omega⟩
  rw [digRoot_step]
  apply ih
  rw [Nat.digSum_lt_iff_base_le]; omega

@[simp]
theorem digRoot_base_zero {n} : digRoot 0 n = 0 := by
  simp [digRoot_of_base_le_one]

@[simp]
theorem digRoot_base_one {n} : digRoot 1 n = 0 := by
  simp [digRoot_of_base_le_one]

theorem digRoot_lt_base_of {b n} (hb : b ≠ 0) : digRoot b n < b := by
  by_cases hb : b = 1; simp [hb]
  replace hb : b.Base := ⟨by omega⟩
  have h₁ := @digSum_digRoot b n; rw [Nat.digSum_eq_self_iff] at h₁; omega

@[simp]
theorem digRoot_lt_Nat.base_iff {b n} : digRoot b n < b ↔ b ≠ 0 := by
  constructor; omega; exact digRoot_lt_base_of

@[simp]
theorem digRoot_digRoot {b n} : digRoot b (digRoot b n) = digRoot b n := by
  nth_rw 1 [digRoot_eq_iterate]
  generalize hk : digRoot b n = k;
  rw [←hk]; nth_rw 1 [hk]; clear hk
  induction k <;> simp_all

@[simp]
theorem digRoot_base : digRoot b b = 1 := by
  have H := hb; rw [Nat.base_iff] at hb
  rw [digRoot_step, Nat.digSum_base, digRoot_of_lt_base]; omega

theorem digRoot_eq_digSum_of {n} (h : n + 1 < b * 2) : digRoot b n = Nat.digSum b n := by
  have H := hb; rw [Nat.base_iff] at hb; by_cases h₁ : n < b
  · rw [digRoot_of_lt_base h₁, Nat.digSum_of_lt_base h₁]
  simp at h₁
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  replace h : n + 1 < b; omega
  rw [add_comm b n]
  rw [digRoot_step]
  generalize hr : Nat.digSum b (n + b) = r
  rw [Nat.digSum_add_base_of_lt_base (by omega)] at hr
  subst hr
  rw [digRoot_of_lt_base h]

@[simp]
theorem digRoot_base_sub_one {b} : digRoot b (b - 1) = b - 1 := by
  cases b; simp; nm b; rw [digRoot_of_lt_base]; simp

@[simp]
theorem digRoot_base_two {n} : digRoot 2 n = if n = 0 then 0 else 1 := by
  rw [digRoot_eq_digRootAlt₂]
  fun_induction digRootAlt₂
  · simp_all [Nat.base_iff]
  · grind
  nm n h₁ h₂ ih
  clear h₁
  replace h₂ : 2 ≤ n; omega
  simpa using ih

@[simp]
theorem digRoot_one : digRoot b 1 = 1 := by
  have H := hb; rw [Nat.base_iff] at hb; rw [digRoot_of_lt_base]; omega

@[simp]
theorem digRoot_mul_base {b n} : digRoot b (n * b) = digRoot b n := by
  rw [digRoot_step]; simp only [Nat.digSum_mul_base, digRoot_digSum]

@[simp]
theorem digRoot_base_mul {b n} : digRoot b (b * n) = digRoot b n := by
  rw [mul_comm]; simp

@[simp]
theorem digRoot_mul_base_pow {b n k} : digRoot b (n * b ^ k) = digRoot b n := by
  rw [digRoot_step]; simp only [Nat.digSum_mul_base_pow, digRoot_digSum]

@[simp]
theorem digRoot_base_pow_mul {b n k} : digRoot b (b ^ k * n) = digRoot b n := by
  rw [mul_comm]; simp

@[simp]
theorem digRoot_mod_base_pred {n} : digRoot b n % (b - 1) = n % (b - 1) := by
  have H := hb; rw [Nat.base_iff] at hb
  induction n using Nat.ind_dig b
  · nm n h
    rw [digRoot_of_lt_base h]
  nm k c hk hc ih
  rw [digRoot_step, Nat.digSum_mul_base_add hc]
  rw [ih]
  rotate_left
  · apply lt_of_le_of_lt (b := k + c) <;> simp; omega
  clear ih
  rw [Nat.add_mod]
  rw [Nat.digSum_mod_base_pred]
  simp
  have h : k * b = k * (b - 1) + k
  · cases b; simp at hb; nm b
    simp [mul_add]
  rw [h]; clear h
  nth_rw 2 [Nat.add_mod]
  simp

@[simp]
theorem digRoot_eq_zero_iff {b n} : digRoot b n = 0 ↔ b ≤ 1 ∨ n = 0 := by
  symm; constructor
  · rintro (h | rfl)
    · rw [digRoot_of_base_le_one h]
    simp
  intro h
  by_contra! h₁
  rcases h₁ with ⟨hb, hn⟩
  replace hb : b.Base := ⟨by omega⟩
  contrapose! h; clear h
  induction n using Nat.ind_dig b
  · nm n h
    rwa [digRoot_of_lt_base h]
  nm k c hk hc ih
  rw [digRoot_step, Nat.digSum_mul_base_add hc]
  apply ih
  · simp; apply lt_of_le_of_lt (b := k) <;> simp; omega
  simp; omega

@[simp]
theorem digRoot_base_succ_le {b n} : digRoot (b + 1) n ≤ b := by
  rw [←Nat.lt_add_one_iff, digRoot_lt_Nat.base_iff]; omega

@[simp]
theorem digRoot_le_base_pred {b n} : digRoot b n ≤ b - 1 := by
  cases b <;> simp

theorem digRoot_add_base {b n} : digRoot b (n + b) = digRoot b (n + 1) := by
  by_cases hb : b ≤ 1
  · simp [digRoot_of_base_le_one hb]
  replace hb : 2 ≤ b; omega
  have h₁ := @digRoot_mod_base_pred b ⟨hb⟩ (n + b)
  have h₂ := @digRoot_mod_base_pred b ⟨hb⟩ (n + 1)
  have h : (n + b) % (b - 1) = (n + 1) % (b - 1)
  · cases b; simp at hb; nm b
    simp
    rw [show n + (b + 1) = n + 1 + b by omega]
    simp
  rw [h] at h₁; clear h
  have h₃ : digRoot b (n + b) = b - 1 ↔ digRoot b (n + 1) = b - 1
  · constructor
    · intro h; simp [h] at h₁; symm at h₁; simp [h₁] at h₂
      apply Nat.eq_of_le_and_mod_eq_zero; omega; simp; omega; simp; exact h₂
    · intro h; simp [h] at h₂; symm at h₂; simp [h₂] at h₁
      apply Nat.eq_of_le_and_mod_eq_zero; omega; simp; omega; simp; exact h₁
  by_cases h₄ : digRoot b (n + b) = b - 1
  · rw [h₄, h₃.mp h₄]
  have h₅ := h₄; rw [h₃] at h₅
  replace h₄ := lt_of_le_of_ne (by simp) h₄
  replace h₅ := lt_of_le_of_ne (by simp) h₅
  apply Nat.eq_of_mod_eq_mod _ h₄ h₅
  rw [h₁, h₂]

theorem digRoot_add_base_pred {b n} (hn : n ≠ 0) : digRoot b (n + (b - 1)) = digRoot b n := by
  by_cases hb : b ≤ 1
  · simp [digRoot_of_base_le_one hb]
  replace hb : 2 ≤ b; omega
  cases n
  · simp at hn
  nm n
  rw [show n + 1 + (b - 1) = n + b by omega]
  rw [digRoot_add_base]

@[csimp]
theorem digRoot_eq_digRootAlt₃ : digRoot = digRootAlt₃ := by
  ext b n
  by_cases hb : b ≤ 1
  · rw [digRoot_of_base_le_one hb]
    simp [digRootAlt₃, hb]
  have hb' := hb
  replace hb : 2 ≤ b; omega
  induction n using Nat.ind_step (b - 1)
  · nm n h
    rw [digRoot_of_lt_base (by omega)]
    simp [digRootAlt₃, hb']
    split_ifs with hn h₁
    · exact hn
    · exact Nat.eq_of_le_and_mod_eq_zero (by omega) hn (le_of_lt h) h₁
    rw [Nat.mod_eq_of_lt h]
  nm n ih
  by_cases hn : n = 0
  · subst hn
    simp [digRootAlt₃]
    omega
  rw [digRoot_add_base_pred hn]
  rw [ih _ (by omega)]; clear ih
  simp [digRootAlt₃, hb', hn]

theorem digRoot_add {n m} : digRoot b (n + m) = digRoot b (digRoot b n + digRoot b m) := by
  have H := hb; rw [Nat.base_iff] at hb
  have hb' : ¬(b ≤ 1); omega
  by_cases hn : n = 0; subst hn; simp
  by_cases hm : m = 0; subst hm; simp
  rw [digRoot_eq_digRootAlt₃]
  simp [digRootAlt₃, hb', hn, hm]
  cases b; simp at hb; nm b; simp
  by_cases h₁ : n % b = 0 <;> simp [h₁]
  · rw [Nat.add_mod n m, h₁]; simp
    by_cases h₂ : m % b = 0 <;> simp [h₂]
  by_cases h₂ : m % b = 0 <;> simp [h₂]
  rw [Nat.add_mod n m, h₂]; simp

@[simp]
theorem digRoot_add_digRoot_succ_lt_base_mul_two_iff {b n m} :
digRoot b n + digRoot b m + 1 < b * 2 ↔ b ≠ 0 := by
  use by omega
  intro h
  have h₁ : digRoot b n < b; simpa
  have h₂ : digRoot b m < b; simpa
  omega

theorem digRoot_add' {n m} :
digRoot b (n + m) = Nat.digSum b (digRoot b n + digRoot b m) := by
  have H := hb; rw [Nat.base_iff] at hb
  rw [digRoot_add]
  nth_rw 1 [digRoot_eq_digSum_of]
  simp

@[simp]
theorem digRoot_mul_base_add {n k} :
digRoot b (n * b + k) = digRoot b (n + k) := by
  have H := hb; rw [Nat.base_iff] at hb
  rw [digRoot_add]; simp; rw [←digRoot_add]

@[simp]
theorem digRoot_base_pred_add {b n} (h : n ≠ 0) :
digRoot b (b - 1 + n) = digRoot b n := by
  rwa [add_comm, digRoot_add_base_pred]

@[simp]
theorem digRoot_digRoot_add_left {n m} :
digRoot b (n + digRoot b m) = digRoot b (n + m) := by
  rw [digRoot_add]; simp; rw [←digRoot_add]

@[simp]
theorem digRoot_digRoot_add_right {n m} :
digRoot b (digRoot b n + m) = digRoot b (n + m) := by
  rw [add_comm]; simp; rw [add_comm]

@[simp]
theorem digRoot_eq_self_iff {n} : digRoot b n = n ↔ n < b := by
  constructor
  · intro h₁; rw [←h₁]; simp
  · intro h; rw [digRoot_of_lt_base h]

@[simp]
theorem digRoot_le_base {b n} : digRoot b n ≤ b := by
  by_cases hb : b ≤ 1
  · simp [digRoot_of_base_le_one hb]
  replace hb : b.Base := ⟨by omega⟩
  apply le_of_lt; simp