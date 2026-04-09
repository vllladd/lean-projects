import Projects.Misc.NatPair.Defs

namespace NatPair

@[simp]
theorem pair_zero {m} : pair 0 m = m * 2 := by
  simp [pair]

@[simp]
theorem fst_mul_two {n} : fst (n * 2) = 0 := by
  rw [fst]; simp

@[simp]
theorem fst_pair {n m} : fst (pair n m) = n := by
  induction n; simp
  nm n ih
  have h₁ : Odd # pair (n + 1) m
  · simp [pair]; grind
  rw [fst, dif_neg # by simpa]
  simp [Nat.one_add]
  rw [Nat.odd_iff_exi] at h₁
  choose k h₁ using h₁
  rw [h₁]; replace h₁ := congrArg (· - 1) h₁
  simp [pair] at h₁
  simp [Nat.pow_add] at h₁
  replace h₁ : k = 2 ^ n * (m * 2 + 1) - 1; grind
  convert ih using 2
  simpa [pair]

@[simp]
theorem pair_add_one {n m} : pair n m + 1 = 2 ^ n * (m * 2 + 1) := by
  grind [pair]

@[simp]
theorem snd_pair {n m} : snd (pair n m) = m := by
  simp [snd]

@[simp]
theorem odd_add_one_div_two_pow_fst {n} : Odd # (n + 1) / 2 ^ fst n := by
  fun_induction fst; simp_all
  nm n h ih; simp at h; simp [Nat.pow_add]; convert ih using 1
  rw [Nat.odd_iff_exi] at h; obtain ⟨n, rfl⟩ := h
  simp; trans (n + 1) * 2 / (2 * 2 ^ fst n); grind; simp

@[simp]
theorem two_pow_fst_le_succ {n} : 2 ^ fst n ≤ n + 1 := by
  fun_induction fst; simp
  nm n h ih; simp at h
  simp [Nat.pow_add]; grind

@[simp]
theorem two_pow_fst_mul_sub_one_eq_self {n} : 2 ^ fst n * ((n + 1) / 2 ^ fst n) - 1 = n := by
  fun_induction fst; simp
  nm n h ih; simp at h
  simp [Nat.pow_add]
  rw [Nat.odd_iff_exi] at h
  obtain ⟨n, rfl⟩ := h
  simp at ih ⊢
  simp [Nat.add_assoc]
  rw [show n * 2 + 2 = (n + 1) * 2 by omega]
  simp
  rw [Nat.sub_eq_iff_eq_add] at ih
  on_goal 2 => simp [Nat.one_le_iff_ne_zero]
  rw [mul_assoc, ih]; omega

@[simp]
theorem pair_fst_snd {r} : pair (fst r) (snd r) = r := by
  simp [pair, snd]
  rw [Nat.div_mul_cancel]
  on_goal 2 => apply Even.two_dvd; simp
  rw [Nat.sub_add_cancel]
  on_goal 2 => apply Nat.one_le_of_odd; simp
  simp

@[simp]
theorem leftInverse_g_f : g.LeftInverse f := by
  intro; simp [f, g]

@[simp]
theorem rightInverse_g_f : g.RightInverse f := by
  intro; simp [f, g]