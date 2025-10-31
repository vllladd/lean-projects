import AP.Util

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.Nat.Choose.Sum

namespace Misc

namespace P1

open Real

noncomputable
def f (n : ℕ) : ℝ :=
  let r := (n : ℝ)
  let a := r ^ r⁻¹
  (a ^ ·)^[n] 1

example : f 2 = √2 ^ √2 := by
  simp [f, sqrt_eq_rpow]

theorem f_lt {n} (h : 1 < n) : f n < n := by
  simp [f]
  obtain ⟨k, hk⟩ := hv n
  nth_rw 3 [←hk]
  clear hk
  generalize hr : (n : ℝ) = r
  have h₂ : 1 < r; rwa [←hr, Nat.one_lt_cast]
  clear! n
  induction k; simpa
  nm k ih
  rw [Function.iterate_succ']; simp
  generalize (λ x => (r ^ r⁻¹) ^ x)^[k] 1 = a at ih ⊢
  rw [←rpow_mul # by linarith]
  convert_to _ < r ^ 1; simp
  convert @rpow_lt_rpow_left_iff r (r⁻¹ * a) 1 h₂
    |>.mpr _; simp
  rw [mul_comm, ←div_eq_mul_inv]
  rw [div_lt_iff₀ # by linarith]
  simpa

example : f 2003 < 2003 := by
  apply f_lt; simp

end P1 namespace P2 -----

open Real

theorem sum_mul_le_112_of_sum_eq_12 {a b c : ℝ}
(ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 12) :
a * b * c + a * b + b * c + c * a ≤ 112 := by
  have h₁ : (a * b * c) ^ (3⁻¹ : ℝ) ≤ (a + b + c) / 3
  · apply gm_le_am_3 <;> positivity
  replace h₁ : a * b * c ≤ (a + b + c) ^ (3 : ℝ) / 27
  · rw [←rpow_le_rpow_iff (z := 3)] at h₁ <;> try positivity
    rw [rpow_inv_rpow] at h₁ <;> try positivity
    rw [div_rpow] at h₁ <;> try positivity
    norm_num at h₁ ⊢; exact h₁
  replace h₁ : a * b * c ≤ 64
  · rw [h] at h₁; norm_num at h₁; exact h₁
  suffices h₂ : a * b + b * c + c * a <= 48; linarith
  replace h₁ : c = 12 - (a + b); linarith
  suffices h₂ : a * b + (a + b) * (12 - (a + b)) ≤ 48
  · subst h₁; ring_nf at h₂ ⊢; exact h₂
  have h₂ : √(a * b) ≤ (a + b) / 2
  · apply gm_le_am_2 <;> positivity
  replace h₂ : a * b ≤ (a + b) ^ (2 : ℝ) / 4
  · rw [←rpow_le_rpow_iff (z := 2)] at h₂ <;> try positivity
    rw [sqrt_eq_rpow, one_div, rpow_inv_rpow] at h₂ <;> try positivity
    rw [div_rpow] at h₂ <;> try positivity
    norm_num at h₂ ⊢; simpa
  generalize a + b = x at h₁ h₂ ⊢
  suffices h₃ : x ^ (2 : ℝ) / 4 + x * (12 - x) ≤ 48; linarith
  suffices h₃ : 0 ≤ (x - 8) ^ 2; simp; linarith
  apply sq_nonneg

end P2 namespace P3 -----

theorem thm_6_div_mul_succ_mul {n : ℕ} : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  induction n; decide; nm n ih; ring_nf at ih
  convert_to 6 ∣ n + n ^ 2 * 3 + n ^ 3 * 2 + 6 * (n * 2 + n ^ 2 + 1); ring_nf
  rw [←Nat.dvd_add_iff_right ih]; simp

end P3 namespace P4 -----

--         1 * 8 + 1 = 9
--        12 * 8 + 2 = 98
--       123 * 8 + 3 = 987
--      1234 * 8 + 4 = 9876
--     12345 * 8 + 5 = 98765
--    123456 * 8 + 6 = 987654
--   1234567 * 8 + 7 = 9876543
--  12345678 * 8 + 8 = 98765432
-- 123456789 * 8 + 9 = 987654321

open Finset

variable {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n)
include hb hn

def f (b n : ℕ) : ℕ :=
  ∑ k ∈ range n, b ^ k

def g (b n : ℕ) : ℕ :=
  ∑ k ∈ range n, k * b ^ k

omit hn in
theorem base_sub_one_ne_zero : (b : ℝ) - 1 ≠ 0 := by
  cases b; simp at hb; nm b; simp; rintro rfl; simp at hb

omit hn in
theorem one_sub_base_ne_zero : 1 - (b : ℝ) ≠ 0 := by
  have h := base_sub_one_ne_zero hb; contrapose! h; linarith

theorem f_eq : (f b n : ℝ) = (1 - b ^ n) / (1 - b) := by
  have h : (f b n : ℝ) = b * f b n + 1 - b ^ n
  · calc
    _ = (∑ k ∈ range n, b ^ k : ℝ) := by rw [f]; simp
    _ = 1 + ∑ k ∈ range (n - 1), b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ']; ring_nf
    _ = 1 + ∑ k ∈ range n, b ^ (k + 1) - b ^ n := by
      cases n; simp at hn; nm n
      simp; rw [sum_range_succ]; ring_nf
    _ = 1 + b * ∑ k ∈ range n, b ^ k - b ^ n := by
      congr; simp_rw [pow_succ, ←sum_mul]; ring_nf; simp
    _ = _ := by rw [←f]; ring_nf
  have h₁ := one_sub_base_ne_zero hb
  field_simp; linarith

theorem g_eq' : (g b n : ℝ) = (b * f b n - n * b ^ n) / (1 - b) := by
  have h₁ := one_sub_base_ne_zero hb
  have h : (g b n : ℝ) = -n * b ^ n + b * g b n + b * f b n
  · calc
    _ = (∑ k ∈ range n, k * b ^ k : ℝ) := by rw [g]; simp
    _ = ∑ k ∈ range (n - 1), (k + 1) * b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ']; simp
    _ = -n * b ^ n + ∑ k ∈ range n, (k + 1) * b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ]; ring_nf; congr; ext; ring_nf
    _ = -n * b ^ n + b * ∑ k ∈ range n, (k + 1) * b ^ k := by
      congr; simp; simp_rw [pow_succ, ←mul_assoc, ←sum_mul]
      ring_nf; congr; ext; ring_nf
    _ = -n * b ^ n + (b * ∑ k ∈ range n, k * b ^ k + b * f b n) := by
      congr; simp; simp_rw [add_mul]
      rw [sum_add_distrib, mul_add]; congr; simp [f]
    _ = -n * b ^ n + b * g b n + b * f b n := by rw [←g]; ring_nf
  field_simp; linarith

theorem g_eq : (g b n : ℝ) = (b ^ n * (n * b - n - b) + b) / (1 - b) ^ 2 := by
  have h := g_eq' hb hn
  rw [f_eq hb hn] at h
  have h₁ := one_sub_base_ne_zero hb
  field_simp at h ⊢
  linarith

theorem main : (∑ k ∈ range n, (n - k : ℝ) * b ^ k) * (b - 2) + n =
∑ k ∈ range n, (b - n + k : ℝ) * b ^ k := by
  convert_to (∑ k ∈ range n, (n * b ^ k - k * b ^ k : ℝ)) * (b - 2 : ℝ) + n =
    ∑ k ∈ range n, ((b - n : ℝ) * b ^ k + k * b ^ k)
  · simp [sub_mul]
  · simp [add_mul, sub_mul]
  convert_to ((n * ∑ k ∈ range n, b ^ k : ℝ) -
    ∑ k ∈ range n, (k : ℝ) * b ^ k) * (b - 2 : ℝ) + n =
    (b - n : ℝ) * (∑ k ∈ range n, (b : ℝ) ^ k) + ∑ k ∈ range n, (k : ℝ) * b ^ k
  · simp [mul_sum]
  · simp [sum_add_distrib, mul_sum]
  have hf : ∑ k ∈ range n, (b : ℝ) ^ k = f b n; simp [f]
  have hg : ∑ k ∈ range n, (k : ℝ) * b ^ k = g b n; simp [g]
  simp; rw [hf, hg]; clear hf hg
  rw [f_eq hb hn, g_eq hb hn]
  have h₁ := one_sub_base_ne_zero hb
  field_simp
  generalize (b : ℝ) = b
  generalize (n : ℝ) = n
  nm x y; clear! x y
  ring_nf

end P4 namespace P5 -----

def le (n m : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), f 0 = n ∧ f k = m ∧ ∀ k, f k.succ = (f k).succ

theorem le_iff_nat_le {n m} : le n m ↔ n ≤ m := by
  constructor
  · rintro ⟨f, k, rfl, rfl, h⟩; induction k; rfl; rw [h]; linarith
  · intro h; obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    use (n + ·); simp [add_assoc]

end P5 namespace P5 -----

def f : ℕ → ℕ → ℕ
| n, 0 => n
| n, m + 1 => f (n + 1) m

theorem thm₁ {n m} : f n (m + 1) = f n m + 1 := by
  induction m generalizing n <;> simp_all [f]

theorem thm₂ {n} : f n n = n * 2 := by
  rw [Nat.mul_two]; apply n.rec (motive := λ k => f n k = n + k)
  simp_all [f]; intros; simp_all [thm₁]; rfl

end P5 namespace P6 -----

-- White horse is not horse

class World where
  HorseT : Type
  Horse : Set HorseT
  WhiteHorse : Set HorseT
  horse_univ : ∀ (e : HorseT), e ∈ Horse
  exi_non_white_horse : ∃ (e : HorseT), e ∉ WhiteHorse

example : World where
  HorseT := String
  Horse := Set.univ
  WhiteHorse := {}
  horse_univ e := by simp
  exi_non_white_horse := by simp

variable [W : World]
open World

theorem whiteHorse_ne_horse : WhiteHorse ≠ Horse := by
  obtain ⟨e, h⟩ := exi_non_white_horse
  apply ne_of_congr (e ∈ .); simp [h, horse_univ]

end P6 namespace P7 -----

-- There exists a person such that if they drinks, everyone drinks

class World where
  Person : Type
  drinks : Person → Prop
  nonempty_person : Nonempty Person

example : World where
  Person := String
  drinks _ := False
  nonempty_person := inferInstance

variable [W : World]
open World

theorem exi_imp_forall_drinks : ∃ (p : Person), drinks p → ∀ p', drinks p' := by
  obtain ⟨p₀⟩ := nonempty_person; by_cases h : ∀ p, drinks p
  use p₀; simp [h]; push_neg at h; obtain ⟨p, h⟩ := h; use p; simp [h]

end P7 namespace P8 -----

-- There exists a woman such that if she becomes sterile, the entire humanity will die out

class World where
  Woman : Type
  sterile : Woman → Prop
  humanityDiesOut : Prop
  nonempty_woman : Nonempty Woman
  humanityDiesOut_of_forall_sterile : (∀ w, sterile w) → humanityDiesOut

example : World where
  Woman := String
  sterile _ := False
  humanityDiesOut := False
  nonempty_woman := inferInstance
  humanityDiesOut_of_forall_sterile := by simp

variable [W : World]
open World

theorem exi_imp_humanityDiesOut : ∃ (w : Woman), sterile w → humanityDiesOut := by
  obtain ⟨w₀⟩ := nonempty_woman; by_cases h : ∀ w, sterile w
  use w₀; simp [humanityDiesOut_of_forall_sterile h]
  push_neg at h; obtain ⟨w, h⟩ := h; use w; simp [h]

end P8 namespace P9 -----

-- From MHA S04E17 at 13:19

noncomputable
abbrev μ : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume

theorem integral_congr {f g : ℝ → ℝ} {a b : ℝ}
(ha : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → f x = g x) :
∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ := by
  apply intervalIntegral.integral_congr; intro x h₁
  simp [Set.mem_uIcc] at h₁; apply h <;> cases h₁ <;> linarith

theorem one_add_sqrt_two_pos : (0 : ℝ) < 1 + √2 := by
  positivity

theorem log_one_add_sqrt_two_pos : (0 : ℝ) < (1 + √2).log := by
  rw [Real.log_pos_iff]; norm_num; positivity

theorem log_one_add_sqrt_two_nonneg : (0 : ℝ) ≤ (1 + √2).log :=
  le_of_lt log_one_add_sqrt_two_pos

theorem integrable_of_continuous {f : ℝ → ℝ} {a b : ℝ}
(h : Continuous f) : IntervalIntegrable f μ a b := by
  rw [intervalIntegrable_iff]; exact Continuous.integrableOn_uIoc h

theorem integral_exp {a b : ℝ} : ∫ x in a..b, x.exp ∂μ = b.exp - a.exp := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intros; apply Real.hasDerivAt_exp
  · apply integrable_of_continuous; continuity

set_option maxHeartbeats 1000000
theorem main : ∫ x in 0..(1 + √2).log,
(((x.exp - (-x).exp) / 2) ^ 3 * ((x.exp + (-x).exp) / 2) ^ 11) ∂μ = 107 / 28 := by
  rw [integral_congr (g := λ x => (x.exp - (-x).exp) ^ 3 / 2 ^ 3 *
    ((x.exp + (-x).exp) ^ 11 / 2 ^ 11)) log_one_add_sqrt_two_nonneg]
  rotate_left
  · intro x hx h₁
    simp_rw [←Real.rpow_natCast]
    congr
    · rw [Real.div_rpow # by simpa]; positivity
    · rw [Real.div_rpow]; positivity; norm_num
  simp_rw [show ∀ (a b c d : ℝ), a / b * (c / d) = (b * d)⁻¹ * (a * c)
    by intros; field_simp]
  rw [intervalIntegral.integral_const_mul]
  rw [inv_mul_eq_iff_eq_mul₀ # by norm_num]
  ring_nf
  simp_rw [←Real.rpow_natCast]
  simp_rw [←Real.exp_mul, ←Real.exp_add]
  ring_nf
  simp only [show ∀ (x y : ℝ), -(x * y) = (-y) * x by simp [mul_comm]]
  repeat rw [intervalIntegral.integral_add]
  repeat rw [intervalIntegral.integral_sub]
  any_goals apply integrable_of_continuous; continuity
  simp [-neg_mul, integral_exp]
  simp only [mul_comm _ # Real.log _, Real.exp_mul]
  rw [Real.exp_log one_add_sqrt_two_pos]
  simp
  field_simp
  ring_nf
  simp_rw [←Real.rpow_natCast]
  simp
  simp_rw [pow_succ]
  simp [mul_assoc]
  ring_nf

end P9 namespace P10 -----

/-
Let `a` be an infinite sequence of positive integers such that `a n ≤ 2025` for all positive
integers `n`. Suppose the geometric mean of the first `n` terms of this sequence is an integer
for all positive integers `n`. Prove that there exist positive integers `c` and `N` such that
`a n = c` for all `n ≥ N`.
-/

open Finset

theorem aux₁ {r N n c : ℕ} {a : ℕ → ℕ} (h₂ : ∀ (n : ℕ), a n ≤ r)
(h₃ : ∀ (n : ℕ), ∃ (k : ℕ), (∏ i ∈ range n, (a i : ℝ)) ^ (n : ℝ)⁻¹ = k)
(hrN : r < N) (hn : N ≤ n) (h₄ : 1 ≤ c)
(H₁ : ∀ (k : ℕ), N ≤ k → k ≤ n → (∏ i ∈ range k, a i : ℝ) ^ (k : ℝ)⁻¹ = c) : a n ≤ c := by
  by_contra! h₆
  replace h₆ : ∃ δ, 1 ≤ δ ∧ δ < r ∧ a n = c + δ
  · use a n - c
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h₆
    simp [hk]
    ring_nf
    split_ands
    · omega
    · suffices h : 1 + k < r; omega
      apply lt_of_lt_of_le (b := c + k + 1)
      · linarith
      rw [←hk]
      apply h₂
    · omega
  obtain ⟨δ, h₆, h₇, h₈⟩ := h₆
  have hn₁ : n ≠ 0
  · linarith
  have h₉ := H₁ n (by linarith) (by linarith)
  rw [Real.rpow_inv_eq] at h₉ <;> try positivity
  obtain ⟨c₁, hc₁⟩ := h₃ (n + 1)
  rw [prod_range_succ, h₉, h₈] at hc₁
  have H₂ : (c : ℝ) < c₁
  · rw [←hc₁, Real.lt_rpow_inv_iff_of_pos, Nat.cast_add, Nat.cast_add, Nat.cast_one,
      Real.rpow_add, mul_lt_mul_iff_right₀, Real.rpow_one, lt_add_iff_pos_right] <;> positivity
  have H₃ : (c₁ : ℝ) < c + 1
  · rw [←hc₁, Real.rpow_inv_lt_iff_of_pos, Nat.cast_add, mul_add] <;> try positivity
    have h : (c : ℝ) ^ (n : ℝ) * c = c ^ ((n + 1 : ℕ) : ℝ)
    · rw [Nat.cast_add, Nat.cast_one, Real.rpow_add, Real.rpow_one]; positivity
    rw [h]; clear h
    simp only [Real.rpow_natCast]
    apply lt_of_lt_of_le (b := (c : ℝ) ^ (n + 1) + (c : ℝ) ^ n * n)
    · simp; rw [mul_lt_mul_iff_right₀] <;> try positivity
      simp; linarith
    rw [add_comm (c : ℝ)]
    rw [Commute.add_pow # by simp [Commute]]
    rw [show n + 1 + 1 = 1 + 1 + n by ring_nf]
    rw [sum_range_add, sum_range_add]
    simp only [range_one, one_pow, one_mul, sum_singleton, tsub_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, add_zero, add_tsub_cancel_right, Nat.choose_one_right, Nat.cast_add,
      Nat.reduceAdd, add_assoc, add_le_add_iff_left]
    rw [mul_add]
    simp only [mul_one, add_assoc, le_add_iff_nonneg_right]
    positivity
  simp at H₂
  replace H₃ : c₁ < c + 1; exact_mod_cast H₃
  omega

theorem aux₂ {r N n c : ℕ} {w : ℝ} {a : ℕ → ℕ}
(h₃ : ∀ (n : ℕ), ∃ (k : ℕ), (∏ i ∈ range n, (a i : ℝ)) ^ (n : ℝ)⁻¹ = k)
(hw : max (r : ℝ) (Real.logb (1 + 1 / r) r) + 1 = w)
(hN : w < N) (hr : 1 ≤ r) (hrN : r < N) (hn : N ≤ n)
(hc : ∏ i ∈ range N, (a i : ℝ) = (c : ℝ) ^ (N : ℝ)) (h₅ : c ≤ r)
(H : ∀ (k : ℕ), N ≤ k → k < n → a k = c) (h₁ : ∀ (n : ℕ), 1 ≤ a n) (h₄ : 1 ≤ c)
(H₁ : ∀ (k : ℕ), N ≤ k → k ≤ n → (∏ i ∈ range k, a i : ℝ) ^ (k : ℝ)⁻¹ = c) : c ≤ a n := by
  by_contra! h₆
  replace h₆ : ∃ δ, 1 ≤ δ ∧ δ < c ∧ a n = c - δ
  · use c - a n
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h₆
    simp [hk]
    ring_nf
    split_ands
    · omega
    · linarith [h₁ n]
    · omega
  obtain ⟨δ, h₆, h₇, h₈⟩ := h₆
  have hn₁ : n ≠ 0
  · linarith
  have h₉ := H₁ n (by linarith) (by linarith)
  rw [Real.rpow_inv_eq] at h₉ <;> try positivity
  obtain ⟨c₁, hc₁⟩ := h₃ (n + 1)
  rw [prod_range_succ, h₉, h₈] at hc₁
  have H₀ : c ≠ 0
  · linarith
  have H₂ : (c₁ : ℝ) < c
  · rw [←hc₁, Real.rpow_inv_lt_iff_of_pos, Nat.cast_add, Nat.cast_sub, Nat.cast_one,
      Real.rpow_add, mul_lt_mul_iff_right₀, Real.rpow_one, sub_lt_self_iff]
    all_goals first | positivity | linarith
  have H₃ : (c - 1 : ℝ) < c₁
  · rw [←hc₁, Real.lt_rpow_inv_iff_of_pos, Nat.cast_sub, mul_sub]
      <;> try first | positivity | (try simp); linarith
    have h : (c : ℝ) ^ (n : ℝ) * c = c ^ ((n + 1 : ℕ) : ℝ)
    · rw [Nat.cast_add, Nat.cast_one, Real.rpow_add, Real.rpow_one]; positivity
    rw [h]; clear h
    simp only [Real.rpow_natCast]
    replace h₈ : a n + δ = c; omega
    replace h₈ : (a n + δ : ℝ) = c; exact_mod_cast h₈
    rw [show (δ : ℝ) = c - a n by linarith]
    cases c; simp at H₀; clear H₀; nm c
    simp
    have hc₂ : 1 ≤ c
    · cases c
      · simp at h₇
        subst h₇
        simp at h₆
      simp
    convert_to _ < (c + 1 : ℝ) ^ n * a n
    · ring_nf
    suffices h : (1 : ℝ) < a n / c * (1 + 1 / c) ^ n
    · suffices h₁ : (c : ℝ) ^ (n + 1) * (a n / c * (1 + 1 / c) ^ n) ≤ (c + 1) ^ n * (a n)
      · apply lt_of_lt_of_le _ h₁
        field_simp at h ⊢
        exact h
      clear h
      rw [pow_succ]
      field_simp
      simp_rw [←Real.rpow_natCast]
      rw [Real.div_rpow] <;> try positivity
      field_simp
      simp
    have G₁ : (c : ℝ) ≤ r * a n
    · suffices h : c ≤ r * a n; exact_mod_cast h
      trans c + 1; simp
      apply h₅.trans
      simp
      right
      specialize h₁ n
      linarith
    suffices h :  (1 : ℝ) < 1 / r * (1 + 1 / ↑c) ^ n
    · field_simp at h ⊢
      apply lt_of_le_of_lt G₁
      rwa [mul_lt_mul_iff_left₀]
      simp
      linarith [h₁ n]
    suffices h : (1 : ℝ) < 1 / r * (1 + 1 / r) ^ n
    · field_simp at h ⊢
      apply lt_of_lt_of_le h; clear h
      rw [pow_le_pow_iff_left₀] <;> try positivity
      field_simp
      ring_nf
      rw [add_comm]
      simp
      linarith
    suffices h : (r : ℝ) < (1 + 1 / r) ^ n
    · field_simp at h ⊢; exact h
    have G₁ : Real.logb (1 + 1 / r) r < n
    · replace hn : (N : ℝ) ≤ n; exact_mod_cast hn
      apply lt_of_lt_of_le _ hn
      apply lt_of_le_of_lt _ hN
      rw [←hw]
      trans w - 1
      rotate_left
      · rw [←hw]
        simp
      rw[ ←hw]
      simp
    apply lt_of_le_of_lt (b := (1 + 1 / r : ℝ) ^ (Real.logb (1 + 1 / r) r))
    rotate_left
    · simp_rw [←Real.rpow_natCast]
      rwa [Real.rpow_lt_rpow_left_iff]
      field_simp; simp
    rw [Real.rpow_logb] <;> try positivity
    simp
    linarith
  simp at H₂
  replace H₃ : c - 1 < c₁; exact_mod_cast H₃
  omega

theorem aux₃ {r : ℕ} {a : ℕ → ℕ} (h₁ : ∀ n, a n ≠ 0) (h₂ : ∀ n, a n ≤ r)
(h₃ : ∀ n, ∃ (k : ℕ), (∏ i ∈ range n, a i : ℝ) ^ (n : ℝ)⁻¹ = k) :
∃ c N, ∀ n, N ≤ n → a n = c := by
  generalize hw : max (r : ℝ) (Real.logb (1 + 1 / r) r) + 1 = w
  obtain ⟨N, hN⟩ := exists_nat_gt w
  have hr : 1 ≤ r
  · cases r
    · simp at h₂
      simp [h₂] at h₁
    simp
  have hrw : r < w
  · rw [←hw]; simp
  have hrN : r < N
  · suffices h : (r : ℝ) < N; exact_mod_cast h
    linarith
  have h0N : 0 < N
  · linarith
  obtain ⟨c, hc⟩ := h₃ N
  use c, N
  suffices h : ∀ n, N ≤ n → (∀ k, N ≤ k → k < n → a k = c) → a n = c
  · intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
    induction n using Nat.strong_induction_on
    nm n ih
    apply h
    · omega
    · intro k h₄ h₅
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₄; clear h₄
      apply ih
      omega
  intro n hn H
  simp [←Nat.one_le_iff_ne_zero] at h₁
  have h₄ : 1 ≤ c
  · suffices h : (1 : ℝ) ≤ c; exact_mod_cast h
    rw [←hc]
    rw [Real.le_rpow_inv_iff_of_pos] <;> try positivity
    simp
    apply one_le_prod_of_forall_one_le
    simp
    intro i hi
    apply h₁
  have h₅ : c ≤ r
  · suffices h : (c : ℝ) ≤ r; exact_mod_cast h
    rw [←hc]
    rw [Real.rpow_inv_le_iff_of_pos] <;> try positivity
    convert_to _ ≤ ∏ i ∈ range N, (r : ℝ); simp
    apply Finset.prod_le_prod
    · simp
    simp
    intro i hi
    linarith [h₂ i]
  rw [Real.rpow_inv_eq] at hc <;> try positivity
  have H₁ : ∀ k, N ≤ k → k ≤ n → (∏ i ∈ range k, a i : ℝ) ^ (k : ℝ)⁻¹ = c
  · intro k hk₁ hk₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk₁; clear hk₁
    rw [prod_range_add, Real.mul_rpow] <;> try positivity
    simp
    rw [hc]
    have h₆ : ∏ i ∈ range k, (a # N + i : ℝ) = (c : ℝ) ^ k
    · trans ∏ i ∈ range k, c
      rotate_left; simp
      apply prod_congr rfl
      simp
      intro m hm
      apply H
      · simp
      linarith
    rw [h₆]; clear h₆
    simp_rw [←Real.rpow_natCast]
    rw [←Real.mul_rpow, Real.rpow_inv_eq, ←Real.rpow_add] <;> try positivity
  apply le_antisymm
  · apply aux₁ <;> assumption
  · apply aux₂ <;> assumption

theorem main {a : ℕ → ℕ} (h₁ : ∀ n, a n ≠ 0) (h₂ : ∀ n, a n ≤ 2025)
(h₃ : ∀ n, ∃ (k : ℕ), (∏ i ∈ range n, a i : ℝ) ^ (n : ℝ)⁻¹ = k) :
∃ c N, ∀ n, N ≤ n → a n = c :=
  aux₃ h₁ h₂ h₃

theorem cntrex₁ : ¬∀ {a : ℕ → ℕ}
(_h₁ : ∀ n : ℕ, a n ≤ 2025)
(_h₂ : ∀ n : ℕ, n ≠ 0 → ∃ k : ℤ, k^n = ∏ i : Fin n, a i),
∃ c N : ℕ, c ≠ 0 ∧ N ≠ 0 ∧ ∀ n : ℕ, n ≥ N → a n = c := by
  push_neg
  use λ n => if n = 0 then 0 else if Odd n then 1 else 2
  split_ands
  · simp
    intro n
    split_ifs <;> norm_num
  · intro n hn
    use 0
    simp
    cases n
    · simp at hn
    rename_i n
    simp
    symm
    apply prod_eq_zero (i := 0)
    · simp
    · simp
  · simp
    intro c N hc hn
    by_cases h₁ : c = 1
    · use N * 2, by linarith
      simp [hn]
      aesop
    · use N * 2 + 1, by linarith
      simp
      rwa [eq_comm]

theorem main_alt_pnat {a : PNat → PNat}
(h₁ : ∀ n : PNat, (a n).val ≤ 2025)
(h₂ : ∀ n : PNat, ∃ (k : ℤ), k ^ n.val = ∏ i : Fin n, a ⟨i + 1, by simp⟩) :
∃ c N : PNat, ∀ n : PNat, n.val ≥ N.val → a n = c := by
  let a' (n : ℕ) : ℕ := a ⟨n + 1, by simp⟩ |>.1
  have h₃ := @main a'
  specialize h₃ _ _ _
  · intro n
    simp [a']
    generalize_proofs h₄
    cases h₅ : a ⟨n + 1, h₄⟩
    simp; linarith
  · intro n
    apply h₁
  · intro n
    cases n
    · use 1; simp
    nm n
    specialize h₂ ⟨n + 1, by simp⟩
    choose k hk using h₂
    symm at hk
    simp at hk ⊢
    use |k|.toNat
    rw [Real.rpow_inv_eq] <;> try positivity
    have h : k ^ (n + 1) = |k| ^ (n + 1)
    · by_cases h₄ : 0 ≤ k
      · rw [abs_of_nonneg h₄]
      push_neg at h₄
      rw [abs_of_neg h₄]
      have h₅ : 0 < k ^ (n + 1)
      · rw [←hk]
        positivity
      symm
      rcases Nat.even_or_odd (n + 1) with h₆ | h₆
      · apply h₆.neg_pow
      · exfalso
        have h₇ := h₆.neg_pow (-k)
        simp at h₇
        rw [h₇] at h₅
        contrapose! h₅; clear h₅
        simp
        apply Int.pow_nonneg
        linarith
    rw [h] at hk; clear h
    rw [show |k| = |k|.toNat by simp] at hk
    generalize |k|.toNat = k at hk ⊢; nm x; clear x
    rw [prod_fin_eq_prod_range] at hk
    simp at hk
    replace hk : (_ : ℝ) = _ := congrArg Int.cast hk
    push_cast at hk
    convert_to _ = (k : ℝ) ^ ((n + 1 : ℕ) : ℝ); simp
    rw [Real.rpow_natCast]
    rw [←hk]; clear hk
    apply prod_congr; rfl
    simp
    intro i h₄
    simp [h₄]
    rfl
  choose c N h₃ using h₃
  have hc : c ≠ 0
  · rintro rfl
    specialize h₃ N (by rfl)
    simp [a'] at h₃
    generalize_proofs h₄ at h₃
    cases h₅ : a ⟨N + 1, h₄⟩
    nm k hk
    simp [h₅] at h₃
    linarith
  use ⟨c, by positivity⟩, ⟨N + 1, by simp⟩
  rintro ⟨n, hn⟩ h₄
  simp at h₄
  cases n
  · simp at hn
  nm n
  specialize h₃ n (by linarith)
  rw [Subtype.eq_iff]
  exact h₃