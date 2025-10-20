import AP.Util

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

-- There exists a person such that if they drinks, everyone drink

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
  humanityDiesOut_of_all_sterile : (∀ w, sterile w) → humanityDiesOut

example : World where
  Woman := String
  sterile _ := False
  humanityDiesOut := False
  nonempty_woman := inferInstance
  humanityDiesOut_of_all_sterile := by simp

variable [W : World]
open World

theorem exi_imp_humanityDiesOut : ∃ (w : Woman), sterile w → humanityDiesOut := by
  obtain ⟨w₀⟩ := nonempty_woman; by_cases h : ∀ w, sterile w
  use w₀; simp [humanityDiesOut_of_all_sterile h]
  push_neg at h; obtain ⟨w, h⟩ := h; use w; simp [h]