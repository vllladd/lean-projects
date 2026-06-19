import Projects.Util.Finset

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Real

noncomputable
def am (xs : List ℝ) : ℝ :=
  xs.sum / xs.length

noncomputable
def gm (xs : List ℝ) : ℝ :=
  xs.prod ^ (xs.length : ℝ)⁻¹

open Classical in noncomputable
def mk! (f : ℕ → ℚ) : ℝ :=
  if h : IsCauSeq abs f then .mk ⟨f, h⟩ else 0

-----

theorem add_inv {a b : ℝ} (h : b ≠ 0) : a + b⁻¹ = (a * b + 1) / b := by
  field_simp

theorem pow_lt_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ b < c ↔ a < c ^ (1 / b) := by
  iterate rw [Real.rpow_lt_iff_lt_log, Real.lt_rpow_iff_log_lt] <;>
    try linarith
  have h : Real.log c = b * ((1 / b) * Real.log c) := by
    rw [←mul_assoc, mul_div, mul_one, div_self # by linarith]
    simp
  nth_rw 1 [h]
  rw [mul_lt_mul_iff_of_pos_left hb]

theorem add_inv_pow_lt_exp_one_of {a : ℝ} (h : 0 ≤ a) :
    (1 + a⁻¹) ^ a < Real.exp 1 := by
  rw [le_iff_eq_or_lt] at h; rcases h with rfl | h; simp
  rw [Real.rpow_def_of_pos # by positivity, Real.exp_lt_exp, (by simp : a = a⁻¹⁻¹),
    mul_inv_lt_iff₀' # by positivity, add_comm]; simp
  nth_rw 2 [(by simp : a⁻¹ = a⁻¹ + 1 - 1)]; apply Real.log_lt_sub_one_of_pos
  positivity; apply ne_of_congr (· - 1); simp; linarith

theorem ofNat_eq {n} : (OfNat.ofNat n : ℝ) = n := by
  rw [ext_cauchy_iff]; (iterate 2 cases n; simp; nm n); rfl

theorem list_sum_map_mul_left {xs : List ℝ} {w : ℝ} :
(xs.map (w * ·)).sum = w * xs.sum := by
  induction xs; simp; nm x xs ih; simp [ih]; ring_nf

theorem list_sum_map_mul_right {xs : List ℝ} {w : ℝ} :
(xs.map (· * w)).sum = xs.sum * w := by
  induction xs; simp; nm x xs ih; simp [ih]; ring_nf

theorem gm_le_am (xs : List ℝ) (h₁ : xs ≠ []) (h₂ : ∀ x ∈ xs, 0 ≤ x) : gm xs ≤ am xs := by
  have h_len : xs.length ≠ 0; simpa
  have h_len' : (xs.length : ℝ) ≠ 0; simpa
  have h₃ := @Real.geom_mean_le_arith_mean_weighted
  specialize @h₃ ℕ (Finset.range xs.length) (λ _ => xs.length⁻¹) (xs[·]!) _ _ _
  · simp only [Finset.mem_range, inv_nonneg, Nat.cast_nonneg, implies_true]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_inv_cancel₀ h_len'
  · simp; intro k hk; rw [List.getElem?_eq_getElem hk]
    simp; simp_all only [ne_eq, List.length_eq_zero_iff, not_false_eq_true,
      Nat.cast_eq_zero, List.getElem_mem]
  rw [Finset.sum_range_list_get! (f := ((xs.length : ℝ)⁻¹ * ·)),
    Finset.prod_range_list_get! (f := (· ^ (xs.length : ℝ)⁻¹)),
    Real.list_prod_map_rpow _ h₂, Real.list_sum_map_mul_left] at h₃
  convert! h₃; unfold am; field_simp

theorem gm_le_am_2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a * b) ≤ (a + b) / 2 := by
  have h := gm_le_am (xs := [a, b])
  specialize h nofun (by simp [ha, hb])
  simp [am, gm] at h; simpa [Real.sqrt_eq_rpow]

theorem gm_le_am_3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
(a * b * c) ^ (3 : ℝ)⁻¹ ≤ (a + b + c) / 3 := by
  have h := gm_le_am (xs := [a, b, c])
  specialize h nofun (by simp [ha, hb, hc])
  simp [am, gm] at h; simpa [add_assoc, mul_assoc]

theorem log_eq_logb {a : ℝ} : a.log = Real.logb (Real.exp 1) a := by
  simp [logb]

theorem eq_of_log_eq_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
(h : a.log = b.log) : a = b := by
  replace h := congrArg (·.exp) h
  rw [exp_log ha, exp_log hb] at h; exact h

theorem log_eq_log_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
a.log = b.log ↔ a = b := by
  use eq_of_log_eq_log ha hb; rintro rfl; rfl

theorem rpow_eq_exp {a b : ℝ} (ha : 0 < a) : a ^ b = (b * a.log).exp := by
  rw [←log_eq_log_iff] <;> try positivity;; simp [log_rpow ha b]

-----

theorem exi_mk_cauchy {x : ℝ} : ∃ (a : ℕ → ℚ) (ha : IsCauSeq abs a), x = .mk ⟨a, ha⟩ := by
  rcases x with ⟨⟨a, ha⟩⟩; use a, ha; rfl

theorem _root_.IsCauSeq.sub {a b : ℕ → ℚ}
(ha : IsCauSeq abs a) (hb : IsCauSeq abs b) : IsCauSeq abs (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem mk_sub_mk {a b : ℕ → ℚ} {ha : IsCauSeq abs a} {hb : IsCauSeq abs b} :
mk ⟨a, ha⟩ - mk ⟨b, hb⟩ = mk ⟨a - b, ha.sub hb⟩ := by
  rw [←ofCauchy_sub]; rfl

theorem _root_.IsCauSeq.abs' {a : ℕ → ℚ} (ha : IsCauSeq abs a) : IsCauSeq abs |a| := by
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, ha⟩ := ha
  use N
  intro n hn
  specialize ha n hn
  simp
  exact lt_of_le_of_lt (abs_abs_sub_abs_le _ _) ha

theorem neg_mk {a : ℕ → ℚ} {ha : IsCauSeq abs a} : -mk ⟨a, ha⟩ = mk ⟨-a, ha.neg⟩ := by
  rw [←ofCauchy_neg]; rfl

theorem abs_mk {a : ℕ → ℚ} {ha : IsCauSeq abs a} : |mk ⟨a, ha⟩| = mk ⟨|a|, ha.abs'⟩ := by
  change max _ _ = _; rw [neg_mk]; exact ofCauchy_sup _ _ |>.symm

-----

theorem inv_lt_self_of_one_lt {x : ℝ} (h : 1 < x) : x⁻¹ < x := by
  have h₁ : 0 < x⁻¹; positivity
  replace h : 1 < x * x; nlinarith
  replace h : 1 * x⁻¹ < x * x * x⁻¹; nlinarith
  simp at h; exact h

theorem inv_le_self_of_one_le {x : ℝ} (h : 1 ≤ x) : x⁻¹ ≤ x := by
  rw [le_iff_eq_or_lt] at h; rcases h with rfl | h; norm_num
  exact le_of_lt # inv_lt_self_of_one_lt h

theorem lt_inv_self_of {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1) : x < x⁻¹ := by
  replace h : 1 < x⁻¹; rw [one_lt_inv_iff₀]; exact ⟨h₁, h₂⟩
  nth_rw 1 [←inv_inv x]; exact inv_lt_self_of_one_lt h

theorem le_inv_self_of {x : ℝ} (h₁ : 0 < x) (h₂ : x ≤ 1) : x ≤ x⁻¹ := by
  rw [le_iff_eq_or_lt] at h₂; rcases h₂ with rfl | h₂; norm_num
  exact le_of_lt # lt_inv_self_of h₁ h₂

theorem sqrt_add_one_sub_lt_one {x} (hx : 0 < x) : √(x + 1) - √x < 1 := by
  have h₁ : √x < √(x + 1); rw [sqrt_lt_sqrt_iff] <;> linarith
  rw [←sq_lt_sq₀, sub_sq, sq_sqrt, sq_sqrt] <;> try first | positivity | linarith
  suffices H : x < √(x + x ^ 2)
  · rw [mul_assoc, ←sqrt_mul'] <;> try positivity
    ring_nf at H ⊢; linarith
  rw [lt_sqrt] <;> try positivity;; simpa

@[simp]
theorem abs_sqrt {x : ℝ} : |√x| = √x := by
  rw [abs_of_nonneg]; positivity

theorem abs_sub_lt_of_lt_lt_half {a b c d : ℝ}
(h₁ : |a - c| < d / 2) (h₂ : |b - c| < d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_lt_of_le_lt_half {a b c d : ℝ}
(h₁ : |a - c| ≤ d / 2) (h₂ : |b - c| < d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_lt_of_lt_le_half {a b c d : ℝ}
(h₁ : |a - c| < d / 2) (h₂ : |b - c| ≤ d / 2) : |a - b| < d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ < _ := by linarith

theorem abs_sub_le_of_le_le_half {a b c d : ℝ}
(h₁ : |a - c| ≤ d / 2) (h₂ : |b - c| ≤ d / 2) : |a - b| ≤ d := by
  calc
  _ = |a - c - (b - c)| := by ring_nf
  _ ≤ |a - c| + |b - c| := abs_sub _ _
  _ ≤ _ := by linarith

theorem sqrt_add {a b : ℝ} (h₁ : 0 ≤ b) (h₂ : b ≤ a) :
√(a + b) = √((a + √(a ^ 2 - b ^ 2)) / 2) + √((a - √(a ^ 2 - b ^ 2)) / 2) := by
  have h₃ : 0 ≤ a; linarith
  have h₄ : 0 ≤ (a - √(a ^ 2 - b ^ 2)) / 2
  · apply div_nonneg _ # by norm_num
    simp
    rw [sqrt_le_iff]
    simp
    split_ands <;> positivity
  have h₅ : 0 ≤ (a + √(a ^ 2 - b ^ 2)) / 2
  · apply h₄.trans
    rw [div_le_div_iff_of_pos_right] <;> try positivity
    rw [sub_eq_add_neg]
    simp
  have h₆ : 0 ≤ a ^ 2 - b ^ 2
  · nlinarith
  rw [←sq_eq_sq₀, sq_sqrt, add_sq, sq_sqrt, sq_sqrt] <;> try positivity
  ring_nf
  simp
  symm
  rw [←sqrt_mul] <;> try positivity
  ring_nf
  field_simp
  rw [sq_sqrt] <;> try positivity
  ring_nf
  field_simp
  norm_num
  rwa [sqrt_sq]

theorem sqrt_sub {a b : ℝ} (h₁ : 0 ≤ b) (h₂ : b ≤ a) :
√(a - b) = √((a + √(a ^ 2 - b ^ 2)) / 2) - √((a - √(a ^ 2 - b ^ 2)) / 2) := by
  have h₃ : 0 ≤ a; linarith
  have h₄ : 0 ≤ (a - √(a ^ 2 - b ^ 2)) / 2
  · apply div_nonneg _ # by norm_num
    simp
    rw [sqrt_le_iff]
    simp
    split_ands <;> positivity
  have h₀ : 0 ≤ (a + √(a ^ 2 - b ^ 2)) / 2 - (a - √(a ^ 2 - b ^ 2)) / 2
  · simp
    rw [div_le_div_iff_of_pos_right] <;> try positivity
    rw [sub_eq_add_neg]
    simp
  have h₈ : 0 ≤ √((a + √(a ^ 2 - b ^ 2)) / 2) - √((a - √(a ^ 2 - b ^ 2)) / 2)
  · simp only [sub_nonneg] at h₀ ⊢
    exact sqrt_le_sqrt h₀
  have h₅ : 0 ≤ (a + √(a ^ 2 - b ^ 2)) / 2
  · linarith
  have h₆ : 0 ≤ a ^ 2 - b ^ 2
  · nlinarith
  have h₇ : 0 ≤ a - b; linarith
  rw [←sq_eq_sq₀, sq_sqrt, sub_sq, sq_sqrt, sq_sqrt] <;> try positivity
  ring_nf
  simp
  symm
  rw [←sqrt_mul] <;> try positivity
  ring_nf
  field_simp
  rw [sq_sqrt] <;> try positivity
  ring_nf
  field_simp
  norm_num
  rwa [sqrt_sq]

theorem sqrt_add_sqrt {a b : ℝ} (h₁ : 0 ≤ b) (h₂ : √b ≤ a) :
√(a + √b) = √((a + √(a ^ 2 - b)) / 2) + √((a - √(a ^ 2 - b)) / 2) := by
  rw [sqrt_add, sq_sqrt] <;> try first | positivity | linarith

theorem sqrt_sub_sqrt {a b : ℝ} (h₁ : 0 ≤ b) (h₂ : √b ≤ a) :
√(a - √b) = √((a + √(a ^ 2 - b)) / 2) - √((a - √(a ^ 2 - b)) / 2) := by
  rw [sqrt_sub, sq_sqrt] <;> try first | positivity | linarith

@[simp]
theorem sq_sqrt_nat {n : ℕ} : √ofNat(n) ^ 2 = ofNat(n) := by
  rw [Real.ofNat_eq, sq_sqrt]; simp

@[simp]
theorem sqrt_sq_nat {n : ℕ} : √(ofNat(n) ^ 2) = ofNat(n) := by
  rw [Real.ofNat_eq, sqrt_sq]; simp

theorem sqrt_eq_of_neg {a : ℝ} (h : a < 0) : √a = 0 := by
  simp [sqrt, toNNReal, max_eq_right_of_lt h]

theorem sqrt_eq_of_nonpos {a : ℝ} (h : a ≤ 0) : √a = 0 := by
  rw [le_iff_eq_or_lt] at h; rcases h with rfl | h; simp; exact sqrt_eq_of_neg h

attribute [simp] sq_nonneg

@[simp]
theorem le_sq_self_iff {a : ℝ} : a ≤ a ^ 2 ↔ a ≤ 0 ∨ 1 ≤ a := by
  constructor
  · intro h
    rw [or_iff_not_imp_left]
    intro h₁
    nlinarith
  · rintro (h | h)
    · apply h.trans
      simp
    nlinarith

@[simp]
theorem lt_sq_self_iff {a : ℝ} : a < a ^ 2 ↔ a < 0 ∨ 1 < a := by
  constructor
  · intro h
    rw [or_iff_not_imp_left]
    intro h₁
    nlinarith
  · rintro (h | h)
    · apply lt_of_lt_of_le h
      simp
    nlinarith

@[simp]
theorem sqrt_le_self_iff {a : ℝ} : √a ≤ a ↔ a = 0 ∨ 1 ≤ a := by
  by_cases h : a < 0
  · rw [sqrt_eq_of_neg h]
    simp [ne_of_lt h]
    constructor <;> intro h <;> linarith
  push Not at h
  simp [sqrt_le_iff, h]
  rw [le_iff_eq_or_lt] at h
  rcases h with rfl | h; simp
  simp [not_le_of_gt h, ne_symm' # ne_of_lt h]

theorem pow_rpow_inv {a : ℝ} {n : ℕ} (ha : 0 ≤ a) (hn : n ≠ 0) :
(a ^ ofNat(n)) ^ (ofNat(n) : ℝ)⁻¹ = a := by
  rw [instOfNatNat]; simp [Real.ofNat_eq]; rw [←rpow_natCast]
  rw [rpow_rpow_inv ha # by exact_mod_cast hn]

theorem rpow_inv_pow {a : ℝ} {n : ℕ} (ha : 0 ≤ a) (hn : n ≠ 0) :
(a ^ (ofNat(n) : ℝ)⁻¹) ^ ofNat(n) = a := by
  rw [instOfNatNat]; simp [ofNat_eq]; rw [←rpow_natCast]
  rw [rpow_inv_rpow ha # by exact_mod_cast hn]