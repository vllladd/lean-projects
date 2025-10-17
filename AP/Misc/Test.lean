import AP.Util

namespace Misc.Test

-- set_option linter.unusedVariables false in
-- example {a b c : ℝ}
-- (ha₁ : 0 < a) (hb₁ : 0 < b) (hc₁ : 0 < c)
-- (ha₂ : 0 ≤ a) (hb₂ : 0 ≤ b) (hc₂ : 0 ≤ c)
-- (ha₃ : a ≠ 0) (hb₃ : b ≠ 0) (hc₃ : c ≠ 0)
-- (ha₄ : 1 < a) (hb₄ : 1 < b) (hc₄ : 1 < c) :
-- a⁻¹ < b ↔ 1 < b * a := by
--   exact?

-- #check 0 #exit

namespace A1

def le (n m : ℕ) : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), f 0 = n ∧ f k = m ∧ ∀ k, f k.succ = (f k).succ

theorem le_iff_nat_le {n m} : le n m ↔ n ≤ m := by
  constructor
  · rintro ⟨f, k, rfl, rfl, h⟩; induction k; rfl; rw [h]; linarith
  · intro h; obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    use (n + ·); simp [add_assoc]

end A1 namespace A2 -----

def f : ℕ → ℕ → ℕ
| n, 0 => n
| n, m + 1 => f (n + 1) m

theorem thm₁ {n m} : f n (m + 1) = f n m + 1 := by
  induction m generalizing n <;> simp_all [f]

theorem thm₂ {n} : f n n = n * 2 := by
  rw [Nat.mul_two]; apply n.rec (motive := λ k => f n k = n + k)
  simp_all [f]; intros; simp_all [thm₁]; rfl

-----

section

open Real

namespace Real

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

-- #check 0 #exit

end Real

namespace Rat

theorem inv_lt_self_of_one_lt {x : ℚ} (h : 1 < x) : x⁻¹ < x := by
  replace h : (1 : ℝ) < x; exact_mod_cast h
  exact_mod_cast Real.inv_lt_self_of_one_lt h

theorem inv_le_self_of_one_le {x : ℚ} (h : 1 ≤ x) : x⁻¹ ≤ x := by
  replace h : (1 : ℝ) ≤ x; exact_mod_cast h
  exact_mod_cast Real.inv_le_self_of_one_le h

theorem lt_inv_self_of {x : ℚ} (h₁ : 0 < x) (h₂ : x < 1) : x < x⁻¹ := by
  replace h₁ : (0 : ℝ) < x; exact_mod_cast h₁
  replace h₂ : (x : ℝ) < 1; exact_mod_cast h₂
  exact_mod_cast Real.lt_inv_self_of h₁ h₂

theorem le_inv_self_of {x : ℚ} (h₁ : 0 < x) (h₂ : x ≤ 1) : x ≤ x⁻¹ := by
  replace h₁ : (0 : ℝ) < x; exact_mod_cast h₁
  replace h₂ : (x : ℝ) ≤ 1; exact_mod_cast h₂
  exact_mod_cast Real.le_inv_self_of h₁ h₂

-- #check 0 #exit

end Rat

theorem aux₁ {a : ℕ → ℚ} : IsCauSeq (abs : ℚ → ℚ) a ↔
∀ (ε : ℚ), 0 < ε → ε < 1 → ∃ (N : ℕ), ∀ n ≥ N, |a n - a N| < ε := by
  use λ h ε hε _ => h ε hε
  intro h ε hε'
  by_cases hε : ε < 1
  · apply h <;> assumption
  push_neg at hε
  specialize h (ε + 1)⁻¹ (by positivity) _
  · apply inv_lt_of_inv_lt₀ rfl; linarith
  obtain ⟨N, h⟩ := h
  use N
  intro n hn
  specialize h n hn
  apply h.trans
  apply lt_of_lt_of_le (b := ε⁻¹)
  · rw [inv_lt_inv₀] <;> try positivity;; simp
  exact Rat.inv_le_self_of_one_le hε

-- #check 0 #exit

theorem aux₂ : IsCauSeq (abs : ℚ → ℚ) (· + 1)⁻¹ := by
  rw [aux₁]
  intro ε hε hε'
  obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
  use n
  intro j hj
  simp
  rw [abs_of_nonpos]
  rotate_left
  · simp
    replace hj : (n : ℚ) + 1 ≤ j + 1; simpa
    rwa [inv_le_inv₀] <;> positivity
  simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  rename' j => k
  clear hj
  field_simp
  replace hn : (n + 1 : ℚ)⁻¹ < ε
  · rw [inv_lt_comm₀] <;> try positivity;; linarith
  rw [mul_comm, div_mul_eq_div_div]
  have h₁ : (k : ℚ) / (n + k + 1) < 1
  · rw [div_lt_comm₀] <;> try positivity;; linarith
  suffices : 1 / (n + 1) < ε
  · rw [div_lt_iff₀] <;> try positivity
    apply h₁.trans
    rw [inv_lt_iff_one_lt_mul₀] at hn <;> try positivity
    exact hn
  rwa [←inv_eq_one_div]

theorem aux₃ : ¬∀ {a : ℕ → ℚ} (_ : IsCauSeq abs a) (N : ℕ) (b : ℕ → ℚ)
(_ : IsCauSeq abs b) (_ : ∀ (n : ℕ), N ≤ n → ∃ x, 0 < x ∧
∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a n + b j),
∃ (x : ℚ), 0 < x ∧ ∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a j + b j := by
  push_neg
  use λ n => (n + 1)⁻¹
  use aux₂
  use 0
  use λ _ => 0
  constructor
  · intro e he
    simp
    use 0
    simpa
  simp
  constructor
  · intro N
    use (N + 1 : ℚ)⁻¹
    simp
    positivity
  intro x hx i
  obtain ⟨n, hn⟩ := exists_nat_gt x⁻¹
  use n + i, by linarith
  simp
  have h : (n : ℚ) < n + i + 1; linarith
  rw [inv_lt_comm₀] <;> try positivity
  apply h.trans'
  exact hn

theorem aux₄ : ¬∀ {a : ℕ → ℚ} (_ : IsCauSeq abs a) (N : ℕ) (e : ℕ → ℚ)
(he : IsCauSeq abs e) (_ : ∀ n, e n < 0) (_ : mk ⟨e, he⟩ < 0) (b : ℕ → ℚ) (_ : IsCauSeq abs b)
(_ : ∀ (n : ℕ), N ≤ n → ∃ x, 0 < x ∧ ∃ i, ∀ (j : ℕ),
i ≤ j → x ≤ a n - (-b - e) j - e j), ∃ x, 0 < x ∧ ∃ i, ∀ (j : ℕ),
i ≤ j → x ≤ a j - (-b - e) j - e j := by
  have H := aux₃; push_neg at H ⊢
  obtain ⟨a, ha, N, b, hb, H⟩ := H
  use a, ha, N, -1, IsCauSeq.const _ |>.neg, by simp
  constructor
  · convert_to (-1 : ℝ) < 0; rotate_left; norm_num
    convert_to _ = -((1 : ℕ) : ℝ); simp
    change mk _ = -mk ⟨_, _⟩
    rw [neg_mk]; rfl
  use b, hb
  simp; ring_nf; exact H

-- #check 0 #exit

theorem aux₅ : ¬∀ {a : ℕ → ℚ} (_ : IsCauSeq abs a) (N : ℕ) (b : ℕ → ℚ)
(_ : IsCauSeq abs b) (e : ℕ → ℚ) (he : IsCauSeq abs e)
(_ : ∀ n, e n < 0) (_ : mk ⟨e, he⟩ < 0)
(_ : ∀ (n : ℕ), N ≤ n → ∃ x, 0 < x ∧ ∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a n - b j - e j),
∃ x, 0 < x ∧ ∃ i, ∀ (j : ℕ), i ≤ j → x ≤ a j - b j - e j := by
  have H := aux₄; push_neg at H ⊢
  obtain ⟨a, ha, N, e, he, He, He', b, hb, H⟩ := H
  use a, ha, N, -b - e, hb.neg.sub he, e, he

-- #check 0 #exit

theorem aux₆ : ¬∀ {a : ℕ → ℚ} (ha : IsCauSeq abs a) (N : ℕ) (b : ℕ → ℚ)
(hb : IsCauSeq abs b) (e : ℕ → ℚ) (he : IsCauSeq abs e)
(He : ∀ n, e n < 0) (He' : mk ⟨e, he⟩ < 0)
(h : ∀ (n : ℕ), N ≤ n → mk ⟨e, he⟩ < ↑(a n) - mk ⟨b, hb⟩ ∧
↑(a n) - mk ⟨b, hb⟩ < -mk ⟨e, he⟩), ∃ x, 0 < x ∧ ∃ i, ∀ (j : ℕ),
i ≤ j → x ≤ a j - b j - e j := by
  have H := aux₅; push_neg at H ⊢
  obtain ⟨a, ha, N, b, hb, e, he, He, He', h, H⟩ := H
  use a, ha, N, b, hb, e, he, He, He'
  refine ⟨?_, H⟩
  intro n hn
  specialize h n hn
  constructor
  · change _ < mk ⟨_, _⟩ - _; simpa [mk_sub_mk]
  suffices H₁ : a n + mk ⟨e, he⟩ < mk ⟨b, hb⟩; linarith
  -- change mk ⟨e, he⟩ < a n - mk ⟨b, hb⟩ at h
  -- change CauSeq.Pos (λ i => a n - b i - e i) at h
  -- change CauSeq.Pos _ at h
  replace h : mk ⟨e, he⟩ < a n - mk ⟨b, hb⟩
  · change _ < mk ⟨_, _⟩ - _; simpa [mk_sub_mk]
  replace h : mk ⟨b, hb⟩ + mk ⟨e, he⟩ < a n; linarith
  change mk ⟨e, he⟩ < 0 at He'
  sorry

-- #check 0 #exit

theorem abs_sub_cauchy_lt_of_exi {a : ℕ → ℚ} {x ε : ℝ} (ha : IsCauSeq abs a)
(h : ∃ N, ∀ n, N ≤ n → |a n - x| < ε) : |x - mk ⟨a, ha⟩| < ε := by
  rw [abs_sub_comm]
  obtain ⟨N, h⟩ := h
  obtain ⟨b, hb, rfl⟩ := x.exi_mk_cauchy
  rw [mk_sub_mk]
  simp_rw [abs_lt] at h ⊢
  constructor
  · obtain ⟨e, he, H⟩ := (-ε).exi_mk_cauchy
    rw [neg_eq_iff_eq_neg] at H
    subst H
    simp at h ⊢
    change ∃ _, _
    simp
    
    replace h : ∀ n, N ≤ n → mk ⟨e, he⟩ < ↑(a n) - mk ⟨b, hb⟩
    · intro n hn; specialize h n hn; exact h.1
    change ∀ n, N ≤ n → mk ⟨e, he⟩ < mk ⟨_, _⟩ - mk ⟨b, hb⟩ at h
    simp [mk_sub_mk] at h
    change ∀ n, N ≤ n → ∃ _, _ at h
    dsimp at h
    
    sorry
  · sorry

end