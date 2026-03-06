import Projects.RealAnalysis.Limit

namespace RealAnalysis

def continuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ y, |y - x| < δ → |f y - f x| < ε

def continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, continuousAt f x

theorem continuousAt_of_continuous {f x} (h : continuous f) : continuousAt f x := h x

theorem tendsTo_of_continuousAt {a f L}
(h₁ : tendsTo a L) (h₂ : continuousAt f L) : tendsTo (f # a ·) (f L) := by
  intro e he; specialize h₂ e he; obtain ⟨d, hd, h₂⟩ := h₂
  specialize h₁ d hd; obtain ⟨N, h₁⟩ := h₁; have h₄ := h₁ N # by rfl
  have h₃ := h₂ _ h₄; use N; intro n hn; exact h₂ _ # h₁ n hn

theorem tendsTo_of_continuous {a f L}
(h₁ : tendsTo a L) (h₂ : continuous f) : tendsTo (f # a ·) (f L) :=
  tendsTo_of_continuousAt h₁ # h₂ L

theorem continuous_exp : continuous (·.exp) := by
  intro x ε hε
  generalize hδ : (1 + ε / 2 * (-x).exp).log = δ
  use δ
  constructor
  · subst hδ; apply Real.log_pos; simp; positivity
  intro y h₁
  dsimp
  wlog hy : x ≤ y with ih
  · push_neg at hy
    specialize @ih y ε hε _ rfl x _ # le_of_lt hy
    · clear ih
      rw [abs_sub_comm]
      apply lt_of_lt_of_le h₁
      rw [←hδ, Real.log_le_log_iff, add_le_add_iff_left,
        mul_le_mul_iff_of_pos_left, Real.exp_le_exp] <;> try positivity
      linarith
    rwa [abs_sub_comm]
  have h₂ := Real.exp_le_exp.mpr hy
  rw [abs_of_nonneg # by linarith] at h₁ ⊢
  calc
  _ ≤ (x + δ).exp - x.exp := by simp; linarith
  _ = x.exp * (δ.exp - 1) := by simp [Real.exp_add]; ring_nf
  _ = x.exp * (ε / 2 * (-x).exp) := by
    subst hδ; simp; rw [Real.exp_log # by positivity]; ring_nf
  _ = ε / 2 := by nth_rw 2 [mul_comm]; rw [←mul_assoc, ←Real.exp_add]; simp
  _ < _ := by linarith

theorem continuousAt_comp {f g x} (hf : continuousAt f (g x))
(hg : continuousAt g x) : continuousAt (f ∘ g) x := by
  intro ε hε
  specialize hf ε hε
  obtain ⟨δ, hδ, hf⟩ := hf
  specialize hg δ hδ
  obtain ⟨δ₁, hδ₁, hg⟩ := hg
  use δ₁, hδ₁
  intro y hy
  exact hf _ # hg _ hy

theorem continuous_comp {f g} (hf : continuous f)
(hg : continuous g) : continuous (f ∘ g) :=
  λ x => continuousAt_comp (hf # g x) (hg x)

theorem continuous_add_left {x} : continuous (x + ·) := by
  intro y ε hε; use ε, hε; intro z h₁; ring_nf; exact h₁

theorem continuous_add_right {x} : continuous (· + x) := by
  simp_rw [add_comm]; exact continuous_add_left

theorem continuous_neg : continuous (-·) := by
  intro x ε hε; use ε, hε; intro y h₁
  rw [←abs_neg]; ring_nf at h₁ ⊢; exact h₁

theorem continuous_sub_left {x} : continuous (x - ·) := by
  have h := continuous_comp (@continuous_add_left x) continuous_neg
  simp at h; ring_nf at h; exact h

theorem continuous_sub_right {x} : continuous (· - x) :=
  continuous_add_right

theorem continuous_mul_left {x} : continuous (x * ·) := by
  intro y ε hε; by_cases h₁ : x = 0
  · use 1; simp [h₁, hε]
  replace h₁ : 0 < |x|; simpa
  simp_rw [←mul_sub, abs_mul]
  generalize |x| = x at h₁ ⊢; nm p; clear p
  use ε / x, by positivity
  intro z h₃; exact (lt_div_iff₀' h₁).mp h₃

theorem continuous_mul_right {x} : continuous (· * x) := by
  simp_rw [mul_comm]; exact continuous_mul_left

theorem continuous_div_right {x} : continuous (· / x) :=
  continuous_mul_right

theorem continuous_rpow_left {b : ℝ} (hb : 0 < b) : continuous (b ^ ·) := by
  simp_rw [Real.rpow_eq_exp hb]
  exact continuous_comp continuous_exp continuous_mul_right

theorem tendsTo_exp {a L} (h : tendsTo a L) : tendsTo (a · |>.exp) L.exp :=
  tendsTo_of_continuous h continuous_exp

theorem continuousAt_log {x : ℝ} (hx : 0 < x) : continuousAt (·.log) x := by
  intro ε hε
  generalize hδ : x * (1 - (-ε).exp) = δ
  have h₁ : 0 < δ
  · subst hδ
    apply Left.mul_pos hx
    rw [sub_pos]
    simpa
  have h₂ : δ < x
  · subst hδ
    convert_to _ < x * 1; simp
    rw [mul_lt_mul_iff_of_pos_left hx]
    simp; positivity
  use δ, h₁
  intro y h₅
  dsimp
  rw [abs_sub_lt_iff'] at h₅ ⊢
  have hy : 0 < y; linarith
  rcases h₅ with ⟨h₃, h₄⟩
  have h₅ : 1 - (-ε).exp < ε.exp - 1
  · rw [Real.exp_neg]
    clear! x y δ
    generalize h₁ : ε.exp = x
    have h₂ : 1 < x; simpa [←h₁]
    suffices h₃ : (1 - x⁻¹) * x < (x - 1) * x; nlinarith
    field_simp
    suffices h₃ : 0 < (x - 1) ^ 2; ring_nf at h₃ ⊢; linarith
    apply sq_pos_of_pos; linarith
  constructor
  · rw [←Real.exp_lt_exp, Real.exp_sub, Real.exp_log hx, Real.exp_log hy]
    change _ > _; calc
    _ > x - δ := h₃
    _ = x - x * (1 - (-ε).exp) := by rw [←hδ]
    _ = x * (-ε).exp := by ring_nf
    _ = _ := by rw [Real.exp_neg, div_eq_mul_inv]
  · rw [←Real.exp_lt_exp, Real.exp_add, Real.exp_log hx, Real.exp_log hy]
    calc
    _ < x + δ := h₄
    _ = x + x * (1 - (-ε).exp) := by rw [←hδ]
    _ < x + x * (ε.exp - 1) := by nlinarith
    _ = x * ε.exp := by ring_nf

theorem continuousAt_logb {b x : ℝ} (hx : 0 < x) : continuousAt (Real.logb b) x :=
  continuousAt_comp (continuous_div_right _) (continuousAt_log hx)