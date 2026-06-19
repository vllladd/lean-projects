import Projects.RealAnalysis.Continuity

namespace RealAnalysis

inductive RationalFn (ι : Type*) where
| one : RationalFn ι
| var : ι → RationalFn ι
| neg : RationalFn ι → RationalFn ι
| inv : RationalFn ι → RationalFn ι
| add : RationalFn ι → RationalFn ι → RationalFn ι
| mul : RationalFn ι → RationalFn ι → RationalFn ι

namespace RationalFn

class Cnd (α : Type*) [ha₁ : AddGroup α] [ha₂ : DivInvMonoid α] where
  h : ∀ (x : α), x * 0 = 0

instance : Cnd ℝ := ⟨by simp⟩
instance : Cnd # ℕ → ℝ := ⟨by simp⟩

variable {α : Type*} [ha₁ : AddGroup α] [ha₂ : DivInvMonoid α] [ha₃ : Cnd α]
variable {ι : Type*} {a b c : RationalFn ι} {F : ι → α}

omit ha₃

instance : One # RationalFn ι := ⟨.one⟩
theorem one_def : (1 : RationalFn ι) = .one := rfl

instance : Neg # RationalFn ι := ⟨.neg⟩
theorem neg_def {a : RationalFn ι} : -a = a.neg := rfl

instance : Inv # RationalFn ι := ⟨.inv⟩
theorem inv_def {a : RationalFn ι} : a⁻¹ = a.inv := rfl

instance : Add # RationalFn ι := ⟨.add⟩
theorem add_def {a b : RationalFn ι} : a + b = a.add b := rfl

instance : Mul # RationalFn ι := ⟨.mul⟩
theorem mul_def {a b : RationalFn ι} : a * b = a.mul b := rfl

def sub (a b : RationalFn ι) : RationalFn ι := a + -b
def div (a b : RationalFn ι) : RationalFn ι := a * b⁻¹

instance : Sub # RationalFn ι := ⟨.sub⟩
theorem sub_def {a b : RationalFn ι} : a - b = a.sub b := rfl

instance : Div # RationalFn ι := ⟨.div⟩
theorem div_def {a b : RationalFn ι} : a / b = a.div b := rfl

def zero : RationalFn ι := 1 - 1

instance : Zero # RationalFn ι := ⟨.zero⟩
theorem zero_def : (0 : RationalFn ι) = .zero := rfl

def pow (a : RationalFn ι) (n : ℕ) : RationalFn ι := match n with
| 0 => a * 0 + 1
| n + 1 => a.pow n * a

instance : Pow (RationalFn ι) ℕ := ⟨.pow⟩
theorem pow_def {a : RationalFn ι} {n : ℕ} : a ^ n = a.pow n := rfl

theorem pow_zero {a : RationalFn ι} : a ^ 0 = a * 0 + 1 := rfl
theorem pow_succ {a : RationalFn ι} {n : ℕ} : a ^ (n + 1) = a ^ n * a := rfl

def ofNat (n : ℕ) : RationalFn ι := match n with
| 0 => 0
| n + 1 => ofNat n + 1

instance {n} : OfNat (RationalFn ι) n := ⟨ofNat n⟩
theorem ofNat_def {n} : (OfNat.ofNat n : RationalFn ι) = ofNat n := rfl

@[simp]
def eval (a : RationalFn ι) (F : ι → α) : α := match a with
| .one => 1
| .var i => F i
| -a => -a.eval F
| a⁻¹ => (a.eval F)⁻¹
| a + b => a.eval F + b.eval F
| a * b => a.eval F * b.eval F

@[simp]
def cnd (a : RationalFn ι) (F : ι → α) : Prop := match a with
| .one => True
| .var _ => True
| -a => a.cnd F
| a⁻¹ => a.eval F ≠ 0 ∧ a.cnd F
| a + b => a.cnd F ∧ b.cnd F
| a * b => a.cnd F ∧ b.cnd F

@[simp]
theorem eval_sub : (a - b).eval F = a.eval F - b.eval F := by
  simp [sub_def, sub, sub_eq_add_neg]

@[simp]
theorem eval_div : (a / b).eval F = a.eval F / b.eval F := by
  simp [div_def, div, div_eq_mul_inv]

@[simp]
theorem eval_zero : (0 : RationalFn ι).eval F = 0 := by
  simp [zero_def, zero]

@[simp]
theorem eval_ofNat_zero' : (ofNat 0).eval F = 0 := by
  simp [ofNat]

@[simp]
theorem eval_ofNat_succ' {n} : (ofNat (n + 1)).eval F = (ofNat n).eval F + 1 := by
  simp [ofNat]

@[simp]
theorem eval_ofNat_zero : (ofNat(0) : RationalFn ι).eval F = 0 :=
  eval_ofNat_zero'

@[simp]
theorem eval_ofNat_succ {n} : (ofNat(n + 1) : RationalFn ι).eval F =
(ofNat(n) : RationalFn ι).eval F + 1 :=
  eval_ofNat_succ'

include ha₃ in @[simp]
theorem eval_pow_zero : (a ^ 0).eval F = 1 := by
  simp [pow_zero, ha₃.h]

include ha₃ in @[simp]
theorem eval_pow {n : ℕ} : (a ^ n).eval F = a.eval F ^ n := by
  induction n; simp; nm n ih; simp [_root_.pow_succ, pow_succ, ih]

@[simp]
theorem cnd_sub : (a - b).cnd F ↔ a.cnd F ∧ b.cnd F := by
  simp [sub_def, sub]

@[simp]
theorem cnd_div : (a / b).cnd F ↔ a.cnd F ∧ b.eval F ≠ 0 ∧ b.cnd F := by
  simp [div_def, div]

@[simp]
theorem cnd_zero' : (ofNat 0).cnd F := by
  simp [ofNat, zero_def, zero]

@[simp]
theorem cnd_ofNat' {n} : (ofNat n).cnd F := by
  induction n; simp; simpa [ofNat]

@[simp]
theorem cnd_zero : (ofNat(0) : RationalFn ι).cnd F :=
  cnd_zero'

@[simp]
theorem cnd_ofNat {n} : (ofNat(n) : RationalFn ι).cnd F :=
  cnd_ofNat'

@[simp]
theorem cnd_pow {n : ℕ} : (a ^ n).cnd F ↔ a.cnd F := by
  induction n <;> simp_all [pow_zero, pow_succ]

end RationalFn

theorem tendsTo_of_rationalFn {ι : Type*} {A : ι → ℕ → ℝ} {L : ι → ℝ}
{f : RationalFn ι} (h₁ : ∀ i, tendsTo (A i) (L i)) (h₂ : f.cnd L) :
tendsTo (f.eval A) (f.eval L) := by
  induction f
  · simp
  · apply h₁
  · nm a ih; exact tendsTo_neg # ih h₂
  · nm a ih; exact tendsTo_inv h₂.1 # ih h₂.2
  · nm a b ih₁ ih₂; exact tendsTo_add (ih₁ h₂.1) (ih₂ h₂.2)
  · nm a b ih₁ ih₂; exact tendsTo_mul (ih₁ h₂.1) (ih₂ h₂.2)

example {a b L M} (ha : tendsTo a L) (hb : tendsTo b M)
(h : 3 * M + 2 - L ^ 2 ≠ 0) :
tendsTo ((a ^ 2 + 2 * a + b) / (3 * b + 2 - a ^ 2)) ((
L ^ 2 + 2 * L + M) / (3 * M + 2 - L ^ 2)) := by
  revert h; obtain ⟨f, hf⟩ := @hv (RationalFn # Fin 2) #
    (.var 0 ^ 2 + 2 * .var 0 + .var 1) / (3 * .var 1 + 2 - .var 0 ^ 2)
  convert_to f.cnd ![L, M] → tendsTo (f.eval ![a, b]) (f.eval ![L, M]) using 0
  simp [hf]; ring_nf; apply tendsTo_of_rationalFn; intro i; fin_cases i <;> simpa