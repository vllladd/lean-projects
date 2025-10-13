import AP.RealAnalysis.Continuity

namespace RealAnalysis

inductive RationalFn {ι : Type*} :
({α : Type*} → [Field α] → (ι → α) → α × List α) → Prop
| lit : (n : ℕ) → RationalFn (λ _ => (n, []))
| var : (i : ι) → RationalFn (λ F => (F i, []))
| neg : (f : _) → RationalFn f → RationalFn
  (λ F => match f F with | (x, cx) => (-x, cx))
| inv : (f : _) → RationalFn f → RationalFn
  (λ F => match f F with | (x, cx) => (x⁻¹, x :: cx))
| add : (f g : _) → RationalFn f → RationalFn g → RationalFn
  (λ F => match f F, g F with | (x, cx), (y, cy) => (x + y, cx ++ cy))
| mul : (f g : _) → RationalFn f → RationalFn g → RationalFn
  (λ F => match f F, g F with | (x, cx), (y, cy) => (x * y, cx ++ cy))

@[simp]
theorem RationalFn.lit' {ι : Type*} {n : ℕ} : @RationalFn ι (λ _ => (n, [])) :=
  RationalFn.lit n

@[simp]
theorem RationalFn.var' {ι : Type*} {i : ι} : @RationalFn ι (λ F => (F i, [])) :=
  RationalFn.var i

@[simp]
theorem RationalFn.neg'.{u, v} {ι : Type u}
{f : {α : Type v} → [Field α] → (ι → α) → α}
{cf : {α : Type v} → [Field α] → (ι → α) → List α} :
@RationalFn ι (λ F => (-f F, cf F)) ↔
@RationalFn ι (λ F => (f F, cf F)) := by
  constructor <;> intro h
  · have h₁ := @RationalFn.neg ι (λ F => (-f F, cf F))
    simp at h₁; exact h₁ h
  · exact RationalFn.neg _ h

@[simp]
theorem RationalFn.inv'.{u, v} {ι : Type u}
{f : {α : Type v} → [Field α] → (ι → α) → α}
{cf : {α : Type v} → [Field α] → (ι → α) → List α} :
@RationalFn ι (λ F => ((f F)⁻¹, cf F)) ↔
@RationalFn ι (λ F => (f F, cf F)) ∧
(∀ {α : Type v} [Field α] (F : ι → α), ∃ xs, cf F = f F :: xs) := by
  constructor <;> intro h
  · sorry
  · exact RationalFn.neg _ h

#check 0 #exit

-- example : RationalFn # λ F =>
-- ( (F "L" ^ 2 + 2 * F "L" + F "M") / (3 * F "M" + 2 - F "L" ^ 2)
-- , [3 * F "M" + 2 - F "L" ^ 2]
-- ) := by
--   apply RationalFn.div (λ F => (F "L" ^ 2 + 2 * F "L" + F "M", []))
--     (λ F => (3 * F "M" + 2 - F "L" ^ 2, []))
--   · apply RationalFn.add

#check 0 #exit

example {a b L M} (ha : tendsTo a L) (hb : tendsTo b M)
(h : 3 * M + 2 - L ^ 2 ≠ 0) :
tendsTo ((a ^ 2 + 2 * a + b) / (3 * b + 2 - a ^ 2))
((L ^ 2 + 2 * L + M) / (3 * M + 2 - L ^ 2)) := by
  revert h ha hb; apply Prove.h; simp
  simp only [Real.ofNat_eq, seq_ofNat_eq]; intros; infer_instance