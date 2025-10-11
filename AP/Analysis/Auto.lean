import AP.Analysis.Continuity

namespace RealAnalysis

class Auto (P : Prop) : Prop where
  h : P

structure Prove (P : Prop) : Prop where
  h : P

@[simp]
theorem Prove.imp {P Q} : Prove (P → Q) ↔ (Auto P → Prove Q) :=
  ⟨λ ⟨pq⟩ ⟨p⟩ => ⟨pq p⟩, λ pq => ⟨λ p => pq ⟨p⟩ |>.1⟩⟩

@[simp low]
theorem Prove.end {P} : Prove P ↔ Auto P := ⟨(⟨·.1⟩), (⟨·.1⟩)⟩

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M] :
Auto # tendsTo (a + b) (L + M) := ⟨tendsTo_add ha.1 hb.1⟩

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M] :
Auto # tendsTo (a - b) (L - M) := ⟨tendsTo_sub ha.1 hb.1⟩

instance {a L} [ha : Auto # tendsTo a L] : Auto # tendsTo (-a) (-L) := ⟨tendsTo_neg ha.1⟩

instance {a L} [ha : Auto # tendsTo a L] [h : Auto # ¬(L = (0 : ℕ))] :
Auto # tendsTo a⁻¹ L⁻¹ where
  h := by apply tendsTo_inv _ ha.1; simp at h; exact h.1

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M]
[h : Auto # ¬(M = (0 : ℕ))] : Auto # tendsTo (a / b) (L / M) where
  h := by apply tendsTo_div _ ha.1 hb.1; simp at h; exact h.1

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M] :
Auto # tendsTo (a * b) (L * M) := ⟨tendsTo_mul ha.1 hb.1⟩

instance {a L} {k : ℕ} [ha : Auto # tendsTo a L] :
Auto # tendsTo (a ^ k) (L ^ k) := ⟨tendsTo_pow ha.1⟩

instance {n : ℕ} : Auto # tendsTo n n := ⟨tendsTo_const_cast⟩

example {a b L M} (ha : tendsTo a L) (hb : tendsTo b M)
(h : 3 * M + 2 - L ^ 2 ≠ 0) :
tendsTo ((a ^ 2 + 2 * a + b) / (3 * b + 2 - a ^ 2))
((L ^ 2 + 2 * L + M) / (3 * M + 2 - L ^ 2)) := by
  revert h ha hb; apply Prove.h; simp
  simp only [Real.ofNat_eq, seq_ofNat_eq]; intros; infer_instance