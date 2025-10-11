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

instance {a L} [ha : Auto # tendsTo a L] [h : Auto # L ≠ 0] :
Auto # tendsTo a⁻¹ L⁻¹ := ⟨tendsTo_inv h.1 ha.1⟩

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M]
[h : Auto # M ≠ 0] : Auto # tendsTo (a / b) (L / M) := ⟨tendsTo_div h.1 ha.1 hb.1⟩

instance {a b L M} [ha : Auto # tendsTo a L] [hb : Auto # tendsTo b M] :
Auto # tendsTo (a * b) (L * M) := ⟨tendsTo_mul ha.1 hb.1⟩

instance {a L} {k : ℕ} [ha : Auto # tendsTo a L] :
Auto # tendsTo (a ^ k) (L ^ k) := ⟨tendsTo_pow ha.1⟩

instance x {n} {inst} [H : ValidOfNat inst] :
Auto # tendsTo (@OfNat.ofNat _ n inst) n := ⟨tendsTo_const_ofNat⟩

-- #check 0 #exit

set_option trace.Meta.synthInstance true
-- set_option pp.all true

example : Auto # tendsTo 2 2 := by
  infer_instance

#check 0 #exit

example {a b L M} (ha : tendsTo a L) (hb : tendsTo b M)
(h : 3 * L + 2 - L ^ 2 ≠ 0) :
tendsTo ((a ^ 2 + 2 * a + b) / (3 * b + 2 - a ^ 2))
((L ^ 2 + 2 * L + M) / (3 * L + 2 - L ^ 2)) := by
  revert h ha hb; apply Prove.h; simp; intros
  infer_instance