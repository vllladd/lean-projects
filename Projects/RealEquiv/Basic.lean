import Projects.RealEquiv.Defs
import Projects.RealAnalysis

namespace RealEquiv

variable {r : ℝ}
variable {bs bs₁ bs₂ bs₃ : Bits}

@[simp]
theorem Bits.get_cons {b} : (bs.cons b).get = (λ i => if i = 0 then b else bs.get (i - 1)) := by
  ext i; cases i <;> simp [cons]

@[simp]
theorem Bits.get_drop {n} : (bs.drop n).get = λ i => bs.get (n + i) := rfl

@[simp]
theorem Bits.get_tail : bs.tail.get = λ i => bs.get (i + 1) := by
  simp [tail, add_comm]

@[simp]
theorem Bits.cons_tail_get_zero : bs.tail.cons (bs.get 0) = bs := by
  ext i; cases i <;> simp

theorem Bits.cs {P : Bits → Prop} (h : ∀ ⦃b⦄ ⦃bs : Bits⦄, P (bs.cons b)) : ∀ bs, P bs := by
  intro bs; specialize @h (bs.get 0) bs.tail; simp at h; exact h

@[simp]
theorem Bits.tail_cons {b} : (bs.cons b).tail = bs := by
  ext; simp

@[simp]
theorem Bits.end_cons {b} : (bs.cons b).end = bs.end := by
  simp [Bits.end]
  congr! 2 with e
  simp [eventually]
  constructor <;> rintro ⟨N, h⟩ <;> use N + 1 <;> intro n hn
  · specialize h (n + 1) (by omega)
    rw [if_neg # by omega] at h
    simp at h; exact h
  · rw [if_neg # by omega]; exact h (n - 1) (by omega)

@[simp]
theorem Bits.end_drop {n} : (bs.drop n).end = bs.end := by
  simp [Bits.end]
  congr! 2 with e
  simp [eventually]
  constructor <;> rintro ⟨N, h⟩ <;> use N + n <;> intro i hi
  · specialize h (i - n) (by omega); convert h; omega
  · apply h; omega

@[simp]
theorem Bits.end_tail : bs.tail.end = bs.end := by
  simp [tail]

theorem Bits.end_eq_of_getNat {n} (h : bs.getNat = (n, bs₁)) : bs₁.end = bs.end := by
  simp [getNat] at h; rcases h with ⟨-, rfl⟩; simp

@[simp]
theorem prepend_nil : bs.prepend [] = bs := rfl

@[simp]
theorem prepend_cons {b xs} : bs.prepend (b :: xs) = (bs.prepend xs).cons b := rfl

@[simp]
theorem Bits.get_prepend {xs} : (bs.prepend xs).get = λ i =>
if h : i < xs.length then xs[i] else bs.get (i - xs.length) := by
  ext i; induction xs generalizing i <;> simp; cases i <;> simp_all

theorem Bits.eq_prepend_of_end_eq_none (h : bs.end = none) (b : Bit) :
∃ n, (bs.drop (n + 1) |>.cons b |>.prepend # .replicate n b.not) = bs := by
  simp [Bits.end, eventually] at h
  specialize h b.not 0
  simp at h
  generalize hn : Nat.find h = n
  use n
  ext i
  simp
  have H₁ := Nat.find_spec h
  rw [hn] at H₁
  symm
  split_ifs with h₁ h₂
  · have H₂ := Nat.find_min h (m := i) (by omega)
    simp at H₂
    exact H₂
  · replace h₁ : i = n; omega; clear h₂; subst h₁
    exact H₁
  · replace h₁ : n < i; omega; clear h₂
    congr
    omega

@[simp]
theorem Bits.take_sub {n k} : bs.take (n - k) = (bs.take n).take (n - k) := by
  simp [take]
  by_cases h : n < k
  · simp [show n - k = 0 by omega]
  push Not at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp [List.range_add]
  rw [List.ext_getElem_iff]
  simp
  intro i h₁
  simp [List.getElem_append]
  intro h₃
  congr
  omega

@[simp]
theorem Bits.length_take {n} : (bs.take n).length = n := by
  simp [take]

-- -- #check 0 #exit
-- 
-- open RealAnalysis in @[simp]
-- theorem isCauSeq_bitsToRat_take : IsCauSeq abs λ i => bitsToRat (bs.take i) := by
--   rw [isCauSeq_iff_isCauchy, isCauchy_iff_alt₁]
--   intro e he
--   dsimp
--   obtain ⟨N, h⟩ := exists_nat_gt # Real.logb 2 e⁻¹
--   use N
--   intro n hn
--   obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
--   nth_rw 2 [show N = N + n - n by simp]
--   rw [Bits.take_sub]; simp
--   generalize hx : bs.take (N + n) = xs
--   have h₁ : xs.length = N + n; simp [←hx]
--   simp [bitsToRat, h₁]
--   sorry
-- 
-- -- #check 0 #exit
-- 
-- theorem ofBitsAux₁_eq_real_mk : ofBitsAux₁ bs =
-- Real.mk ⟨λ i => bitsToRat # bs.take i, isCauSeq_bitsToRat_take⟩ := by
--   sorry
-- 
-- -- #check 0 #exit
-- 
-- theorem toBits_ofBits : toBits (ofBits bs) = bs := by
--   unfold ofBits
--   split <;> nm x h <;> clear x
--   ·
--     cases bs using Bits.cs <;> nm s bs
--     simp at h ⊢
--     unfold ofBitsAux₂
--     split
--     nm x n bs₁ h₁; clear x
--     simp [Bits.getNat] at h₁
--     rcases h₁ with ⟨rfl, rfl⟩
--     obtain ⟨n, h₁⟩ := Bits.eq_prepend_of_end_eq_none h 0
--     simp at h₁
--     have h₂ : bs.indexOf 0 = some n
--     ·
--       simp [Bits.indexOf]
--       apply Nat.find!_eq_of
--       ·
--         rw [←h₁]
--         simp
--       intro i h₂
--       rw [←h₁]
--       simp
--       omega
--     simp [h₂]
--     generalize h₃ : bs.drop (n + 1) = bs₁ at h₁ ⊢
--     
--     simp [ofBitsAux₁]
--     sorry
--   ·
--     sorry
--   ·
--     sorry