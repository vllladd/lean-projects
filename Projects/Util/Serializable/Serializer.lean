import Projects.Util.Basic

namespace Nat

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type}
variable {xs ys zs : List α}
variable {M : Type → Type} [H₁ : Monad M] [H₂ : LawfulMonad M]

-- #check 0 #exit

end List

namespace Bit

-- #check 0 #exit

end Bit

namespace BitVec

variable {w : ℕ}
variable {x y z : BitVec w}

-- #check 0 #exit

end BitVec

namespace UInt8

-- @[simp]
-- theorem mk_toBitVec_shiftLeft {x : BitVec 8} {y : UInt8} : ⟨x⟩ <<< y = ⟨x <<< y.1⟩ := by
--   rw [UInt8.ext_iff]
--   simp
--   simp [Nat.shiftLeft_eq]
--   have h₁ : x.toNat < 256
--   · exact BitVec.toNat_lt_size_pow
--   rw [y.toNat.eq_div_add_mod 8]
--   simp [-Nat.div_add_mod₂]
--   sorry

-- #check 0 #exit

end UInt8

namespace ByteArray

-- #check 0 #exit

end ByteArray

structure Serializer where
  bytes : ByteArray
  curByte : UInt8
  bitMask : UInt8
deriving DecidableEq

namespace Serializer

abbrev Ser := StateM Serializer

def empty : Serializer where
  bytes := ∅
  curByte := 0
  bitMask := 1

instance : EmptyCollection Serializer := ⟨empty⟩
theorem empty_def : (∅ : Serializer) = empty := rfl

def flush' : Ser Unit := modify # λ s =>
  { bytes := s.bytes.push s.curByte
    curByte := 0
    bitMask := 1
  }

def flush : Ser Unit := do
  bif (←get).bitMask != 0 then pure () else flush'

def finish : Ser Unit := do
  bif (←get).bitMask == 1 then pure () else flush'

def writeBit' (b : Bit) : Ser Unit := modify # λ s =>
  { bytes := s.bytes
    curByte := match b with
      | .B₀ => s.curByte
      | .B₁ => s.curByte ||| s.bitMask
    bitMask := s.bitMask <<< 1
  }

def writeBit (b : Bit) : Ser Unit := do
  writeBit' b; flush

def writeBits (bs : List Bit) : Ser Unit :=
  bs.forM writeBit

def getOutput : Ser ByteArray := do
  finish; gets (·.bytes)

def ofBits (bs : List Bit) : Serializer :=
  StateT.run (m := Id) (writeBits bs) ∅ |>.2

-- #check 0 #exit

-----

variable {α β γ : Type}
variable {s : Serializer}

@[simp]
theorem writeBits_nil : writeBits [] = pure () := rfl

@[simp]
theorem finish_empty : finish.run ∅ = ((), ∅) := rfl

@[simp]
theorem getOutput_empty : getOutput.run ∅ = (∅, ∅) := rfl

@[simp]
theorem ofBits_nil : ofBits [] = ∅ := rfl

@[simp]
theorem flush_empty : flush.run ∅ = ((), ∅) := rfl

@[simp]
theorem writeBits_cons {b bs} : writeBits (b :: bs) = (do writeBit b; writeBits bs) := rfl

@[simp]
theorem writeBits_append {bs₁ bs₂} :
writeBits (bs₁ ++ bs₂) = (do writeBits bs₁; writeBits bs₂) := by
  simp [writeBits]

@[simp]
theorem flush_flush' : flush.run (flush'.run s).2 = flush'.run s := rfl

@[simp]
theorem flush_flush : flush.run (flush.run s).2 = flush.run s := by
  nth_rw 2 [flush]; simp
  split_ifs with h <;> simp
  simp [flush, h]

@[simp]
theorem finish_finish {s} : finish.run (finish.run s).2 = finish.run s := by
  simp [finish]; split_ifs <;> simp_all [flush']

@[simp]
theorem flush_ofBits {bs} : flush.run (ofBits bs) = ((), ofBits bs) := by
  induction bs using List.reverseRecOn; simp
  unfold ofBits; simp [writeBit, writeBit']; rfl

@[simp]
theorem bytes_empty : (∅ : Serializer).bytes = ∅ := rfl

@[simp]
theorem ofBits_append {bs₁ bs₂} :
ofBits (bs₁ ++ bs₂) = (writeBits bs₂ |>.run (ofBits bs₁) |>.2) := by
  unfold ofBits; simp

@[simp]
theorem bitMask_empty : (∅ : Serializer).bitMask = 1 := rfl

theorem writeBit_eq_of_lt {b} (n : ℕ) (h₁ : s.bitMask = 1 <<< UInt8.ofNat n) (h₂ : n ≤ 6) :
(writeBit b).run s = ((), {s with curByte := s.curByte |||
(UInt8.ofBit b <<< UInt8.ofNat n), bitMask := 1 <<< UInt8.ofNat (n + 1)}) := by
  rw [Prod.ext_iff]; simp
  simp [writeBit, writeBit', flush, flush', h₁]
  rw [←UInt8.shiftLeft_add _ (by grind)]
  rotate_left; iterate 2
    rw [UInt8.lt_iff_toFin_lt]
    simp; change (_ : ℕ) % _ < _
    simp [UInt8.size]
    rw [Nat.mod_eq_of_lt] <;> omega
  rw [if_neg # by apply UInt8.one_shiftLeft_ne_zero]
  cases b <;> simp

theorem writeBits_eq_of_lt {bs} (n : ℕ)
(h₁ : s.bitMask = 1 <<< UInt8.ofNat n) (h₂ : n + bs.length ≤ 7) :
(writeBits bs).run s = ((), {s with curByte := s.curByte |||
(UInt8.ofBits bs <<< UInt8.ofNat n), bitMask := 1 <<< UInt8.ofNat (n + bs.length)}) := by
  rw [Prod.ext_iff]; simp
  induction bs using List.reverseRecOn
  · simp [←h₁]
  nm bs b ih
  simp
  rw [ih (by grind)]; clear ih
  rw [writeBit_eq_of_lt (n + bs.length) (by simp) (by grind)]
  simp [UInt8.or_assoc]
  simp [UInt8.ext_iff]
  generalize hx : (BitVec.ofBits 8 bs).toNat = x
  generalize hy : (BitVec.ofBit 8 b).toNat = y
  by_cases h₀ : bs = []
  · subst hx hy h₀
    simp at h₂
    simp
    congr
    rw [Nat.mod_eq_of_lt]
    exact BitVec.toNat_lt_size_pow
  simp [Nat.shiftLeft_eq]
  split_ands
  · congr
    rw [show n % 8 = n by rw [Nat.mod_eq_of_lt (by omega)]]
    repeat rw [Nat.mod_eq_of_lt];; rotate_left
    · subst hy
      cases b <;> simp
      change _ < 2 ^ 8; apply Nat.pow_lt_pow_of_lt (by omega); grind
    · subst hy
      cases b <;> simp
      · subst hx
        apply lt_of_lt_of_le (b := 2 ^ (bs.length + n))
        · simp [Nat.pow_add]
        change _ ≤ 2 ^ 8; apply Nat.pow_le_pow_of_le (by omega); grind
      · rw [Nat.mod_eq_of_lt]; rotate_left
        · change _ < 2 ^ 8; apply Nat.pow_lt_pow_of_lt (by omega); grind
        apply lt_of_lt_of_le (b := 2 ^ (bs.length + n + 1))
        · subst hx
          rw [show bs.length + n + 1 = bs.length + 1 + n by omega]
          rw [Nat.pow_add]
          simp
          rw [Nat.or_two_pow_eq_add_of (by simp)]
          simp [Nat.pow_add, Nat.mul_two]
        change _ ≤ 2 ^ 8; apply Nat.pow_le_pow_of_le (by omega)
        grind
    · grind
    · rw [Nat.mod_eq_of_lt (by grind)]
      subst hy
      cases b <;> simp
      change _ < 2 ^ 8; apply Nat.pow_lt_pow_of_lt (by omega); grind
    · apply lt_of_lt_of_le (b := 2 ^ bs.length * 2 ^ n)
      · subst hx
        simp
      rw [←Nat.pow_add]
      change _ ≤ 2 ^ 8
      apply Nat.pow_le_pow_of_le <;> grind
    rw [add_comm, Nat.pow_add, ←mul_assoc]
    rw [Nat.or_mul_two_pow]
  · repeat rw [Nat.mod_eq_of_lt];; ring_nf
    on_goal 1 => {grind}
    on_goal 2 => {grind}
    all_goals
      rw [Nat.mod_eq_of_lt (by grind)]
      change _ < 2 ^ 8; apply Nat.pow_lt_pow_of_lt (by omega)
      grind

-- #check 0 #exit

-- @[simp]
-- theorem fst_getOutput_ofBits {bs : List Bit} :
-- (getOutput.run (ofBits bs)).1 = .ofBits bs := by
--   generalize hn : bs.length = n
--   induction n using Nat.strong_induction_on generalizing bs
--   nm n ih
--   subst hn
--   by_cases h : bs = []
--   ·
--     subst h
--     simp
--   by_cases h₁ : bs.length < 8
--   ·
--     clear ih
--     rw [ByteArray.ofBits_of_length_le h (by omega)]
--     rename' bs => bs₂
--     
--     rw [ofBits, empty_def, empty]
--     -- generalize hn : bs.length = n at h₁
--     -- replace h : n ≠ 0; grind
--     -- generalize hx : (0 : UInt8) = x
--     -- generalize hm : (1 : UInt8) = m
--     rw [show (0 : UInt8) = UInt8.ofBits [] by simp]
--     rw [show (1 : UInt8) = 1 <<< (UInt8.ofNat ([] : List Bit).length) by simp]
--     rw [show bs₂ = [] ++ bs₂ by simp] at h h₁ ⊢
--     generalize hb₁ : [] = bs₁ at h₁
--     nth_rw 1 [hb₁] at h
--     nth_rw 1 [show bs₁ ++ bs₂ = bs₂ by grind]
--     clear hb₁
--     simp at h₁
--     
--     generalize hn : bs₁.length + bs₂.length = n
--     induction n generalizing bs₁ bs₂
--     ·
--       simp at hn
--       simp [hn] at h
--     nm n ih
--     
--     induction bs₂ using List.reverseRecOn
--     ·
--       clear ih
--       cases bs₁ using List.reverseRecOn
--       · simp at h
--       nm bs₁ b ih₁
--       clear ih₁
--       by_cases h₂ : bs₁ = []
--       · subst h₂
--         cases b <;> rfl
--       simp [getOutput, finish]
--       rw [if_neg]; rfl
--       change ¬(1 <<< UInt8.ofNat _ = 1)
--       rw [UInt8.one_shiftLeft_eq_one_iff]
--       simp; iterate 2 rw [Nat.mod_eq_of_lt]
--       all_goals grind
--     nm bs₂ b ih₁; clear ih₁
--     
--     by_cases h₂ : bs₁ ++ bs₂ = []
--     ·
--       simp at h₂
--       rcases h₂ with ⟨rfl, rfl⟩
--       cases b <;> rfl
--     
--     specialize @ih bs₂ bs₁ h₂ (by grind) (by grind)
--     simp
--     
--     simp [getOutput, finish, flush'] at ih
--     rw [if_neg] at ih; rotate_left
--     ·
--       clear ih
--       apply ne_of_congr (1 <<< UInt8.ofNat (bs₁.length + bs₂.length) = ·)
--       rw [UInt8.one_shiftLeft_eq_one_iff]
--       rw [Nat.mod_eq_of_lt (by grind)]
--       simp [show ¬(bs₁ = [] ∧ bs₂ = []) by grind]
--       symm
--       induction bs₂ generalizing bs₁ n
--       ·
--         simp
--       nm b₁ bs₂ ih
--       -- cases n
--       -- ·
--       --   grind
--       -- nm n
--       by_cases h₃ : bs₁ ++ bs₂ = []
--       ·
--         simp at h₃
--         rcases h₃ with ⟨rfl, rfl⟩
--         rfl
--       
--       specialize @ih n (bs₁ ++ [b₁]) (by grind) (by grind) (by grind) (by simp)
--       simp at ih ⊢
--       rw [writeBit_eq_of_lt bs₁.length rfl (by grind)]; simp
--       
--       -- rw [BitVec.mk_shiftLeft]
--       
--       sorry
--     
--     simp [getOutput, finish, flush']
--     rw [if_neg]; rotate_left
--     ·
--       clear ih
--       sorry
--     
--     simp at ih ⊢
--     
--     sorry
--   
--   sorry