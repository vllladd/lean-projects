import AP.Util.Serializable.Serializer
import AP.Util.Serializable.Deserializer

namespace Serializable

open Serializer

variable {α : Type}

structure Cnd (ser : α → Ser Unit) (dser : DSer α)
(f : α → List Bit) (g : List Bit → ℕ × α) : Prop where
  ser_eq_writeBits {x : α} : ser x = writeBits (f x)
  -- dser_eq_queryAllBits :
  -- dser = do
  --   let bs <- queryAllBits
  --   let (n, x) := g bs
  --   skipBits n
  --   pure x
  g_f_append {x : α} {bs : List Bit} : g (f x ++ bs) = (f x |>.length, x)
  g_snoc_zero {bs : List Bit} : g (bs ++ [0]) = g bs

-- def cnd {α : Type} (ser : α → Ser Unit) (dser : DSer α) : Prop :=
--   ∃ (f : α → List Bit) (g : List Bit → α × ℕ),
--   (∀ s x, (ser x |>.run s).2 = s.writeBits (f x)) ∧
--   (∀ d d' x, dser.run d = (x, d') ↔ (g d.getBits).1 = x ∧ d.drop (g d.getBits).2 = d') ∧
--   (∀ x y, f x <+: f y -> x = y) ∧
--   (∀ x bs, g (f x ++ bs).trim = (x, (f x).length)) ∧
--   (∀ bs1 bs2, (g bs1).1 = (g bs2).1 -> (g bs1).2 = (g bs2).2 ∧
--     bs1.take (g bs1).2 = bs2.take (g bs2).2)

-- #check 0 #exit

-- class Serializable (α : Type) where
--   ser : α → Ser Unit
--   dser : DSer α
--   h : Serializable.cnd ser dser