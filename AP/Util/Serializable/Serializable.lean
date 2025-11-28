import AP.Util.Serializable.Serializer
import AP.Util.Serializable.Deserializer

namespace Serializable

abbrev Ser := StateM Serializer
abbrev DSer := StateM Deserializer

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