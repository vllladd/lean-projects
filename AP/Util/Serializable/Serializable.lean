import AP.Util.Serializable.Serializer
import AP.Util.Serializable.Deserializer

abbrev Ser := StateM Serializer
abbrev DSer := StateM Deserializer

-- def Serializable.cnd {α : Type*} (ser : α → Ser Unit) (dser : DSer Unit) : Prop :=
--   ∃ (f g : α → List Bit),
--   (∀ s x, ser x s = s.pushBits (f x)) ∧
--   (∀ ds ds', dser ds = (x, ds') <-> (g ds.getBits).1 = x ∧ ds.drop (g ds.getBits).2 = ds') ∧
--   (∀ x y, f x <:+ f y -> x = y) ∧
--   (∀ x bs, g (f x ++ bs).trim = (x, (f x).length)) ∧
--   (∀ bs1 bs2, (g bs1).1 = (g bs2).1 -> (g bs1).2 = (g bs2).2 ∧
--     bs1.take (g bs1).2 = bs2.take (g bs2).2)
-- 
-- class Serializable (α : Type*) where
--   ser : α → Ser Unit
--   dser : DSer Unit
--   h : Serializable.cnd ser dser