import Projects.Util.Serializable.Serializable

namespace Serializable

open Serializer Deserializer

section Unit

@[simp]
def ser_unit (_ : Unit) : Ser Unit :=
  pure ()

@[simp]
def dser_unit : DSer Unit :=
  pure ()

@[simp]
def f_unit (_ : Unit) : List Bit :=
  []

@[simp]
def g_unit (_ : List Bit) : ℕ × Unit :=
  (0, ())

theorem cnd_unit : Cnd ser_unit dser_unit f_unit g_unit := by
  constructor <;> simp

instance : Serializable Unit where
  ser := ser_unit
  dser := dser_unit
  cnd := ⟨_, _, cnd_unit⟩

end Unit