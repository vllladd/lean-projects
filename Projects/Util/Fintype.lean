import Projects.Util.Finset

noncomputable
def Finite.toFintype {α : Type*} (ha : Finite α) : Fintype α :=
  Fintype.ofFinite α

-----

namespace Fintype

variable {α : Type*} [ha : Fintype α]