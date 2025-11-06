import AP.Util.Finset

import Mathlib.Data.Sym.Sym2

namespace Sym2

variable {α β : Type*}

def liftLe [ha : LinearOrder α] (p : Sym2 α) (f : α → α → β) : β :=
  p.lift ⟨λ a b => f (min a b) (max a b), by simp [min_comm, max_comm]⟩

def univ [ha₁ : DecidableEq α] [ha₂ : Fintype α] : Finset (Sym2 α) :=
  (Finset.univ : Finset (α × α)).image Sym2.mk

-----

@[simp]
theorem mem_univ [ha₁ : DecidableEq α] [ha₂ : Fintype α]
{p : Sym2 α} : p ∈ Sym2.univ := by
  simp only [univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  induction p; nm x y; use x, y

instance [ha₁ : DecidableEq α] [ha₂ : Fintype α] : Fintype (Sym2 α) where
  elems := Sym2.univ
  complete _ := Sym2.mem_univ