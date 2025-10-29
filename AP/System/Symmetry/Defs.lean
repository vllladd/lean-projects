import AP.System.Invariant

namespace System

universe u
variable {S T : Type u} {sys : System S T}

@[ext]
structure Symmetry (sys : System S T) : Type u where
  ft : T ≃ T
  fs : S ≃ S

namespace Symmetry

def ft' (sym : sys.Symmetry) : T ≃ T := sym.ft.symm
def fs' (sym : sys.Symmetry) : S ≃ S := sym.fs.symm

class WF (sym : sys.Symmetry) : Prop where
  initial_fs_iff : ∀ {s}, sys.Initial (sym.fs s) ↔ sys.Initial s
  tr_eq : ∀ {s t}, sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs'

def one : sys.Symmetry where
  ft := Equiv.refl T
  fs := Equiv.refl S

instance : One sys.Symmetry := ⟨one⟩
theorem one_def : (1 : sys.Symmetry) = one := rfl

instance : Inhabited sys.Symmetry := ⟨1⟩
theorem default_def : (default : sys.Symmetry) = 1 := rfl

@[simp]
def simFn (sym : sys.Symmetry) (f : S → T) (s : S) : T :=
  sym.ft # f # sym.fs' s

@[simp]
def simFn' (sym : sys.Symmetry) (f : S → T) (s : S) : T :=
  sym.ft' # f # sym.fs s

def inv (sym : sys.Symmetry) : sys.Symmetry where
  ft := sym.ft'
  fs := sym.fs'

instance : Inv sys.Symmetry := ⟨inv⟩
theorem inv_def {sym : sys.Symmetry} : sym⁻¹ = sym.inv := rfl

def mul (sym₁ sym₂ : sys.Symmetry) : sys.Symmetry where
  ft := sym₁.ft.comp sym₂.ft
  fs := sym₁.fs.comp sym₂.fs

instance : Mul sys.Symmetry := ⟨mul⟩
theorem mul_def {sym₁ sym₂ : sys.Symmetry} : sym₁ * sym₂ = sym₁.mul sym₂ := rfl

def div (sym₁ sym₂ : sys.Symmetry) : sys.Symmetry :=
  sym₁ * sym₂⁻¹

instance : Div sys.Symmetry := ⟨div⟩
theorem div_def {sym₁ sym₂ : sys.Symmetry} : sym₁ / sym₂ = sym₁ * sym₂⁻¹ := rfl

def npow (n : ℕ) (sym : sys.Symmetry) : sys.Symmetry :=
  (· * sym)^[n] 1

def zpow (z : ℤ) (sym : sys.Symmetry) : sys.Symmetry :=
  match z with
  | .ofNat n => sym.npow n
  | .negSucc n => sym⁻¹.npow (n + 1)

class SelfInverse (sym : sys.Symmetry) extends sym.WF where
  inv_eq_self : sym⁻¹ = sym