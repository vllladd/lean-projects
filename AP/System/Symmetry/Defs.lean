import AP.System.Symmetry.Raw

namespace System

universe u
variable {S T : Type u} {sys : System S T}

structure Symmetry (sys : System S T) : Type u extends Symmetry.Raw sys where
  wf : toRaw.WF

namespace Symmetry

variable {sym sym₁ sym₂ sym₃ : sys.Symmetry}

@[ext]
theorem ext (h : sym₁.toRaw = sym₂.toRaw) : sym₁ = sym₂ := by
  cases sym₁; cases sym₂; simp_all

def one : sys.Symmetry :=
  ⟨Raw.one, inferInstance⟩

instance : One sys.Symmetry := ⟨one⟩
theorem one_def : (1 : sys.Symmetry) = 1 := rfl

instance : Inhabited sys.Symmetry := ⟨1⟩
theorem default_eq : (default : sys.Symmetry) = 1 := rfl

instance : sym.toRaw.WF := sym.wf

theorem tr_fs {s t} : sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := Raw.tr_fs
theorem tr_fs' {s t} : sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := Raw.tr_fs'
theorem tr_ft {s t} : sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := Raw.tr_ft
theorem tr_ft' {s t} : sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := Raw.tr_ft'

theorem validTr_fs_of {s t} (h : sys.validTr s (sym.ft' t)) :
sys.validTr (sym.fs s) t := Raw.validTr_fs_of h

theorem validTr_fs'_of {s t} (h : sys.validTr s (sym.ft t)) :
sys.validTr (sym.fs' s) t := Raw.validTr_fs'_of h

theorem validTr_ft_of {s t} (h : sys.validTr (sym.fs' s) t) :
sys.validTr s (sym.ft t) := Raw.validTr_ft_of h

theorem validTr_ft'_of {s t} (h : sys.validTr (sym.fs s) t) :
sys.validTr s (sym.ft' t) := Raw.validTr_ft'_of h

theorem validTr_fs {s t} : sys.validTr (sym.fs s) t ↔
sys.validTr s (sym.ft' t) := Raw.validTr_fs

theorem validTr_fs' {s t} : sys.validTr (sym.fs' s) t ↔
sys.validTr s (sym.ft t) := Raw.validTr_fs'

theorem validTr_ft {s t} : sys.validTr s (sym.ft t) ↔
sys.validTr (sym.fs' s) t := Raw.validTr_ft

theorem validTr_ft' {s t} : sys.validTr s (sym.ft' t) ↔
sys.validTr (sym.fs s) t := Raw.validTr_ft'

def simFn (sym : sys.Symmetry) (f : S → T) (s : S) : T :=
  sym.toRaw.simFn f s

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  unfold simFn; infer_instance

def inv (sym : sys.Symmetry) : sys.Symmetry :=
  ⟨sym.toRaw.inv, inferInstance⟩

instance : Inv sys.Symmetry := ⟨inv⟩
theorem inv_def : sym⁻¹ = sym.inv := rfl

@[simp]
theorem inv_inv : sym⁻¹⁻¹ = sym := ext Raw.inv_inv

def mul (sym₁ sym₂ : sys.Symmetry) : sys.Symmetry :=
  ⟨sym₁.toRaw.mul sym₂.toRaw, inferInstance⟩

instance : Mul sys.Symmetry := ⟨mul⟩
theorem mul_def : sym₁ * sym₂ = sym₁.mul sym₂ := rfl

def div (sym₁ sym₂ : sys.Symmetry) : sys.Symmetry :=
  ⟨sym₁.toRaw.div sym₂.toRaw, inferInstance⟩

instance : Div sys.Symmetry := ⟨div⟩
theorem div_def : sym₁ / sym₂ = sym₁.div sym₂ := rfl

def npow (n : ℕ) (sym : sys.Symmetry) : sys.Symmetry :=
  ⟨sym.toRaw.npow n, inferInstance⟩

def zpow (z : ℤ) (sym : sys.Symmetry) : sys.Symmetry :=
  ⟨sym.toRaw.zpow z, inferInstance⟩