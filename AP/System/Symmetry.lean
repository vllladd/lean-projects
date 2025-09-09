import AP.System.Invariant

namespace System

universe u
variable {S T : Type u} {sys : System S T}

structure Symmetry (sys : System S T) : Type u where
  fs : S → S
  ft : T → T

namespace Symmetry

variable {sym : sys.Symmetry}

class WF (sym : sys.Symmetry) : Prop where
  tr_eq : ∀ {s t} [sys.WF s], sys.tr (sym.fs s) (sym.ft t) = (sys.tr s t).map sym.fs

theorem wf_def : sym.WF ↔ ∀ {s t} [sys.WF s],
sys.tr (sym.fs s) (sym.ft t) = (sys.tr s t).map sym.fs := ⟨(·.1), (⟨·⟩)⟩

def tr_eq {s t} [hs : sys.WF s] [h : sym.WF] :
sys.tr (sym.fs s) (sym.ft t) = (sys.tr s t).map sym.fs := h.tr_eq

instance : Inhabited (Symmetry sys) := ⟨id, id⟩

theorem default_eq : (default : Symmetry sys) = ⟨id, id⟩ := rfl

@[simp] instance : (default : Symmetry sys).WF := by simp [wf_def, default_eq]