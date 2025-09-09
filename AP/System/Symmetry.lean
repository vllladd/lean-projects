import AP.System.Invariant

namespace System

universe u
variable {S T : Type u} {sys : System S T}

@[ext]
structure Symmetry (sys : System S T) : Type u where
  fs : S → S
  fs' : S → S
  ft : T → T
  ft' : T → T

namespace Symmetry

variable {sym : sys.Symmetry}

class WF (sym : sys.Symmetry) : Prop where
  h_fs : Function.BijectiveOn sys.WF sys.WF sym.fs sym.fs'
  h_ft : Function.BijectiveOn sys.WFTrans sys.WFTrans sym.ft sym.ft'
  tr_eq : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs s) (sym.ft t)).map sym.fs'
  tr_eq' : ∀ {s t} [sys.WF s], sys.tr s t = (sys.tr (sym.fs' s) (sym.ft' t)).map sym.fs

instance : Inhabited (Symmetry sys) := ⟨id, id, id, id⟩

theorem default_eq : (default : Symmetry sys) = ⟨id, id, id, id⟩ := rfl

@[simp]
instance : (default : Symmetry sys).WF := by
  rw [default_eq]; constructor <;> simp

instance {s} [H : sym.WF] [hs : sys.WF s] : sys.WF (sym.fs s) :=
  H.h_fs.cnd_right hs

instance {s} [H : sym.WF] [hs : sys.WF s] : sys.WF (sym.fs' s) :=
  H.h_fs.cnd_left hs

instance {t} [H : sym.WF] [ht : sys.WFTrans t] : sys.WFTrans (sym.ft t) :=
  H.h_ft.cnd_right ht

instance {t} [H : sym.WF] [ht : sys.WFTrans t] : sys.WFTrans (sym.ft' t) :=
  H.h_ft.cnd_left ht

@[simp]
theorem fs'_fs {s} [H : sym.WF] [hs : sys.WF s] : sym.fs' (sym.fs s) = s :=
  H.h_fs.cancel_left hs

@[simp]
theorem fs_fs' {s} [H : sym.WF] [hs : sys.WF s] : sym.fs (sym.fs' s) = s :=
  H.h_fs.cancel_right hs

@[simp]
theorem ft'_ft {t} [H : sym.WF] [ht : sys.WFTrans t] : sym.ft' (sym.ft t) = t :=
  H.h_ft.cancel_left ht

@[simp]
theorem ft_ft' {t} [H : sym.WF] [ht : sys.WFTrans t] : sym.ft (sym.ft' t) = t :=
  H.h_ft.cancel_right ht

def tr_fs {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr (sym.fs s) t = (sys.tr s (sym.ft' t)).map sym.fs := by
  nth_rw 1 [H.tr_eq']; ext s'; simp

def tr_fs' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr (sym.fs' s) t = (sys.tr s (sym.ft t)).map sym.fs' := by
  nth_rw 1 [H.tr_eq]; ext s'; simp

def tr_ft {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr s (sym.ft t) = (sys.tr (sym.fs' s) t).map sym.fs := by
  nth_rw 2 [H.tr_eq]; ext s'; simp; constructor
  · intro h; use s'; have hs' := wf_of_tr h; simpa
  · rintro ⟨s₁, h₁, h₂⟩; have hs₁ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

def tr_ft' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.tr s (sym.ft' t) = (sys.tr (sym.fs s) t).map sym.fs' := by
  nth_rw 2 [H.tr_eq']; ext s'; simp; constructor
  · intro h; use s', h; have h₁ := wf_of_tr h; simp
  · rintro ⟨s₁, h₁, h₂⟩; have h₃ := wf_of_tr h₁; simp at h₂; simpa [←h₂]

theorem validTr_fs_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs'_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := by
  obtain ⟨s', h⟩ := h; simp [tr_ft] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs'] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_ft'_of {s t} [H : sym.WF] [hs : sys.WF s]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := by
  obtain ⟨s', h⟩ := h; simp [tr_fs] at h; obtain ⟨s', h, rfl⟩ := h; use s'

theorem validTr_fs {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) :=
  ⟨validTr_ft'_of, validTr_fs_of⟩

theorem validTr_fs' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) :=
  ⟨validTr_ft_of, validTr_fs'_of⟩

theorem validTr_ft {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t :=
  ⟨validTr_fs'_of, validTr_ft_of⟩

theorem validTr_ft' {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp]
theorem hasTr_fs {s} [H : sym.WF] [hs : sys.WF s] :
sys.hasTr (sym.fs s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft' t; simpa [validTr_ft']
  · use sym.ft t; simpa [validTr_ft]

@[simp]
theorem hasTr_fs' {s} [H : sym.WF] [hs : sys.WF s] :
sys.hasTr (sym.fs' s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩
  · use sym.ft t; simpa [validTr_ft]
  · use sym.ft' t; simpa [validTr_ft']

example {s t} [H : sym.WF] [hs : sys.WF s] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) := by
  symm; constructor
  · exact fun a ↦ validTr_fs_of a
  · exact fun a ↦ validTr_ft'_of a

@[simp]
def simFn (sym : Symmetry sys) (f : S → T) (s : S) : T :=
  sym.ft # f # sym.fs' s

instance {f} [H : sym.WF] [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  rw [sys.simFn_def]; intro s hs h; simp; apply hf.1 at h; apply validTr_ft_of
  have h₁ : sys.hasTr (sym.fs' s); simp; exact ⟨_, h⟩; exact hf.1 h₁

def inv (sym : Symmetry sys) : Symmetry sys where
  fs := sym.fs'
  fs' := sym.fs
  ft' := sym.ft
  ft := sym.ft'

@[simp]
theorem inv_inv : sym.inv.inv = sym := by ext <;> rfl

instance [H : sym.WF] : sym.inv.WF where
  h_fs := H.h_fs.symm
  h_ft := H.h_ft.symm
  tr_eq := WF.tr_eq'
  tr_eq' := WF.tr_eq

@[simp]
theorem wf_inv_iff : sym.inv.WF ↔ sym.WF := by
  symm; constructor <;> intro h; infer_instance
  rw [←sym.inv_inv]; infer_instance