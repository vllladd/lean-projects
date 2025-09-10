import AP.System.Symmetry.Raw

namespace System

universe u
variable {S T : Type u} {sys : System S T}

def Symmetry (sys : System S T) : Type u :=
  Quotient # Symmetry.Raw.setoid (sys := sys)

namespace Symmetry

variable {sym sym₁ sym₂ sym₃ : Symmetry sys}

def one : Symmetry sys :=
  Quotient.mk' Raw.one

instance : One (Symmetry sys) := ⟨one⟩
theorem one_def : (1 : Symmetry sys) = one := rfl

instance : Inhabited (Symmetry sys) := ⟨1⟩
theorem default_eq : (default : Symmetry sys) = 1 := rfl

def fs (sym : Symmetry sys) (s : S) [hs : sys.WF s] : S :=
  sym.lift (·.fs s) # λ _ _ h => by exact h.hs

def fs' (sym : Symmetry sys) (s : S) [hs : sys.WF s] : S :=
  sym.lift (·.fs' s) # λ _ _ h => by exact h.hs'

def ft (sym : Symmetry sys) (t : T) [ht : sys.WFTrans t] : T :=
  sym.lift (·.ft t) # λ _ _ h => by exact h.ht

def ft' (sym : Symmetry sys) (t : T) [ht : sys.WFTrans t] : T :=
  sym.lift (·.ft' t) # λ _ _ h => by exact h.ht'

instance {s} [hs : sys.WF s] : sys.WF (sym.fs s) := by
  apply sym.ind; simp [fs]; infer_instance

instance {s} [hs : sys.WF s] : sys.WF (sym.fs' s) := by
  apply sym.ind; simp [fs']; infer_instance

instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft t) := by
  apply sym.ind; simp [ft]; infer_instance

instance {t} [ht : sys.WFTrans t] : sys.WFTrans (sym.ft' t) := by
  apply sym.ind; simp [ft']; infer_instance

@[simp]
theorem fs'_fs {s} [hs : sys.WF s] : sym.fs' (sym.fs s) = s := by
  apply sym.ind; simp [fs, fs']

@[simp]
theorem fs_fs' {s} [hs : sys.WF s] : sym.fs (sym.fs' s) = s := by
  apply sym.ind; simp [fs, fs']

@[simp]
theorem ft'_ft {t} [ht : sys.WFTrans t] : sym.ft' (sym.ft t) = t := by
  apply sym.ind; simp [ft, ft']

@[simp]
theorem ft_ft' {t} [ht : sys.WFTrans t] : sym.ft (sym.ft' t) = t := by
  apply sym.ind; simp [ft, ft']

theorem tr_fs {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.tr (sym.fs s) t = match h : sys.tr s (sym.ft' t) with
| none => none | some s' => haveI := wf_of_tr h; sym.fs s' := by
  apply sym.ind; simp [fs, ft']; intro sym; rw [sym.tr_fs]; split <;> simp_all

theorem tr_fs' {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.tr (sym.fs' s) t = match h : sys.tr s (sym.ft t) with
| none => none | some s' => haveI := wf_of_tr h; sym.fs' s' := by
  apply sym.ind; simp [fs', ft]; intro sym; rw [sym.tr_fs']; split <;> simp_all

theorem tr_ft {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.tr s (sym.ft t) = match h : sys.tr (sym.fs' s) t with
| none => none | some s' => haveI := wf_of_tr h; sym.fs s' := by
  apply sym.ind; simp [fs, fs', ft]; intro sym; rw [sym.tr_ft]; split <;> simp_all

theorem tr_ft' {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.tr s (sym.ft' t) = match h : sys.tr (sym.fs s) t with
| none => none | some s' => haveI := wf_of_tr h; sym.fs' s' := by
  apply sym.ind; simp [fs, fs', ft']; intro sym; rw [sym.tr_ft']; split <;> simp_all

theorem validTr_fs_of {s t} [hs : sys.WF s] [ht : sys.WFTrans t]
(h : sys.validTr s (sym.ft' t)) : sys.validTr (sym.fs s) t := by
  obtain ⟨s', h⟩ := h; have h₁ := wf_of_tr h; use sym.fs s'
  rw [tr_ft'] at h; split at h <;> simp_all; simp [←h]

theorem validTr_fs'_of {s t} [hs : sys.WF s] [ht : sys.WFTrans t]
(h : sys.validTr s (sym.ft t)) : sys.validTr (sym.fs' s) t := by
  obtain ⟨s', h⟩ := h; have h₁ := wf_of_tr h; use sym.fs' s'
  rw [tr_ft] at h; split at h <;> simp_all; simp [←h]

theorem validTr_ft_of {s t} [hs : sys.WF s] [ht : sys.WFTrans t]
(h : sys.validTr (sym.fs' s) t) : sys.validTr s (sym.ft t) := by
  obtain ⟨s', h⟩ := h; have h₁ := wf_of_tr h; use sym.fs s'
  rw [tr_fs'] at h; split at h <;> simp_all; simp [←h]

theorem validTr_ft'_of {s t} [hs : sys.WF s] [ht : sys.WFTrans t]
(h : sys.validTr (sym.fs s) t) : sys.validTr s (sym.ft' t) := by
  obtain ⟨s', h⟩ := h; have h₁ := wf_of_tr h; use sym.fs' s'
  rw [tr_fs] at h; split at h <;> simp_all; simp [←h]

theorem validTr_fs {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.validTr (sym.fs s) t ↔ sys.validTr s (sym.ft' t) :=
  ⟨validTr_ft'_of, validTr_fs_of⟩

theorem validTr_fs' {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.validTr (sym.fs' s) t ↔ sys.validTr s (sym.ft t) :=
  ⟨validTr_ft_of, validTr_fs'_of⟩

theorem validTr_ft {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.validTr s (sym.ft t) ↔ sys.validTr (sym.fs' s) t :=
  ⟨validTr_fs'_of, validTr_ft_of⟩

theorem validTr_ft' {s t} [hs : sys.WF s] [ht : sys.WFTrans t] :
sys.validTr s (sym.ft' t) ↔ sys.validTr (sym.fs s) t :=
  ⟨validTr_fs_of, validTr_ft'_of⟩

@[simp]
theorem hasTr_fs {s} [hs : sys.WF s] : sys.hasTr (sym.fs s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩ <;> have ht := wfTrans_of_validTr h
  · use sym.ft' t; simpa [validTr_ft']
  · use sym.ft t; simpa [validTr_ft]

@[simp]
theorem hasTr_fs' {s} [hs : sys.WF s] :
sys.hasTr (sym.fs' s) ↔ sys.hasTr s := by
  constructor <;> rintro ⟨t, h⟩ <;> have ht := wfTrans_of_validTr h
  · use sym.ft t; simpa [validTr_ft]
  · use sym.ft' t; simpa [validTr_ft']

#check 0 #exit

@[simp]
def simFn (sym : Symmetry sys) (f : S → T) (s : S) : T :=
  sym.simFn f s

instance {f} [hf : sys.SimFn f] : sys.SimFn (sym.simFn f) := by
  unfold simFn; infer_instance

def inv (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.inv, inferInstance⟩

@[simp]
theorem inv_inv : sym.inv.inv = sym := ext Raw₀.inv_inv

def mul (sym₁ sym₂ : Raw sys) : Raw sys :=
  ⟨sym₁.toRaw₀.mul sym₂.toRaw₀, inferInstance⟩

def npow (n : ℕ) (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.npow n, inferInstance⟩

def zpow (z : ℤ) (sym : Raw sys) : Raw sys :=
  ⟨sym.toRaw₀.zpow z, inferInstance⟩