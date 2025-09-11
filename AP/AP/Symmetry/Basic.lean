import AP.AP.Symmetry.Defs

namespace AP

@[simp] theorem mkSymFs_symm {ft} : (mkSymFs ft).symm = mkSymFs ft.symm := rfl

@[simp] theorem ft_mkSym {ft} : (mkSym ft).ft = ft := rfl
@[simp] theorem ft'_mkSym {ft} : (mkSym ft).ft' = ft.symm := rfl
@[simp] theorem fs_mkSym {ft} : (mkSym ft).fs = mkSymFs ft := rfl
@[simp] theorem fs'_mkSym {ft} : (mkSym ft).fs' = mkSymFs ft.symm := rfl

@[simp] theorem mkSymFs_apply {ft s} : mkSymFs ft s = mkSymFsAux ft s := rfl

@[simp] theorem pw_mkSymFsAux {ft s} : (mkSymFsAux ft s).pw = s.pw := rfl
@[simp] theorem taken_mkSymFsAux {ft s} : (mkSymFsAux ft s).taken = s.taken.map ft := rfl
@[simp] theorem aPos_mkSymFsAux {ft s} : (mkSymFsAux ft s).aPos = ft s.aPos := rfl
@[simp] theorem aTurn_mkSymFsAux {ft s} : (mkSymFsAux ft s).aTurn = s.aTurn := rfl
@[simp] theorem hist_mkSymFsAux {ft s} : (mkSymFsAux ft s).hist = s.hist.map ft := rfl

@[simp]
theorem aPos₀_mkSymFsAux {ft s} [hs : sys.WF s] : (mkSymFsAux ft s).aPos₀ = ft s.aPos₀ := by
  obtain ⟨ps, h⟩ := s.exi_hist_eq_snoc; simp [State.aPos₀]; simp [h]

theorem aPos₀_mkSymFsAux_eq_ite {ft s} : (mkSymFsAux ft s).aPos₀ =
if s.hist = [] then s.aPos₀ else ft s.aPos₀ := by
  simp [State.aPos₀]; cases h : s.hist.getLast? <;> simp
  simp at h; simp [h]; intro h₁; simp [h₁] at h

@[simp]
theorem aTurn_sym_fs {s} {sym : sys.Symmetry} (H : sym.WF) :
(sym.fs s).aTurn = s.aTurn := by
  sorry

-- #check 0 #exit

@[simp]
theorem aTurn_sym_fs' {s} {sym : sys.Symmetry} (H : sym.WF) :
(sym.fs' s).aTurn = s.aTurn := by rw [←aTurn_sym_fs H]; simp

def AStrat.sym (a : AStrat) (sym : sys.Symmetry) : AStrat where
  f := sym.simFn a.f

def DStrat.sym (d : DStrat) (sym : sys.Symmetry) : DStrat where
  f := sym.simFn d.f

def Strat.sym (st : Strat) (sym : sys.Symmetry) : Strat where
  a := st.a.sym sym
  d := st.d.sym sym

theorem Strat.f_sym_eq {st : Strat} {sym : sys.Symmetry} [H : sym.WF] :
(st.sym sym).f = sym.simFn st.f := by
  ext s :1; simp [Strat.f]; split_ifs with h₁ <;> rfl

@[simp]
instance AState.sym_fs {s} {sym : sys.Symmetry} [hs : AState s] [H : sym.WF] :
AState (sym.fs s) := by constructor <;> simp

@[simp]
instance AState.sym_fs' {s} {sym : sys.Symmetry} [hs : AState s] [H : sym.WF] :
AState (sym.fs' s) := by constructor <;> simp

@[simp]
instance DState.sym_fs {s} {sym : sys.Symmetry} [hs : DState s] [H : sym.WF] :
DState (sym.fs s) := by constructor <;> simp

@[simp]
instance DState.sym_fs' {s} {sym : sys.Symmetry} [hs : DState s] [H : sym.WF] :
DState (sym.fs' s) := by constructor <;> simp

@[simp]
instance {a : AStrat} {sym : sys.Symmetry} [ha : a.WF] [H : sym.WF] : (a.sym sym).WF := by
  rw [AStrat.wf_iff]
  intro s hs h
  rw [sym.hasTr_iff'] at h
  replace h := ha.validTr h
  simp [AStrat.sym]
  rw [sym.validTr_iff']
  simpa

@[simp]
instance {d : DStrat} {sym : sys.Symmetry} [hd : d.WF] [H : sym.WF] : (d.sym sym).WF := by
  rw [DStrat.wf_iff]
  intro s hs h
  rw [sym.hasTr_iff'] at h
  simp [DStrat.sym]
  rw [sym.validTr_iff']
  simp

@[simp]
instance {st : Strat} {sym : sys.Symmetry} [hst : st.WF] [H : sym.WF] : (st.sym sym).WF := by
  rw [Strat.wf_def]; intro s hs h; rw [st.f_sym_eq]; exact sys.validTr_of_simFn_and_hasTr h

theorem State.aHws_sym_of {s} {sym : sys.Symmetry}
[H : sym.WF] (h : s.aHws) : (sym.fs s).aHws := by
  obtain ⟨a, Ha, h⟩ := h
  use a.sym sym, inferInstance
  intro d Hd
  specialize h (d.sym sym⁻¹) inferInstance
  have h₁ : (Strat.mk (a.sym sym) d) = (Strat.mk a (d.sym sym⁻¹)).sym sym
  · simp [Strat.sym, AStrat.sym, DStrat.sym]
  rw [h₁]; clear h₁
  intro n
  specialize h n
  convert h using 1; clear h
  simp [Strat.f_sym_eq]

theorem State.aHws_iff_sym {s} {sym : sys.Symmetry}
[H : sym.WF] : s.aHws ↔ (sym.fs s).aHws := by
  use aHws_sym_of; intro h; have h₁ := aHws_sym_of (sym := sym⁻¹) h; simp at h₁; exact h₁

theorem State.dHws_iff_sym {s} {sym : sys.Symmetry} {hs : sys.WF s}
[H : sym.WF] : s.dHws ↔ (sym.fs s).dHws := by
  rw [←not_iff_not]; simp [←aHws_iff_sym]

@[simp]
theorem mkSymFsAux_initState {ft pw p} :
mkSymFsAux ft (initState pw p) = initState pw (ft p) := by
  ext:1 <;> simp

-- #check 0 #exit

-----

def translate (dif : PointZ) : sys.Symmetry := mkSym
  { toFun := (· + dif)
  , invFun := (· - dif)
  , left_inv := λ _ => by simp
  , right_inv := λ _ => by simp
  }

theorem translate.cnd_initial_fs_iff {dif s} :
sys.Initial ((translate dif).fs s) ↔ sys.Initial s := by
  simp [translate, aPos₀_mkSymFsAux_eq_ite]
  split_ifs with h
  · simp [State.aPos₀, h]
    have h₁ : initState s.pw none.iget ≠ s
    · intro h₁
      rw [←h₁] at h
      simp at h
    simp [h₁]
    apply ne_of_congr (·.hist.length)
    simp [h]
  simp [State.ext_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [h₁, h₂, h₃]
    symm at h₄; simp at h₄
    simp [h₂, h₄]
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    simp [h₁, h₂, h₃]
    symm; simp
    rw [←h₂, h₄]

theorem translate.cnd_tr_eq {dif s p} : sys.tr s p =
(sys.tr ((translate dif).fs s) ((translate dif).ft p)).map (translate dif).fs' := by
  ext s'
  simp [translate, sys, State.move]
  split_ifs with ht
  · simp [State.aMove]; simp [State.ext_iff]
  · simp [State.dMove]; simp [State.ext_iff]

@[simp]
instance {dif} : (translate dif).WF where
  initial_fs_iff := translate.cnd_initial_fs_iff
  tr_eq := translate.cnd_tr_eq