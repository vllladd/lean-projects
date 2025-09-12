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
theorem aTurn_sym_fs {s} {sym : sys.Symmetry} [hs : sys.WF s] (H : sym.WF) :
(sym.fs s).aTurn = s.aTurn := by
  rw [State.wf_iff] at hs
  obtain ⟨ps, h⟩ := hs
  generalize h₀ : initState s.pw s.aPos₀ = s₀ at h
  replace h₀ : (sym.fs s₀).aTurn = s₀.aTurn
  · simp [←h₀]
  induction ps generalizing s₀
  · simp at h; rwa [←h]
  nm p ps ih
  simp at h
  split at h; simp at h
  nm x s' h₁; clear x
  have h₂ := h₁
  rw [sym.tr_eq] at h₁
  simp at h₁
  obtain ⟨s₁, h₁, rfl⟩ := h₁
  apply ih _ h; clear ih
  simp
  rw [State.aTurn_eq_of_tr h₁, State.aTurn_eq_of_tr h₂, h₀]

@[simp]
theorem aTurn_sym_fs' {s} {sym : sys.Symmetry} [hs : sys.WF s] (H : sym.WF) :
(sym.fs' s).aTurn = s.aTurn := by rw [←aTurn_sym_fs H]; simp

def AStrat.sym (a : AStrat) (sym : sys.Symmetry) : AStrat where
  f := sym.simFn a.f

def DStrat.sym (d : DStrat) (sym : sys.Symmetry) : DStrat where
  f := sym.simFn d.f

def Strat.sym (st : Strat) (sym : sys.Symmetry) : Strat where
  a := st.a.sym sym
  d := st.d.sym sym

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
  intro s hs
  simp [DStrat.sym]
  rw [sym.validTr_iff']
  simp

@[simp]
instance {st : Strat} {sym : sys.Symmetry} [hst : st.WF] [H : sym.WF] :
sys.SimFn (st.sym sym).f := by simp [Strat.sym]

theorem Strat.f_sym_eq {st : Strat} {s} {sym : sys.Symmetry}
[hs : sys.WF s] [H : sym.WF] : (st.sym sym).f s = sym.simFn st.f s := by
  simp [Strat.f]; split_ifs with h₁ <;> rfl

theorem Strat.simulate_sym_eq {st : Strat} {s n} {sym : sys.Symmetry}
[hst : st.WF] [hs : sys.WF s] [H : sym.WF] : sys.simulate (st.sym sym).f s n =
sys.simulate (sym.simFn st.f) s n := by
  apply sys.simulate_congr
  intro k hk b h₁ h₂ h
  have hb := sys.wf_of_simulate_eq h₁
  rw [f_sym_eq]

@[simp]
instance {st : Strat} {sym : sys.Symmetry} [hst : st.WF] [H : sym.WF] : (st.sym sym).WF := by
  rw [Strat.wf_def]; intro s hs h; rw [st.f_sym_eq]; exact sys.validTr_of_simFn_and_hasTr h

theorem State.aHws_sym_of {s} {sym : sys.Symmetry} [hs : sys.WF s]
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
  simp [Strat.simulate_sym_eq]

theorem State.aHws_iff_sym {s} {sym : sys.Symmetry} [hs : sys.WF s]
[H : sym.WF] : s.aHws ↔ (sym.fs s).aHws := by
  use aHws_sym_of; intro h; have h₁ := aHws_sym_of (sym := sym⁻¹) h; simp at h₁; exact h₁

theorem State.dHws_iff_sym {s} {sym : sys.Symmetry} {hs : sys.WF s}
[H : sym.WF] : s.dHws ↔ (sym.fs s).dHws := by
  rw [←not_iff_not]; simp [←aHws_iff_sym]

@[simp]
theorem mkSymFsAux_initState {ft pw p} :
mkSymFsAux ft (initState pw p) = initState pw (ft p) := by
  ext:1 <;> simp