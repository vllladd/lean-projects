import AP.AP.Determinacy

namespace AP

@[simp]
theorem State.aMove_setHist {s : State} {hist p} :
(s.setHist hist).aMove p = (s.aMove p).map (·.setHist hist) := by
  simp [State.aMove]; rfl

@[simp]
theorem State.dMove_setHist {s : State} {hist p} :
(s.setHist hist).dMove p = (s.dMove p).map (·.setHist hist) := by
  simp [State.dMove]; rfl

@[simp]
theorem State.move_setHist {s : State} {hist p} :
(s.setHist hist).move p = (s.move p).map (·.setHist # p :: hist) := by
  simp [State.move, Option.bind_map]
  split_ifs with ht <;> simp [State.setHist]

@[simp]
theorem State.tr_setHist {s : State} {hist p} :
sys.tr (s.setHist hist) p = (sys.tr s p).map (·.setHist # p :: hist) := by
  simp [sys]

@[simp]
theorem State.validTr_setHist {s : State} {hist} :
sys.validTr (s.setHist hist) = sys.validTr s := by
  ext p; constructor <;> rintro ⟨s₁, h₁⟩
  · simp at h₁; obtain ⟨s', h₁, h₂⟩ := h₁; use s'
  · use s₁.setHist (p :: hist); simp; use s₁

@[simp]
theorem State.hasTr_setHist {s : State} {hist} :
sys.hasTr (s.setHist hist) ↔ sys.hasTr s := by
  apply exists_iff_of; simp

def AStrat.histBlind (a : AStrat) : Prop :=
  ∀ s hist, AState s → sys.WF (s.setHist hist) →
  sys.hasTr s → a.f (s.setHist hist) = a.f s

def DStrat.histBlind (d : DStrat) : Prop :=
  ∀ s hist, DState s → sys.WF (s.setHist hist) →
  sys.hasTr s → d.f (s.setHist hist) = d.f s

@[simp]
theorem State.chooseAMove_setHist {s : State} {hist} :
(s.setHist hist).chooseAMove = s.chooseAMove := by
  simp [chooseAMove]

-- #check 0 #exit

set_option linter.dupNamespace false in
open Classical in private noncomputable
def aAux₁ : AStrat := .mk' # λ s => do
  let a ← choose? # λ (a : AStrat) => a.WF ∧
    ∃ s', sys.WF s' ∧ s.setHist s'.hist = s' ∧
    ∀ (d : DStrat), d.WF → s'.a_wins ⟨a, d⟩
  return a.f s

set_option linter.dupNamespace false in
@[simp] private theorem histBlind_aAux₁_aux {f : State → AStrat} {s : State} {hist}
(hf : f = λ (s : State) => Classical.epsilon # λ a => a.WF ∧ ∃ s', sys.WF s' ∧
s.setHist s'.hist = s' ∧ ∀ (d : DStrat), d.WF → s'.a_wins ⟨a, d⟩) :
f (s.setHist hist) = f s := by subst hf; ext:2; nm s₁; simp

-- #check 0 #exit

set_option linter.dupNamespace false in
@[simp] private theorem histBlind_aAux₁ : aAux₁.histBlind := by
  simp [AStrat.histBlind]
  intro s hist hs hs' h₁
  unfold aAux₁
  simp [AStrat.mk', Option.pure_def, Option.bind_eq_bind, AStrat.f_mk,
    mk_strat_fn, State.setHist_setHist, choose?_eq_ite]
  split_ifs with h₂; rotate_left; simp
  generalize ha : Classical.epsilon (λ (a : AStrat) => a.WF ∧
    ∃ s', sys.WF s' ∧ s.setHist s'.hist = s' ∧ ∀ (d : DStrat),
    d.WF → s'.a_wins ⟨a, d⟩) = a
  replace h₃ := Classical.epsilon_spec h₂
  rw [ha] at h₃; simp
  rcases h₃ with ⟨h₃, s₁, hs₁, h₄, h₅⟩
  replace hs₁ : AState s₁; use hs₁; rw [←h₄]; simp
  have hb : sys.validTr s # a.f # s.setHist hist
  · suffices h : sys.validTr (s.setHist hist) (a.f (s.setHist hist))
    simp at h; exact h
    apply a.validTr; rwa [State.hasTr_setHist]
  have hc := a.validTr h₁
  simp [hb, hc]
  generalize hf : (λ (s : State) => Classical.epsilon λ a =>
    a.WF ∧ ∃ s', sys.WF s' ∧ s.setHist s'.hist = s' ∧ ∀ (d : DStrat),
    d.WF → s'.a_wins ⟨a, d⟩) = f
  replace ha : f s = a; rw [←hf, ←ha]
  have h₆ : ∀ (s : State) hist, f (s.setHist hist) = f s
  · intros; exact histBlind_aAux₁_aux hf.symm
  sorry

#check 0 #exit

-- theorem State.a_hws_histBlind_of_a_hws {s} [hs : sys.WF s] (h : s.a_hws) :
-- ∃ (a : AStrat), a.WF ∧ a.histBlind ∧ ∀ (d : DStrat), d.WF → s.a_wins ⟨a, d⟩ := by