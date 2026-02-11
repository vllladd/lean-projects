import AP.AP.Defense.Defs

namespace AP.Defense

variable {dse dse₁ dse₂ : Defense}

theorem empty_def : (∅ : Defense) = empty := rfl
theorem default_def : (default : Defense) = ∅ := rfl

@[simp] theorem cnd_empty : cnd ∅ = λ _ => True := rfl
@[simp] theorem ps_empty : ps ∅ = ∅ := rfl
@[simp] theorem f_empty : f ∅ = λ _ => none := rfl

@[simp]
instance : WF ∅ where
  valid_tr := by simp [ValidTr]
  not_mem_ps := by simp

@[simp]
instance : WF default := by
  rw [default_def]; infer_instance

theorem valid_tr [H : dse.WF] {s} [DState s] {p} :
dse.f s = some p → sys.validTr s p := H.1

@[simp]
instance {d : DStrat} [H : dse.WF] [Hd : d.WF] : (dse.st d).WF := by
  unfold st; rw [DStrat.wf_iff]; intro s hs
  dsimp; cases h : dse.f s <;> simp; exact dse.valid_tr h

theorem st_comm {d}
(h : ∀ {s p₁ p₂}, dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
dse₁.st (dse₂.st d) = dse₂.st (dse₁.st d) := by
  ext s :2; simp [st]; cases h₁ : dse₁.f s <;>
  cases h₂ : dse₂.f s <;> simp; exact h h₁ h₂

theorem simulate_st_comm {s₀ n} {a : AStrat} {d : DStrat}
[hs₀ : sys.WF s₀] [Ha : a.WF] [Hd : d.WF] [H₁ : dse₁.WF] [H₂ : dse₂.WF]
(h : ∀ {s}, sys.Reachable s₀ s → ∀ {p₁ p₂},
dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
sys.simulate (Strat.f ⟨a, dse₁.st (dse₂.st d)⟩) s₀ n =
sys.simulate (Strat.f ⟨a, dse₂.st (dse₁.st d)⟩) s₀ n := by
  apply simulate_congr <;> simp
  intro k hk s hs h₁ h₂ h₃
  simp [st]
  cases H₃ : dse₁.f s <;> cases H₄ : dse₂.f s <;> simp
  nm s₁ s₂
  have H₅ := sys.reachable_of_simulate h₁
  exact h H₅ H₃ H₄

@[simp]
theorem sym_one : dse.sym 1 = dse := by
  ext <;> simp [sym]

@[simp]
theorem sym_sym {sym₁ sym₂ : sys.Symmetry} : (dse.sym sym₁).sym sym₂ = dse.sym (sym₂ * sym₁) := by
  ext <;> simp [sym]
  apply Iff.intro
  · intro a
    apply Exists.intro
    · apply And.intro
      · exact a
      · simp_all only [System.Symmetry.ft_ft']
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only [System.Symmetry.ft'_ft]

@[simp]
theorem ps_sym {sym : sys.Symmetry} : (dse.sym sym).ps = sym.ft '' dse.ps := rfl

theorem wf_sym_of_basicSym {sym} [H₁ : dse.WF] [H₂ : BasicSym sym] : dse.sym sym |>.WF := by
  have H₁' := H₁
  have wf := H₂.toWF
  obtain ⟨ft, rfl⟩ := H₂.exi_mkSym; clear H₂
  rcases H₁ with ⟨h₁, h₂⟩
  constructor
  · clear h₂
    unfold ValidTr at h₁ ⊢
    intro s hs p h₂
    generalize mkSym ft = sym at wf h₂
    have hs' : DState # sym.fs' s; simp
    specialize @h₁ (sym.fs' s) _ (sym.ft' p) _
    · simp [Defense.sym] at h₂ ⊢
      obtain ⟨p, h₂, rfl⟩ := h₂
      simpa
    rw [sym⁻¹.validTr_iff]
    simpa
  · clear h₁
    rintro s hs h₃ a Ha d Hd n
    simp
    
    generalize ha' : AStrat.mk (λ s => (mkSym ft).ft' # a.f # (mkSym ft).fs s) = a'
    generalize hd' : DStrat.mk (λ s => (mkSym ft).ft' # d.f # (mkSym ft).fs s) = d'
    
    have Ha' : a'.WF; subst ha'; infer_instance
    have Hd' : d'.WF; subst hd'; infer_instance
    
    specialize @h₂ ((mkSym ft).fs' s) _ _ a' _ d' _ n
    · simp [Defense.sym] at h₃; simpa
    
    generalize hsym : mkSym ft = sym at *
    
    rw [show ft.symm = sym.ft' by subst hsym; rfl]
    
    have h₄ : (dse.sym sym).st d |>.WF
    · rw [DStrat.wf_iff]
      intro sd hsd
      simp [Defense.sym, st]
      cases h₄ : dse.f # sym.fs' sd; simp
      nm p
      simp
      replace h₄ := H₁'.1 h₄
      rw [sym.validTr_iff']
      simpa
    
    have h := @sys.simulate_congr_rel (f := Strat.f ⟨a', dse.st d'⟩)
      (g := Strat.f ⟨a, dse.sym sym |>.st d⟩) (r := λ s' s => sym.fs s' = s)
      (a₁ := sym.fs' s) (a₂ := s) (n := n) _ _ _ _ _ _ (by simp)
    
    specialize h _
    · clear h h₂ h₃
      
      rintro k hk b₁ b₂ hb₁ hb₂ rfl
      simp
      intro c₁ c₂ hc₁ hc₂
      
      have Hb₁ : sys.WF b₁; grind
      have Hb₂ : sys.WF # sym.fs b₁; grind
      
      replace Hb₁ := b₁.aState_or_dState
      rcases Hb₁ with Hb₁ | Hb₁
      
      · replace Hb₂ : AState # sym.fs b₁
        · use Hb₂; simp
        
        simp at hc₁ hc₂
        replace hc₁ : sys.tr b₁ (sym.ft' # a.f # sym.fs b₁) = some c₁
        · clear! d hb₁
          subst ha'
          simp at hc₁
          
          have h₁ : sys.validTr b₁ # sym.ft' # a.f # sym.fs b₁
          · rw [sym.validTr_iff]
            simp
            use c₂
          
          simp [h₁] at hc₁
          exact hc₁
        
        rw [sym.tr_eq] at hc₁
        simp at hc₁
        obtain ⟨c₂', hc₁, rfl⟩ := hc₁
        simp [hc₁] at hc₂
        simpa
      
      · replace Hb₂ : DState # sym.fs b₁
        · use Hb₂; simp
        
        simp at hc₁ hc₂
        
        rw [sym.tr_eq'] at hc₂
        simp at hc₂
        obtain ⟨c₁', hc₂, rfl⟩ := hc₂
        
        simp [Defense.sym, st] at hc₁ hc₂
        simp_rw [←Option.getD_map] at hc₂
        simp at hc₂
        
        have H₁ : sys.validTr b₁ # sym.ft' # d.f # sym.fs b₁
        · rw [sym.validTr_iff]; simp
        
        simp [←hd', H₁, hc₂] at hc₁
        rw [hc₁]
    
    obtain ⟨s', rfl, h⟩ := h
    rw [h]; clear h
    subst hsym; simpa

instance {sym} [H₁ : dse.WF] [H₂ : BasicSym sym] : dse.sym sym |>.WF :=
  wf_sym_of_basicSym

@[simp]
theorem wf_sym_iff_of_basicSym {sym} [H₂ : BasicSym sym] : (dse.sym sym).WF ↔ dse.WF := by
  symm; constructor <;> intro h; infer_instance
  convert_to dse.sym sym |>.sym sym⁻¹ |>.WF
  · simp
  · infer_instance

@[simp]
theorem merge_empty_left : merge ∅ dse = dse := by
  ext:1 <;> simp [merge]

@[simp]
theorem merge_empty_right : merge dse ∅ = dse := by
  ext:1 <;> simp [merge]

@[simp] theorem ofList_nil : ofList [] = ∅ := rfl
@[simp] theorem ofList_cons {d ds} : ofList (d :: ds) = merge d (ofList ds) := rfl

@[simp] theorem cnd_merge : (dse₁.merge dse₂).cnd = λ s => dse₁.cnd s ∧ dse₂.cnd s := rfl
@[simp] theorem ps_merge : (dse₁.merge dse₂).ps = dse₁.ps ∪ dse₂.ps := rfl
@[simp] theorem f_merge : (dse₁.merge dse₂).f = λ s => dse₁.f s <|> dse₂.f s := rfl

@[simp]
theorem st_merge : (dse₁.merge dse₂).st = λ d => dse₁.st (dse₂.st d) := by
  simp [merge]; delta st; simp

theorem st_merge_ext {d} : (dse₁.merge dse₂).st d = dse₁.st (dse₂.st d) := by
  simp

@[simp]
theorem validTr_merge_of_wf [H₁ : dse₁.WF] [H₂ : dse₂.WF] : (dse₁.merge dse₂).ValidTr := by
  intro s hs p hp
  simp at hp
  rcases hp with hp | ⟨h₁, h₂⟩
  · exact valid_tr hp
  · exact valid_tr h₂

@[refl, simp]
theorem Compatible.refl : dse.Compatible dse := by
  simp [Compatible, Compatible']; intros; simp_all only [Option.some.injEq]

@[symm]
theorem Compatible.symm (h : dse₁.Compatible dse₂) : dse₂.Compatible dse₁ := by
  simp [Compatible, Compatible'] at h ⊢
  intro s₀ s p₁ p₂ hs h₁ h₂ h₃ h₄ h₅
  exact h h₂ h₁ h₃ h₅ h₄ |>.symm

@[simp]
theorem compatible_empty_left : Compatible ∅ dse := by
  simp [Compatible, Compatible']

@[simp]
theorem compatible_empty_right : Compatible dse ∅ := by
  simp [Compatible, Compatible']

theorem compatible_merge_left_of {a b c} (h₁ : Compatible a c)
(h₂ : Compatible b c) : Compatible (merge a b) c := by
  simp [Compatible, Compatible'] at h₁ h₂ ⊢
  intro s₀ s p₁ p₂ h₀ ha hb h₄ h₅ h₆ h₇
  rcases h₆ with h₆ | ⟨h₆, h₈⟩
  · exact h₁ ha h₄ h₅ h₆ h₇
  · exact h₂ hb h₄ h₅ h₈ h₇

theorem compatible_merge_right_of {a b c} (h₁ : Compatible a b)
(h₂ : Compatible a c) : Compatible a (merge b c) := by
  symm at *; exact compatible_merge_left_of h₁ h₂

theorem compatible_ofList_of_forall_compatible {e : Defense} {ds : List Defense}
(h : ∀ e₁ ∈ ds, e.Compatible e₁) : e.Compatible (ofList ds) := by
  induction ds; simp
  nm e' ds ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  specialize @ih h₂
  simp; exact compatible_merge_right_of h₁ ih

-- theorem compatibleList_of_compatibleList_cons {d ds}
-- (h : CompatibleList (d :: ds)) : CompatibleList ds := by
--   intros s₀ hs₀ s p₁ p₂ d₁ d₂ h₁ h₂ h₃ h₄ h₅ h₆
--   specialize @h s₀ _ s p₁ p₂ d₁ d₂
--   simp at h

-- #check 0 #exit

-- theorem compatible_ofList_of_compatibleList {d : Defense} {ds : List Defense}
-- (h : CompatibleList (d :: ds)) : d.Compatible (ofList ds) := by
--   induction ds; simp
--   nm d' ds ih
--   simp

-- #check 0 #exit

@[simp]
theorem compatibleList_nil : CompatibleList [] := by
  simp [CompatibleList, CompatibleList']

-- theorem compatible_of_compatibleList {ds d₁ d₂} (h : CompatibleList ds)
-- (h₁ : d₁ ∈ ds) (h₂ : d₂ ∈ ds) : Compatible d₁ d₂ := by
--   unfold CompatibleList at h
-- 
-- #check 0 #exit
-- 
-- theorem of_compatibleList_cons {e ds} (h : CompatibleList (e :: ds)) :
-- CompatibleList ds ∧ ∀ e₁ ∈ ds, e.Compatible e₁ := by
--   simp [CompatibleList]
--   split_ands
--   · intro e₁ e₂ he₁ he₂
--     specialize @h e₁ e₂
--     simp [he₁, he₂] at h
--     exact h
--   · intro e₁ he₁
--     specialize @h e e₁
--     simp [he₁] at h
--     exact h

@[simp]
theorem validTr_empty : ValidTr ∅ := by
  simp [ValidTr]

theorem validTr_merge_of (h₁ : ValidTr dse₁) (h₂ : ValidTr dse₂) :
ValidTr # merge dse₁ dse₂ := by
  intro s hs p h
  simp at h
  rcases h with h | ⟨h₃, h₄⟩
  · exact h₁ h
  · exact h₂ h₄

theorem validTr_ofList' {ds : List Defense}
(H : ∀ d ∈ ds, d.ValidTr) : (ofList ds).ValidTr := by
  induction ds; simp
  nm e ds ih
  simp at H ⊢
  rcases H with ⟨h₁, h₂⟩
  exact validTr_merge_of h₁ # @ih h₂

theorem validTr_ofList {ds : List Defense}
(H : ∀ d ∈ ds, d.WF) : (ofList ds).ValidTr :=
  validTr_ofList' # λ d hd => H d hd |>.1

@[simp]
theorem merge_self {d} : merge d d = d := by
  simp [merge]

theorem merge_assoc {a b c} : merge (merge a b) c = merge a (merge b c) := by
  simp [merge, and_assoc, Set.union_assoc, Option.or_assoc]

@[simp]
theorem ofList_append {ds₁ ds₂} : ofList (ds₁ ++ ds₂) = merge (ofList ds₁) (ofList ds₂) := by
  induction ds₁ <;> simp; nm d ds₁ ih; simp [ih, merge_assoc]

@[simp]
theorem cnd_ofList {ds s} : (ofList ds).cnd s ↔ ∀ d ∈ ds, d.cnd s := by
  induction ds <;> simp; grind

@[simp]
theorem ps_ofList {ds} : (ofList ds).ps = ⋃ d ∈ ds, d.ps := by
  induction ds <;> simp; grind

@[simp]
theorem st_empty : (∅ : Defense).st = id := by
  ext:1; simp [st]

theorem compatibleList'_of_perm {p} {ds₁ ds₂ : List Defense}
(h₁ : CompatibleList' p ds₁) (h₂ : ds₁.Perm ds₂) : CompatibleList' p ds₂ := by
  unfold CompatibleList' at h₁ ⊢; grind

theorem compatibleList_of_perm {ds₁ ds₂ : List Defense}
(h₁ : CompatibleList ds₁) (h₂ : ds₁.Perm ds₂) : CompatibleList ds₂ :=
  compatibleList'_of_perm h₁ h₂

theorem compatibleList'_iff_of_perm {p} {ds₁ ds₂ : List Defense}
(h : ds₁.Perm ds₂) : CompatibleList' p ds₁ ↔ CompatibleList' p ds₂ :=
  ⟨λ h₁ => compatibleList'_of_perm h₁ h, λ h₁ => compatibleList'_of_perm h₁ h.symm⟩

theorem compatibleList_iff_of_perm {ds₁ ds₂ : List Defense}
(h : ds₁.Perm ds₂) : CompatibleList ds₁ ↔ CompatibleList ds₂ :=
  compatibleList'_iff_of_perm h

theorem of_compatibleList'_cons {p d ds} (h : CompatibleList' p (d :: ds)) :
CompatibleList' (λ s => d.cnd s ∧ p s) ds := by
  unfold CompatibleList' at h ⊢; grind

theorem of_compatibleList_cons {d ds} (h : CompatibleList (d :: ds)) :
CompatibleList' d.cnd ds := by
  have h₁ := @of_compatibleList'_cons (h := h)
  simp at h₁; simp_all only

theorem of_f_ofList_eq_some {ds s p} (h : (ofList ds).f s = some p) :
∃ d ∈ ds, d.f s = some p := by
  induction ds <;> simp_all; grind

theorem wf_merge {e₁ e₂ : Defense} [He₁ : e₁.WF] [He₂ : e₂.WF]
(h₀ : Compatible e₁ e₂) : (e₁.merge e₂).WF := by
  use validTr_merge_of_wf
  intro s hs h a Ha d Hd n
  simp at h
  rcases h with ⟨h₁, h₂⟩
  have H₁ := He₁.2 h₁ a (e₂.st d) n
  have H₂ := He₂.2 h₂ a (e₁.st d) n
  generalize hr : sys.simulate (Strat.f ⟨a, e₁.st # e₂.st d⟩) s n = r at H₁
  have h₃ : sys.simulate (Strat.f ⟨a, e₂.st # e₁.st d⟩) s n = r
  · rw [←hr, ←simulate_st_comm]
    intro s' h₃ p₁ p₂ h₄
    have hs' := sys.wf_of_reachable h₃
    intro h₅; exact @h₀ s _ s' p₁ p₂ (by simp) h₁ h₂ h₃ h₄ h₅
  rw [h₃] at H₂; clear h₃
  have h₄ : sys.simulate (Strat.f ⟨a, (e₁.merge e₂).st d⟩) s n = r
  · convert hr using 2; ext1 s
    unfold Strat.f; split_ifs with ht <;> simp
  rw [h₄]; simp [H₁, H₂]

theorem wf_iff_validTr_and_wf' {d : Defense} : d.WF ↔ d.ValidTr ∧ d.WF' (λ _ => True) := by
  simp [WF']; constructor
  · intro h; cases h; nm h₁ h₂; use h₁
  · rintro ⟨h₁, h₂⟩; use h₁

-- @[simp] theorem cnd_setCnd {d cnd} : (setCnd d cnd).cnd = cnd := rfl
-- @[simp] theorem ps_setCnd {d cnd} : (setCnd d cnd).ps = d.ps := rfl
-- @[simp] theorem f_setCnd {d cnd} : (setCnd d cnd).f = d.f := rfl
-- 
-- @[simp]
-- theorem ofList_accCndList {d ds} : ofList (accCndList d ds) = ofList (d :: ds) := by
--   unfold accCndList; ext:1 <;> simp; ext s p :2; simp; induction ds <;> simp; grind
-- 
-- @[simp]
-- theorem length_accCndList {d ds} : (accCndList d ds).length = ds.length + 1 := by
--   simp [accCndList]

theorem wf_dStrat_of_validTr {d : DStrat} [Hd : d.WF] (h : dse.ValidTr) : (dse.st d).WF := by
  unfold st; rw [DStrat.wf_iff]; intro s hs
  dsimp; cases h₁ : dse.f s <;> simp; exact h h₁

@[simp]
theorem compatibleList'_nil {p} : CompatibleList' p [] := by
  simp [CompatibleList']

theorem compatibleList'_append_comm {p ds₁ ds₂} :
CompatibleList' p (ds₁ ++ ds₂) ↔ CompatibleList' p (ds₂ ++ ds₁) :=
  compatibleList'_iff_of_perm List.perm_append_comm

theorem right_of_compatibleList'_append {p ds₁ ds₂} (h : CompatibleList' p (ds₁ ++ ds₂)) :
CompatibleList' (λ s => (∀ d ∈ ds₁, d.cnd s) ∧ p s) ds₂ := by
  induction ds₁ generalizing ds₂ p
  · simp at h ⊢; simp_all only
  nm d ds₁ ih
  simp
  replace h := @of_compatibleList'_cons (h := h)
  specialize @ih _ _ h
  clear h
  grind

theorem left_of_compatibleList'_append {p ds₁ ds₂} (h : CompatibleList' p (ds₁ ++ ds₂)) :
CompatibleList' (λ s => (∀ d ∈ ds₂, d.cnd s) ∧ p s) ds₁ := by
  rw [compatibleList'_append_comm] at h
  exact right_of_compatibleList'_append h

theorem wf'_of_imp {d p₁ p₂} (h₁ : WF' p₁ d) (h₂ : ∀ s, p₂ s → p₁ s) : WF' p₂ d := by
  unfold WF' at h₁ ⊢; grind

theorem simulate_st_comm' {s₀ n} {a : AStrat} {d : DStrat}
[hs₀ : sys.WF s₀] [Ha : a.WF] [Hd : d.WF]
(hv₁ : dse₁.ValidTr) (hv₂ : dse₂.ValidTr)
(h : ∀ s, sys.Reachable s₀ s → ∀ {p₁ p₂},
dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
sys.simulate (Strat.f ⟨a, dse₁.st (dse₂.st d)⟩) s₀ n =
sys.simulate (Strat.f ⟨a, dse₂.st (dse₁.st d)⟩) s₀ n := by
  have G₁ : dse₁.st d |>.WF; exact wf_dStrat_of_validTr hv₁
  have G₀ : dse₂.st d |>.WF; exact wf_dStrat_of_validTr hv₂
  have G₂ : dse₁.st (dse₂.st d) |>.WF; exact wf_dStrat_of_validTr hv₁
  have G₃ : dse₂.st (dse₁.st d) |>.WF; exact wf_dStrat_of_validTr hv₂
  apply simulate_congr <;> simp
  intro k hk s hs h₁ h₂ h₃
  simp [st]
  cases H₃ : dse₁.f s <;> cases H₄ : dse₂.f s <;> simp
  nm p₁ p₂
  have H₅ := sys.reachable_of_simulate h₁
  exact @h s H₅ p₁ p₂ H₃ H₄

theorem wf_ofList {ds : List Defense} (H : ∀ d ∈ ds, d.WF)
(h₀ : CompatibleList ds) : (ofList ds).WF := by
  rw [wf_iff_validTr_and_wf']
  generalize hp : (λ s => True) = p at h₀
  replace H : ∀ d ∈ ds, d.ValidTr ∧ d.WF' p
  · simp [←hp]
    simp_rw [wf_iff_validTr_and_wf'] at H
    exact H
  unfold CompatibleList at h₀
  rw [hp] at h₀
  clear hp
  generalize hN : ds.length = N
  induction N using Nat.strong_induction_on generalizing ds p
  nm N IH
  use validTr_ofList' # by grind
  intro s₀ hs₀ G h a Ha d Hd n
  generalize hr : sys.simulate (Strat.f ⟨a, (ofList ds).st d⟩) s₀ n = r
  rcases r with ⟨s, r⟩
  have hx := sys.reachable_of_simulate hr
  simp
  intro e he
  replace he := List.eq_append_cons_of_mem he
  obtain ⟨ds₁, ds₂, hds, -⟩ := he
  generalize hds' : e :: (ds₁ ++ ds₂) = ds'
  have H₁ : ds.Perm ds'
  · simp [hds, ←hds']
  simp [hds] at hr
  generalize hd' : (ofList ds₂).st d = d' at hr
  replace hd' : d'.WF
  · simp [←hd']
    apply wf_dStrat_of_validTr
    apply validTr_ofList'
    simp [hds] at H
    grind
  clear Hd d
  rename' d' => d, hd' => hd
  generalize H₂ : ofList ds₁ = e₁ at hr
  obtain ⟨he', he⟩ : e.ValidTr ∧ e.WF' p
  · grind
  rw [hds] at h₀
  have h₀' := @left_of_compatibleList'_append (h := h₀)
  generalize hp' : (λ s => (∀ d ∈ e :: ds₂, d.cnd s) ∧ p s) = p'
  obtain ⟨he₁', he₁⟩ : e₁.ValidTr ∧ e₁.WF' p'
  · subst H₂ hp'
    apply @IH ds₁.length (by grind) ds₁ _ h₀' _ rfl
    intro y hy
    simp [hds] at H
    specialize H y
    simp [hy] at H
    rcases H with ⟨H₃, H₄⟩
    use H₃
    apply wf'_of_imp H₄
    simp
  have hd₁ : e₁.st d |>.WF
  · exact wf_dStrat_of_validTr he₁'
  rw [simulate_st_comm'] at hr
  rotate_left
  · grind
  · grind
  · intro s₁ hs₁ p₁ p₂ hp₁ hp₂
    simp [←H₂] at hp₁
    replace hp₁ := of_f_ofList_eq_some hp₁
    choose e₂ H₃ hp₁ using hp₁
    specialize @h₀ s₀ _ s₁ p₁ p₂ e₂ e _ _ hs₁
    · simp [hds] at h; grind
    · simp [hds] at h; grind
    simp [H₃, hp₁, hp₂] at h₀
    exact h₀
  specialize @he s₀ _ G _ a _ (e₁.st d) _ n
  · simp [hds] at h
    grind
  simp [hr] at he
  exact he

theorem compatible'_of_compatible {d₁ d₂ p} (h : Compatible d₁ d₂) : Compatible' p d₁ d₂ := by
  dsimp [Compatible, Compatible'] at h ⊢; grind

theorem compatible'_of_compatibleList' {p ds d₁ d₂} (h : CompatibleList' p ds)
(h₁ : d₁ ∈ ds) (h₂ : d₂ ∈ ds) : Compatible' (λ s => (∀ d ∈ ds, d.cnd s) ∧ p s) d₁ d₂ := by
  dsimp [CompatibleList', Compatible'] at h ⊢; grind

theorem compatible'_of_compatibleList {ds d₁ d₂} (h : CompatibleList ds)
(h₁ : d₁ ∈ ds) (h₂ : d₂ ∈ ds) : Compatible' (λ s => ∀ d ∈ ds, d.cnd s) d₁ d₂ := by
  have h₃ := @compatible'_of_compatibleList' (h := h) (h₁ := h₁) (h₂ := h₂)
  simp at h₃; simp_all only

theorem compatibleList_iff_getElem {ds : List Defense} : CompatibleList ds ↔
∀ i j (h₁ : i < j) (h₂ : j < ds.length), ds[i].Compatible' (λ s => ∀ d ∈ ds, d.cnd s) ds[j] := by
  constructor
  · intro h i j h₁ h₂
    apply compatible'_of_compatibleList h <;> simp
  intro h s₀ hs₀ s p₁ p₂ d₁ d₂ h₀ h₁ h₂ h₃ h₄ h₅ h₆
  rw [List.mem_iff_getElem] at h₃ h₄
  unfold Compatible' at h; grind

theorem compatibleList_iff_getElem! {ds : List Defense} : CompatibleList ds ↔
∀ i j, i < j → j < ds.length → ds[i]!.Compatible' (λ s => ∀ d ∈ ds, d.cnd s) ds[j]! := by
  convert compatibleList_iff_getElem <;> apply getElem!_pos

theorem f_st_eq_of_f_eq_none {s d} (h : dse.f s = none) : (dse.st d).f s = d.f s := by
  simp [st, h]

theorem f_st_eq_of_f_eq_some {s d p} (h : dse.f s = some p) : (dse.st d).f s = p := by
  simp [st, h]

@[simp]
theorem f_ofList_eq_none_iff {ds s} : (ofList ds).f s = none ↔ ∀ d ∈ ds, d.f s = none := by
  induction ds <;> simp; grind