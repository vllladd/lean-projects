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
instance [H : dse.WF] {d : DStrat} [Hd : d.WF] : (dse.st d).WF := by
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
  have H₅ := sys.reachable_of_simulate_eq h₁
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
      
      have Hb₁ := sys.wf_of_simulate_eq hb₁
      have Hb₂ := sys.wf_of_simulate_eq hb₂
      dsimp at Hb₁ Hb₂
      
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

@[simp]
theorem validTr_merge [H₁ : dse₁.WF] [H₂ : dse₂.WF] : (dse₁.merge dse₂).ValidTr := by
  intro s hs p hp
  simp at hp
  rcases hp with hp | ⟨h₁, h₂⟩
  · exact valid_tr hp
  · exact valid_tr h₂

theorem wf_merge {e₁ e₂ : Defense} [He₁ : e₁.WF] [He₂ : e₂.WF]
(h₀ : Compatible e₁ e₂) : (e₁.merge e₂).WF := by
  use validTr_merge
  intro s hs h a Ha d Hd n
  simp at h
  rcases h with ⟨h₁, h₂⟩
  have H₁ := He₁.2 h₁ a (e₂.st d) n
  have H₂ := He₂.2 h₂ a (e₁.st d) n
  generalize hr : sys.simulate (Strat.f ⟨a, e₁.st # e₂.st d⟩) s n = r at H₁
  have h₃ : sys.simulate (Strat.f ⟨a, e₂.st # e₁.st d⟩) s n = r
  · rw [←hr, ←Defense.simulate_st_comm]
    intro s' h₃ p₁ p₂ h₄
    have hs' := sys.wf_of_reachable h₃
    intro h₅; exact h₀ h₄ h₅
  rw [h₃] at H₂; clear h₃
  have h₄ : sys.simulate (Strat.f ⟨a, (e₁.merge e₂).st d⟩) s n = r
  · convert hr using 2; ext1 s
    unfold Strat.f; split_ifs with ht <;> simp
  rw [h₄]; simp [H₁, H₂]

@[refl, simp]
theorem Compatible.refl : dse.Compatible dse := by
  simp [Compatible]; intros; simp_all only [Option.some.injEq]

@[symm]
theorem Compatible.symm (h : dse₁.Compatible dse₂) : dse₂.Compatible dse₁ := by
  simp [Compatible] at h ⊢; intro s hs p₁ p₂ h₁ h₂; exact h h₂ h₁ |>.symm

@[simp]
theorem compatible_empty_left : Compatible ∅ dse := by
  simp [Compatible]

@[simp]
theorem compatible_empty_right : Compatible dse ∅ := by
  simp [Compatible]

theorem compatible_merge_left_of {a b c} (h₁ : Compatible a c)
(h₂ : Compatible b c) : Compatible (merge a b) c := by
  intro s hs p₁ p₂ h₃ h₄
  simp at h₃
  rcases h₃ with h₃ | ⟨h₃, h₅⟩
  · exact h₁ h₃ h₄
  · exact h₂ h₅ h₄

theorem compatible_merge_right_of {a b c} (h₁ : Compatible a b)
(h₂ : Compatible a c) : Compatible a (merge b c) := by
  symm at *; exact compatible_merge_left_of h₁ h₂

theorem compatible_ofList_of {e : Defense} {ds : List Defense}
(h : ∀ e₁ ∈ ds, e.Compatible e₁) : e.Compatible (ofList ds) := by
  induction ds; simp
  nm e' ds ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  specialize @ih h₂
  simp; exact compatible_merge_right_of h₁ ih

@[simp]
theorem compatibleList_nil : CompatibleList [] := by
  simp [CompatibleList]

@[simp]
theorem compatibleList_cons {e ds} :
CompatibleList (e :: ds) ↔ CompatibleList ds ∧ ∀ e₁ ∈ ds, e.Compatible e₁ := by
  simp [CompatibleList]
  constructor
  · intro h
    split_ands
    · intro e₁ e₂ he₁ he₂
      specialize @h e₁ e₂
      simp [he₁, he₂] at h
      exact h
    · intro e₁ he₁
      specialize @h e e₁
      simp [he₁] at h
      exact h
  · rintro ⟨h₁, h₂⟩ e₁ e₂ (rfl | he₁) (rfl | he₂)
    · rfl
    · exact h₂ _ he₂
    · symm; exact h₂ _ he₁
    · exact h₁ he₁ he₂

theorem wf_ofList {ds : List Defense} (H : ∀ d ∈ ds, d.WF)
(h₀ : CompatibleList ds) : (ofList ds).WF := by
  induction ds <;> simp
  nm e ds ih
  simp only [List.mem_cons, forall_eq_or_imp, compatibleList_cons] at H h₀
  rcases H with ⟨He, H⟩
  rcases h₀ with ⟨h₁, h₂⟩
  specialize ih H h₁
  apply wf_merge
  exact compatible_ofList_of h₂