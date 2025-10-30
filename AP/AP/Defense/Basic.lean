import AP.AP.Defense.Defs

namespace AP.Defense

variable {dse dse₁ dse₂ : Defense}

instance : Inhabited Defense :=
  ⟨{cnd := λ _ => True, ps := ∅, f := λ _ => none}⟩

@[simp]
theorem default_def : (default : Defense) =
{cnd := λ _ => True, ps := ∅, f := λ _ => none} := rfl

@[simp] instance : WF default where
  valid_tr := by simp [ValidTr]
  not_mem_ps := by simp

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