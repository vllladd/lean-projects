import AP.AP.Defense.Edge.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

def cnd (e : Edge) (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := e.getBorderPoint₀ pa
  let get := e.getBorderPoints pa
  match e.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => 2 ≤ (p₀ :: get 1).countP (· ∈ s.taken)
  | 2 => sorry
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

theorem wf_defense : e.defense.WF := by
  have H := e.validTr_defense
  constructor; intro s hs h a Ha d Hd n
  sorry

-- #check 0 #exit

@[simp]
instance : e.defense.WF := wf_defense