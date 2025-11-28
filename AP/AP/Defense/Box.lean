import AP.AP.Defense.Corner

namespace AP.Box

def offset : ℕ := 106

def corners : List Corner :=
  Dir.univList.map (⟨·, offset⟩)

def defenses : List Defense :=
  corners.map (·.defense)

def defense : Defense :=
  .ofList defenses

-----

theorem compatible_of_mem_defenses {c₁ c₂}
(h₁ : c₁ ∈ defenses) (h₂ : c₂ ∈ defenses) : c₁.Compatible c₂ := by
  sorry

-- #check 0 #exit

@[simp]
instance : defense.WF :=
  Defense.wf_ofList (by simp [defenses]) compatible_of_mem_defenses