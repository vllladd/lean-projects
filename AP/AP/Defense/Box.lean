import AP.AP.Defense.Corner

namespace AP.Box

def offset : ℕ := 106

def corner₀ : Corner where
  dir := .up
  offset := offset

def corners : List Corner :=
  List.range 4 |>.map (Corner.rotRight^[·] corner₀)

def defenses : List Defense :=
  corners.map (·.defense)

def defense : Defense :=
  .ofList defenses

-----

@[simp] theorem length_corners : corners.length = 4 := rfl
@[simp] theorem length_defenses : defenses.length = 4 := rfl

@[simp]
theorem getElem_corners_eq_iter_rotRight {i h} :
corners[i]'h = Corner.rotRight^[i] corner₀ := by
  simp [corners]; decide +revert

-- theorem compatible_0_1 : defenses[0].Compatible defenses[1] := by
--   simp [defenses]; apply Corner.compatible_rotRight; decide

-- #check 0 #exit
-- 
-- theorem compatible_getElem_defenses {i j} (h₁ : i < j) (h₂ : j < defenses.length) :
-- defenses[i].Compatible defenses[j] := by
--   revert h₂; rw![length_defenses]; intro h₂
--   obtain (rfl | rfl | rfl) : i = 0 ∨ i = 1 ∨ i = 2; omega
--   ·
--     obtain (rfl | rfl | rfl) : j = 1 ∨ j = 2 ∨ j = 3; omega
--     ·
--       sorry
--     · sorry
--     · sorry
--   · sorry
--   · sorry
-- 
-- #check 0 #exit
-- 
-- @[simp]
-- instance : defense.WF := by
--   apply Defense.wf_ofList; simp [defenses]
--   rw [Defense.compatibleList_iff_getElem]
--   intro i j; exact compatible_getElem_defenses