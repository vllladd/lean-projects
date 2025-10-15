import AP.Util
import AP.Euclidean

namespace Physics

noncomputable section

open scoped Euclidean

abbrev dim : ℕ := 2
abbrev Vec := Fin dim → ℝ

local notation3 "x" => (0 : Fin dim)
local notation3 "y" => (1 : Fin dim)

example : ‖(![3, 4] : Vec)‖ = 5 := by
  simp [Euclidean.norm_def, Euclidean.norm]; norm_num

----- Particle

structure ParticleId : Type where id : ℕ
deriving Inhabited, DecidableEq, Hashable

structure Particle : Type where
  id : ParticleId
  radius : ℝ
  mass : ℝ
  position : Vec
  velocity : Vec
  cVelocity : Option Vec
  resting : Bool
  restRef : Set' ParticleId
  restRefC : Set' ParticleId

class Particle.WF (p : Particle) : Prop where
  radius_pos : 0 < p.radius
  mass_pos : 0 < p.mass

instance : Inhabited Particle where
  default :=
    { id := ⟨0⟩
    , radius := 1
    , mass := 1
    , position := 0
    , velocity := 0
    , cVelocity := none
    , resting := false
    , restRef := ∅
    , restRefC := ∅
    }

instance : (default : Particle).WF where
  radius_pos := show 0 < 1 by norm_num
  mass_pos := show 0 < 1 by norm_num

def Particle.overlaps (p₁ p₂ : Particle) : Prop :=
  ‖p₁.position - p₂.position‖ = 0

----- Simulator

structure Simulator : Type where
  particles : Map ParticleId Particle

class Simulator.WF (sim : Simulator) : Prop where
  particle_id_eq : ∀ {i p}, sim.particles.get? i = some p → p.id = i

instance : Inhabited Simulator where
  default :=
    { particles := ∅
    }

instance : (default : Simulator).WF where
  particle_id_eq := by intro i p; change (∅ : Map _ _).get? i = _ → _; simp