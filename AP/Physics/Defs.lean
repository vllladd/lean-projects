import AP.Util
import AP.Euclidean

namespace Physics

noncomputable section

abbrev dim : ℕ := 2
abbrev Vec := Fin dim → ℝ

local notation3 "x" => (0 : Fin dim)
local notation3 "y" => (1 : Fin dim)

def Vec.norm (a : Vec) : ℝ :=
  (∑ i, a i ^ dim) ^ (dim : ℝ)⁻¹

def Vec.dist (a b : Vec) : ℝ :=
  (a - b).norm

scoped instance (priority := high) : Norm Vec where
  norm := Vec.norm

scoped instance (priority := high) : Dist Vec where
  dist := Vec.dist

theorem norm_def' {a : Vec} : ‖a‖ = (∑ i, a i ^ dim) ^ (dim : ℝ)⁻¹ := rfl
theorem dist_def' {a b : Vec} : dist a b = (a - b).norm := rfl

scoped instance (priority := high) : PseudoMetricSpace Vec where
  dist_self a := by simp [dist_def', Vec.norm]
  dist_comm a b := by simp [dist_def', Vec.norm, dim, sub_sq_comm]
  dist_triangle a b c := by
    simp [dist_def', Vec.norm]
    sorry

-- #check 0 #exit

scoped instance (priority := high) : MetricSpace Vec where
  eq_of_dist_eq_zero := by
    intro a b h
    simp [dist_def', Vec.norm, dim] at h
    rw [Real.rpow_inv_eq] at h <;> try positivity
    simp at h
    rw [add_eq_zero_iff_of_nonneg] at h <;> try positivity
    simp at h
    ext i
    fin_cases i <;> dsimp <;> linarith

example : ‖(![3, 4] : Vec)‖ = 5 := by
  simp [norm_def', dim]; rw [Real.rpow_inv_eq] <;> norm_num

-- #check 0 #exit

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
  
  hr : 0 < radius
  hm : 0 < mass

def Particle.overlaps (p₁ p₂ : Particle) : Prop :=
  ‖p₁.position - p₂.position‖ = 0

structure Simulator : Type where
  particles : Map ParticleId Particle