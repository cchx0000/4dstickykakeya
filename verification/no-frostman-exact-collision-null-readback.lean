import Theorems.Thm_StickyKakeya4_no_frostman_exact_collision_null

set_option autoImplicit false

#print axioms StickyKakeya4.NoFrostmanExactCollision.lintegral_sq_eq_zero_iff
#print axioms StickyKakeya4.NoFrostmanExactCollision.edge_mass_eq_zero_of_rootedDensity_eq_zero
#print axioms StickyKakeya4.NoFrostmanExactCollision.exactEdges
#print axioms StickyKakeya4.NoFrostmanExactCollision.measurableSet_exactEdges
#print axioms StickyKakeya4.NoFrostmanExactCollision.exactWeight
#print axioms StickyKakeya4.NoFrostmanExactCollision.measurable_exactWeight
#print axioms StickyKakeya4.NoFrostmanExactCollision.exactWeight_le_one
#print axioms StickyKakeya4.NoFrostmanExactCollision.exactWeight_ne_zero_iff
#print axioms StickyKakeya4.NoFrostmanExactCollision.exact_cycle_times_eq
#print axioms StickyKakeya4.NoFrostmanExactCollision.exact_cycle_third_mem_root_bush
#print axioms StickyKakeya4.NoFrostmanExactCollision.rootSuccess_eq_zero_of_bush_null
#print axioms StickyKakeya4.NoFrostmanExactCollision.exactEdges_null_of_bush_null
#print axioms StickyKakeya4.NoFrostmanExactCollision.tendsto_fixed_angle_residual_mass_zero
#print axioms StickyKakeya4.NoFrostmanExactCollision.exact_bush_null_of_no_front_frostman
#print axioms StickyKakeya4.NoFrostmanExactCollision.no_front_frostman_exact_collision_null
#print axioms StickyKakeya4.NoFrostmanExactCollision.no_front_frostman_tendsto_fixed_angle_residual_mass_zero
#print axioms StickyKakeya4.NoFrostmanExactCollision.oldGraph_mass_le_fixed_angle_residual_mass
#print axioms StickyKakeya4.NoFrostmanExactCollision.tendsto_oldGraph_mass_zero
#print axioms StickyKakeya4.NoFrostmanExactCollision.no_front_frostman_tendsto_oldGraph_mass_zero
#print axioms StickyKakeya4.NoFrostmanExactCollision.tendsto_dominated_fine_residual_lift_mass_zero

open MeasureTheory Set Filter
open scoped ENNReal Topology
open StickyKakeya4

example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) :
    (σ.prod σ) {p : E3 × E3 | p.1 ≠ p.2 ∧
      collisionResidual (p.1 - p.2) (b p.1 - b p.2) = 0} = 0 :=
  NoFrostmanExactCollision.no_front_frostman_exact_collision_null ambient hcompact
    σ hσ b hb hslopes u v huv hsupport hno

example (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (J : Set ℝ) (sep : ℝ) (hsep : 0 < sep) :
    Tendsto (fun r : ℝ => (σ.prod σ).withDensity
      (ActualResidualCycleWitness.oldGraphWeight b J sep r) univ)
      (𝓝[>] 0) (𝓝 0) :=
  NoFrostmanExactCollision.no_front_frostman_tendsto_oldGraph_mass_zero ambient hcompact
    σ hσ b hb hslopes u v huv hsupport hno J sep hsep
