import Theorems.Thm_StickyKakeya4_hausdorff_bush_routing

set_option autoImplicit false

#print axioms StickyKakeya4.HausdorffBushRouting.unitTime
#print axioms StickyKakeya4.HausdorffBushRouting.quarterStart
#print axioms StickyKakeya4.HausdorffBushRouting.sampledTime
#print axioms StickyKakeya4.HausdorffBushRouting.measurable_quarterStart
#print axioms StickyKakeya4.HausdorffBushRouting.measurable_sampledTime
#print axioms StickyKakeya4.HausdorffBushRouting.sampledTime_mem_slab
#print axioms StickyKakeya4.HausdorffBushRouting.sampledTime_separated
#print axioms StickyKakeya4.HausdorffBushRouting.measurable_heightPoint
#print axioms StickyKakeya4.HausdorffBushRouting.sampledPoint
#print axioms StickyKakeya4.HausdorffBushRouting.measurable_sampledPoint
#print axioms StickyKakeya4.HausdorffBushRouting.height_distance_lt_of_ball
#print axioms StickyKakeya4.HausdorffBushRouting.horizontalProjection_heightPoint
#print axioms StickyKakeya4.HausdorffBushRouting.bush_error_lt_of_ball
#print axioms StickyKakeya4.HausdorffBushRouting.ball_height_separated
#print axioms StickyKakeya4.HausdorffBushRouting.unitTime_ball_hit_le
#print axioms StickyKakeya4.HausdorffBushRouting.eventBranch
#print axioms StickyKakeya4.HausdorffBushRouting.eventBranch_le
#print axioms StickyKakeya4.HausdorffBushRouting.eventBranch_le_smul_of_fibre_le
#print axioms StickyKakeya4.HausdorffBushRouting.sum_eventBranch_ordered_eq
#print axioms StickyKakeya4.HausdorffBushRouting.ballEvents
#print axioms StickyKakeya4.HausdorffBushRouting.ballBranch
#print axioms StickyKakeya4.HausdorffBushRouting.measurableSet_ballEvents
#print axioms StickyKakeya4.HausdorffBushRouting.ballBranch_le
#print axioms StickyKakeya4.HausdorffBushRouting.ballBranch_le_radius_smul
#print axioms StickyKakeya4.HausdorffBushRouting.sum_ballBranch_eq
#print axioms StickyKakeya4.HausdorffBushRouting.sum_ballBranch_map_eq
#print axioms StickyKakeya4.HausdorffBushRouting.ae_good_labels
#print axioms StickyKakeya4.HausdorffBushRouting.ballBranch_ae_bush_and_separated
#print axioms StickyKakeya4.HausdorffBushRouting.exists_low_cost_separated_bush_routing
#print axioms StickyKakeya4.HausdorffBushRouting.exists_original_front_low_cost_separated_bush_routing

open Filter MeasureTheory Set
open scoped ENNReal
open StickyKakeya4 StickyKakeya4.ActualSlopeSource
open StickyKakeya4.HausdorffBushRouting

example
    {Ω : Type*} [MeasurableSpace Ω]
    (Γ : Measure Ω) [IsFiniteMeasure Γ] {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    (ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1)
    {u v : ℝ} (huv : u < v) (ambient : Set MarkedLine)
    (hcompact : IsCompact ambient)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v,
      heightPoint (b ω + s • a ω) s ∈ unitFront ambient)
    {q : NNReal} (hdim : dimH (unitFront ambient) < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ center : Fin n → E4, ∃ radius : Fin n → ℝ,
      unitFront ambient ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
      (∀ i, 0 < radius i ∧ radius i < rho ∧ radius i < (v - u) / 8) ∧
      (∑ i, radius i ^ (q : ℝ)) < epsilon ∧
      Measure.sum (ballBranch Γ a b t u v center radius) = Γ ∧
      ∀ i, ballBranch Γ a b t u v center radius i ≤ Γ ∧
        ballBranch Γ a b t u v center radius i ≤
          ENNReal.ofReal (8 * radius i / (v - u)) • Γ ∧
        ∀ᵐ ω ∂ballBranch Γ a b t u v center radius i,
          ‖b ω + center i (Fin.last 3) • a ω - horizontalProjection (center i)‖ <
            2 * radius i ∧
          (v - u) / 8 ≤ |center i (Fin.last 3) - t ω| :=
  exists_low_cost_separated_bush_routing Γ ha hb ht ha1 huv
    (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hcompact) hfront hdim hrho hepsilon


-- The whole original observable law is unchanged, including labels ignored by geometry.
example {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {n : ℕ}
    (Γ : Measure Ω) [IsFiniteMeasure Γ] {a b : Ω → E3} {t : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ht : Measurable t)
    {u v : ℝ} (huv : u < v) (front : Set E4)
    (hfront : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v, heightPoint (b ω + s • a ω) s ∈ front)
    (center : Fin n → E4) (radius : Fin n → ℝ)
    (hcover : front ⊆ ⋃ i, Metric.ball (center i) (radius i))
    (observable : Ω → Y) (hobservable : Measurable observable) :
    Measure.sum (fun i => (ballBranch Γ a b t u v center radius i).map observable) =
      Γ.map observable :=
  sum_ballBranch_map_eq Γ ha hb ht huv front hfront center radius hcover observable hobservable
