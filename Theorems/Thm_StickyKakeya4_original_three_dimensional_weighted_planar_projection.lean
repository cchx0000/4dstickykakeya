import Theorems.Thm_StickyKakeya4_original_three_dimensional_projection_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalWeightedPlanarProjection
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalFiniteCellWeights

/-- Actual original points in a unit-normal slab admit an orthogonal
planar projection and a literal Delta-cell quotient. All point and graph
mass remains on its original labels through exact fiber weights. The
only regularity input is the original source law above Delta. -/
theorem exists_original_weighted_planar_projection (P : Finset Point3)
    (G : Finset (Point3 × Point3)) (n : Point3) (c Delta K lam : ℝ)
    (hn : ∑ j,n j^2=1) (hDelta : 0<Delta) (hK : 0 ≤ K)
    (hbox : ∀ x∈P,∀ j,|x j| ≤ 1)
    (hslab : ∀ x∈P,|(∑ j,n j*x j)-c| ≤ Delta)
    (hG : G⊆P.product P) (hdense : lam*(P.card : ℝ)^2 ≤ (G.card : ℝ))
    (hfr : ∀ p∈P,∀ R : ℝ,Delta ≤ R →
      ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ K*R*P.card) :
    ∃ b : Frame3,
      (∀ x,frameCoordinate b 2 x=∑ j,n j*x j) ∧
      (∀ x∈P,|(project b x).1| ≤ 3 ∧ |(project b x).2| ≤ 3) ∧
      (∀ x∈P,frameCoordinate b 2 (orthogonalFoot b c x)=c ∧
        project b (orthogonalFoot b c x)=project b x ∧
        distance3 x (orthogonalFoot b c x) ≤ Delta) ∧
      (∀ x∈P,∀ y∈P,distance3 x y ≤ distance2 (project b x) (project b y)+2*Delta) ∧
      (∑ k∈occupied P (cellCode b Delta),pointWeight P (cellCode b Delta) k=(P.card : ℝ)) ∧
      (∑ z∈occupied G (pairCode (cellCode b Delta)),pairWeight G (cellCode b Delta) z=(G.card : ℝ)) ∧
      (∀ z,pairWeight G (cellCode b Delta) z ≤
        pointWeight P (cellCode b Delta) z.1*pointWeight P (cellCode b Delta) z.2) ∧
      (lam*(∑ k∈occupied P (cellCode b Delta),pointWeight P (cellCode b Delta) k)^2 ≤
        ∑ z∈occupied G (pairCode (cellCode b Delta)),pairWeight G (cellCode b Delta) z) ∧
      (∀ a r,∑ k∈ballCells P b Delta a r,pointWeight P (cellCode b Delta) k ≤
        8*K*max r Delta*P.card) := by
  obtain ⟨b,hb⟩ := exists_original_normal_frame n hn
  have hslab' (x : Point3) (hx : x∈P) : |frameCoordinate b 2 x-c| ≤ Delta := by
    rw [hb]
    exact hslab x hx
  refine ⟨b,hb,?_,?_,?_,point_mass_readback P (cellCode b Delta),
    pair_mass_readback G (cellCode b Delta),?_,?_,?_⟩
  · intro x hx
    exact original_projected_coordinate_bounds b x (hbox x hx)
  · intro x hx
    refine ⟨orthogonalFoot_on_plane b c x,project_orthogonalFoot b c x,?_⟩
    rw [distance_to_orthogonalFoot]
    exact hslab' x hx
  · intro x hx y hy
    exact original_slab_distance_comparison b c Delta x y (hslab' x hx) (hslab' y hy)
  · exact pairWeight_le_pointWeight_product P G (cellCode b Delta) hG
  · exact original_graph_weighted_density P G (cellCode b Delta) lam hdense
  · exact original_cell_weighted_frostman P b c Delta K hDelta hK hslab' hfr

end OriginalThreeDimensionalWeightedPlanarProjection
