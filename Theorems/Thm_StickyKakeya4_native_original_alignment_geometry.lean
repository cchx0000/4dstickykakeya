import Theorems.Thm_StickyKakeya4_native_original_parent_union
import Theorems.Thm_StickyKakeya4_literal_affine_fiber_coordinates

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace NativeOriginalAlignmentGeometry

open NativeOriginalParentAssembly NativeParentRefinement NativeSelectedParentPreparation NativeOriginalParentUnion
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines NativeAngularChartSelection
open ActualTubeFootprintProfiles NativeSeparatedFractionalPatches SmallFiberAlignment
open ShearedGridADReference NormalizedQuantizedPatches LiteralAffineFiberCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual normalized image, with scalar fibers recoverable from its
actual integer vertices. Original point populations are kept separately. -/
def normalizedImage (Ω : Finset Plane) (μ angle b : ℝ) (c : Plane) : Finset Plane :=
  Ω.image (affine c (64 * b) ∘ quantized μ angle)

structure NearGraphImage (Ω : Finset Plane) (μ angle b : ℝ) (c : Plane) : Prop where
  near : ∀ p ∈ Ω.image (affine c (64 * b)), ∃ q ∈ normalizedImage Ω μ angle b c,
    dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) <
      (64 * μ / (64 * b)) / 10
  back : ∀ q ∈ normalizedImage Ω μ angle b c, ∃ p ∈ Ω.image (affine c (64 * b)),
    dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) <
      (64 * μ / (64 * b)) / 10
  separated : ∀ p ∈ normalizedImage Ω μ angle b c, ∀ q ∈ normalizedImage Ω μ angle b c, p ≠ q →
    64 * μ / (64 * b) ≤ dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q)
  bounded : ∀ p ∈ normalizedImage Ω μ angle b c, ∀ i, |p i| ≤ 1 / 32
  graph : normalizedImage Ω μ angle b c =
    (quotientCoordinates (Ω.image (vertex μ angle)) μ angle (64 * b) c).biUnion
      (fun y => (fiberAt (Ω.image (vertex μ angle)) μ angle (64 * b) c y).image (fun x => ![x, angle * x + y]))

/-- Two-way proximity, separation, bounded location and literal graph fibers
are proved for the actual quantizer image of each constructed parent. -/
theorem refined_parent_near_graph {d : ℕ} {A : Finset Plane} (Ω : Finset A) (j : Fin 2)
    (μ angle b : ℝ) (c : GridLabel 1) (R : Fin d → ℕ) (N Q L : ℕ) (δ K t s H ell : ℝ)
    (F : RefinedParent ((parent A Ω b c).image (chartPosition A j)) μ angle R N Q L δ K t s H ell)
    (hμ : 0 < μ) (hμb : μ ≤ b) (q : A) (hq : grid (position A) b q = c) :
    NearGraphImage F.points μ angle b (chartPosition A j q) := by
  have hb : 0 < b := hμ.trans_le hμb
  have hL : 0 < 64 * b := by positivity
  have hnear := normalized_quantized_proximity F.points μ angle hμ (chartPosition A j q) hL
  refine ⟨hnear.1, hnear.2,
    normalized_image_separation F.points μ angle (chartPosition A j q) hL F.separated, ?_, ?_⟩
  · intro p hp i
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    have hrs := F.residue_subset (F.subset hr)
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hrs
    have hcell : ADGridCoverMenus.gridLabel b r = ADGridCoverMenus.gridLabel b (chartPosition A j q) := by
      rw [← he]
      apply chartPosition_same_cell
      exact (Finset.mem_filter.mp hz).2.trans hq.symm
    exact normalized_parent_coordinates μ angle b hμ hμb r (chartPosition A j q) hcell i
  · have h := actual_image_eq_graph_fibers (F.points.image (vertex μ angle)) μ angle (64 * b) (chartPosition A j q)
    rw [Finset.image_image] at h
    exact h

end
end NativeOriginalAlignmentGeometry
