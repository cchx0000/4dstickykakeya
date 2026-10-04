import Theorems.Thm_StickyKakeya4_native_original_bounded_nonconcentrated_rows
import Theorems.Thm_StickyKakeya4_original_three_dimensional_marked_slice_incidences
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThreeDimensionalMarkedPairCap
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalHeavySliceGraph OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalThreeDimensionalNonconcentratedRowMass NativeOriginalConcentratedPairGraph
open OriginalThreeDimensionalMarkedSliceIncidences OriginalThreeDimensionalExpandedSliceMultiplicity

/-- The literal surviving original direction row, after its actual slice
mass cutoff. Both filters retain the original heavy-slab code. -/
def boundedNonconcentratedRows (P : Finset Point3)
    (rho r eta1 e1 e2 q : ℝ) (z : Pair3) : Finset DirectionLabel :=
  smallSliceDirections P
    (goodDirections P rho (rho^(1+eta1)*P.card) z\
      concentratedDirections P rho r eta1 e1 e2 z)
    (chosenHeavySlabCode P rho (rho^(1+eta1)*P.card) z)
    rho (54*rho/r) r q

/-- Membership in the ACTUAL marked graph supplies the selected-slice
normalization of the pair cap. The original ambient P population never
replaces the selected slice population in this estimate. -/
theorem original_marked_nonconcentrated_pair_cap (P : Finset Point3)
    (G : Finset Pair3) (rho r eta1 e1 e2 q : ℝ) (s : SliceLabel) (z : Pair3)
    (hz : z∈markedGraph P G rho (rho^(1+eta1)*P.card)
      (boundedNonconcentratedRows P rho r eta1 e1 e2 q) s) :
    ((physicalPairTube3 (enlargedSlice P rho s.1 s.2 (54*rho/r))
      ((54*rho/r)^e1) z).card : ℝ) ≤
      (54*rho/r)^e2*(enlargedSlice P rho s.1 s.2 (54*rho/r)).card := by
  obtain ⟨_hzG,hd,hcode⟩ := Finset.mem_filter.mp hz
  have hdU := (Finset.mem_filter.mp hd).1
  obtain ⟨hdGood,hdNot⟩ := Finset.mem_sdiff.mp hdU
  apply le_of_not_gt
  intro hlarge
  apply hdNot
  apply Finset.mem_filter.mpr
  refine ⟨hdGood,?_⟩
  simpa only [hcode] using hlarge

end OriginalThreeDimensionalMarkedPairCap
