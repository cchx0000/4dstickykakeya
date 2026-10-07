import Theorems.Thm_StickyKakeya4_native_reference_parent_grain_cleanup
import Theorems.Thm_StickyKakeya4_native_history_grain_power_density
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_fibers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeSharpXCapCancellation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeParentVertexMassCap NativeSpatialParentCount
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSourceParentGrainCleanup NativeHistoryGrainPowerDensity
open scoped BigOperators

/-- The original raw-vertex cap cancels against the original class-count
threshold. No reciprocal vertex-cap factor survives. -/
lemma cross_cap_cancellation {W M L N B T U A loss Ht X grains : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hN : 0 < N) (hB : 0 ≤ B)
    (hU : 0 ≤ U) (hloss : 0 ≤ loss) (hHt : 0 ≤ Ht) (hX : 0 ≤ X)
    (hcount : N ≤ B*grains) (hgrain : M*L*grains ≤ T)
    (hcross : A*(W/(2*N)) ≤ loss*(U*M)*Ht*X) :
    A*W*L ≤ 2*B*T*U*loss*Ht*X := by
  have hcross' : A*W ≤ (loss*(U*M)*Ht*X)*(2*N) := by
    apply (div_le_iff₀ (show 0 < 2*N by positivity)).mp
    simpa only [mul_div_assoc] using hcross
  have hscaled := mul_le_mul_of_nonneg_right hcross' hL
  have hclasses : M*L*N ≤ B*T := by
    calc
      _ ≤ (M*L)*(B*grains) := mul_le_mul_of_nonneg_left hcount (mul_nonneg hM hL)
      _ = B*(M*L*grains) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrain hB
  calc
    _ ≤ (2*U*loss*Ht*X)*(M*L*N) := by nlinarith only [hscaled]
    _ ≤ (2*U*loss*Ht*X)*(B*T) :=
      mul_le_mul_of_nonneg_left hclasses (by positivity)
    _ = _ := by ring

end NativeSharpXCapCancellation
