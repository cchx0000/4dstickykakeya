import Theorems.Thm_StickyKakeya4_native_selected_parent_preparation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace NativeParameterConstants

open NativeSelectedParentPreparation NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeContactFractionalComposition NativeFractionalReferenceComposition
open NativeContactSpineColumns ShearedGridSpineColumns

noncomputable section

/-- Exact density-loss formula derived from the source parent populations. -/
lemma density_cost_expand (A : Finset Plane) (N m Q L lo hi : ℕ) (K t : ℝ) :
    8192 * K * (64 : ℝ) ^ t * sourceMassCost A N m Q L lo hi K t =
      8192 * (64 : ℝ) ^ t * (epochCost A N : ℝ) * (refinementCost (m + 1) L : ℝ) *
        (Q : ℝ) ^ 6 * (angularCost lo hi m : ℝ) * spatialConstant K t * K ^ 2 := by
  unfold sourceMassCost
  ring

/-- Exact cancellation of the constructed pruning, parent-refinement and
spine-density denominators. The fixed-width spine is C=2 throughout. -/
lemma column_cost_expand (N m Q L : ℕ) (hm : 0 < m) (hQ : 0 < Q)
    {K H t : ℝ} (hK : 1 ≤ K) (hH : 0 < H) :
    contactColumnConstant 2 K H t (spineConstant N m Q L K t H) =
      (3081 * 525 * 400 : ℝ) * (Fintype.card (Index N) : ℝ) * (refinementCost m L : ℝ) *
        (Q : ℝ) ^ 2 * (spatialConstant K t) ^ 2 * H ^ 2 * K ^ 2 := by
  have hI : (0 : ℝ) < Fintype.card (Index N) := by exact_mod_cast index_card_pos N
  have hF : (0 : ℝ) < refinementCost m L := by
    unfold refinementCost
    have hcount : 0 < m + (m + m) := by omega
    positivity
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hKpos := zero_lt_one.trans_le hK
  have hsp := spatialConstant_pos (t := t) hK
  unfold contactColumnConstant spineConstant pruningRate
  norm_num only [contactOverlapBudget, localCapacity, Nat.cast_ofNat]
  rw [show (81 : ℝ) * (6 : ℝ) ^ t * K ^ 2 = spatialConstant K t by unfold spatialConstant; norm_num]
  field_simp
  ring

/-- The K powers in the exact column formula total six. -/
lemma spatial_squared (K t : ℝ) :
    (spatialConstant K t) ^ 2 * K ^ 2 = (9 : ℝ) ^ 4 * ((6 : ℝ) ^ t) ^ 2 * K ^ 6 := by
  unfold spatialConstant
  ring

/-- The K powers in the density multiplier total four. -/
lemma spatial_times_K_sq (K t : ℝ) :
    spatialConstant K t * K ^ 2 = (9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 4 := by
  unfold spatialConstant
  ring

end
end NativeParameterConstants
