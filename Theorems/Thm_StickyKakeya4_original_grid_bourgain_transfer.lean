import Theorems.Thm_StickyKakeya4_original_bourgain_graph_transfer
import Theorems.Thm_StickyKakeya4_integer_bin_real_near_energy
import Theorems.Thm_StickyKakeya4_original_weak_scalar_positive_power
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalGridBourgainTransfer
open ActualRoundedAdditiveEnergy IntegerBinRealNearEnergy OriginalDenseCoefficientProjection
open OriginalDenseCoefficientCounts

def scaledPoint (delta : ℝ) (z : ℤ × ℤ) : ℝ × ℝ :=
  (delta*(z.1:ℝ),delta*(z.2:ℝ))

lemma original_scaled_round {delta : ℝ} (hd : 0 < delta) (x : ℝ) (z : ℤ × ℤ) :
    rounded delta ((scaledPoint delta z).1+x*(scaledPoint delta z).2)=
      OriginalBourgainGraphTransfer.code x z := by
  unfold rounded OriginalBourgainGraphTransfer.code OriginalBourgainGraphTransfer.value scaledPoint
  congr 1
  have he : delta*(z.1:ℝ)+x*(delta*(z.2:ℝ))=delta*((z.1:ℝ)+x*(z.2:ℝ)) := by ring
  rw [he,mul_div_cancel_left₀ _ hd.ne']

/-- The original scalar growth image and the exact integer graph code
coincide on the literal target mesh, without a new rounding loss. -/
theorem original_grid_sum_cover (A : Finset ℤ) {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    sumCover (realGrid delta A) delta x=(A.product A).image (OriginalBourgainGraphTransfer.code x) := by
  have hprod : (realGrid delta A).product (realGrid delta A)=
      (A.product A).image (scaledPoint delta) := by
    exact (Finset.prodMap_image_product (fun z : ℤ => delta*(z:ℝ))
      (fun z : ℤ => delta*(z:ℝ)) A A).symm
  change ((realGrid delta A).product (realGrid delta A)).image
    (fun z => rounded delta (z.1+x*z.2)) = _
  rw [hprod,Finset.image_image]
  apply Finset.image_congr
  intro z _hz
  exact original_scaled_round hd x z

/-- Every original graph inherits the exact integer Bourgain transfer
while the expansion theorem sees its actual separated real-grid alphabet. -/
theorem original_grid_graph_transfer (A B : Finset ℤ) (G : Finset (ℤ × ℤ))
    {delta : ℝ} (hd : 0 < delta) (x : ℝ) (hG : G⊆A.product B) :
    G.card*(sumCover (realGrid delta A) delta x).card ≤
      2*(A-A).card*(B-A).card*(G.image (OriginalBourgainGraphTransfer.code x)).card := by
  rw [original_grid_sum_cover A hd x]
  exact OriginalBourgainGraphTransfer.original_integer_graph_transfer A B G x hG

end OriginalGridBourgainTransfer
