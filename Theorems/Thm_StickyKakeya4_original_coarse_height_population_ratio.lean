import Theorems.Thm_StickyKakeya4_original_coarse_height_curve
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalCoarseHeightPopulationRatio
open Classical DyadicOriginalFiberSelection OriginalCoarseHeightCurve OriginalSeparatedHeightCap
/-- Count the full selected original heights through actual coarse cells,
 using only the original separation-based fiber upper bound. -/
theorem selected_height_card_upper (Z : Finset ℝ) (j : ℕ) {delta width : ℝ}
    (hd : 0 < delta) (hw : 0 < width)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → delta ≤ |z-z'|) :
    ((bin Z (coarseHeight width) j).card : ℝ) ≤
      (width/delta+2)*(((bin Z (coarseHeight width) j).image (coarseHeight width)).card : ℝ) := by
  let W := bin Z (coarseHeight width) j
  let Q := W.image (coarseHeight width)
  have hf : ∀ k ∈ Q, ((W.filter (fun z => coarseHeight width z=k)).card : ℝ) ≤ width/delta+2 := by
    intro k _hk
    have hsub : W.filter (fun z => coarseHeight width z=k) ⊆ Z.filter (fun z => ⌊z/width⌋=k) := by
      intro z hz
      obtain ⟨hzW,hzk⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzW).1,hzk⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (original_coarse_height_fiber_cap Z hd hw hsep k)
  have hh := FinePointSlabGeometry.card_le_real_mul_of_fibers W Q (coarseHeight width)
    (width/delta+2) (fun z hz => Finset.mem_image_of_mem _ hz) hf
  simpa only [mul_comm] using hh
/-- Original fine-height density and GRAPH-selected retention provide the
 actual coarse B cardinality at its normalized mesh width/rho. This is the
 source of the population lower bound used in relative ABC Frostman input. -/
theorem original_coarse_height_mass (Z : Finset ℝ) (j : ℕ)
    {delta width rho beta lambda loss : ℝ} (hd : 0 < delta) (hrho : 0 < rho)
    (hwidth : delta ≤ width) (hbeta : 0 ≤ beta) (hloss : 0 < loss)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → delta ≤ |z-z'|)
    (hdensity : lambda*rho ≤ (Z.card : ℝ)*delta)
    (hretention : beta*(Z.card : ℝ) ≤ loss*((bin Z (coarseHeight width) j).card : ℝ)) :
    beta*lambda/(3*loss) ≤ (width/rho)*(((bin Z (coarseHeight width) j).image (coarseHeight width)).card : ℝ) := by
  let N := ((bin Z (coarseHeight width) j).card : ℝ)
  let Q := (((bin Z (coarseHeight width) j).image (coarseHeight width)).card : ℝ)
  have hcount := selected_height_card_upper Z j hd (hd.trans_le hwidth) hsep
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscaled : N*delta ≤ 3*width*Q := by
    calc
      _ ≤ ((width/delta+2)*Q)*delta := mul_le_mul_of_nonneg_right hcount hd.le
      _ = (width+2*delta)*Q := by field_simp [ne_of_gt hd]
      _ ≤ 3*width*Q := by nlinarith [mul_le_mul_of_nonneg_right hwidth hQ]
  have hcombined : beta*lambda*rho ≤ 3*loss*width*Q := by
    calc
      _ = beta*(lambda*rho) := by ring
      _ ≤ beta*((Z.card : ℝ)*delta) := mul_le_mul_of_nonneg_left hdensity hbeta
      _ = (beta*(Z.card : ℝ))*delta := by ring
      _ ≤ (loss*N)*delta := mul_le_mul_of_nonneg_right hretention hd.le
      _ = loss*(N*delta) := by ring
      _ ≤ loss*(3*width*Q) := mul_le_mul_of_nonneg_left hscaled hloss.le
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity : 0 < 3*loss)).mpr
  apply (mul_le_mul_iff_right₀ hrho).mp
  change rho*(beta*lambda) ≤ rho*((width/rho)*Q*(3*loss))
  calc
    _ = beta*lambda*rho := by ring
    _ ≤ 3*loss*width*Q := hcombined
    _ = (3*loss*width*Q)*(rho/rho) := by rw [div_self hrho.ne',mul_one]
    _ = rho*((width/rho)*Q*(3*loss)) := by ring
end OriginalCoarseHeightPopulationRatio
