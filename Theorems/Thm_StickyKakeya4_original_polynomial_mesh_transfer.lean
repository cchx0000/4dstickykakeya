import Theorems.Thm_StickyKakeya4_gkz_grid_code_perturbation
import Theorems.Thm_StickyKakeya4_projection_annulus_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace OriginalPolynomialMeshTransfer
open ActualRoundedAdditiveEnergy GKZGridCodePerturbation


/-- Select an actual dyadic engine mesh above the required normalized
cutoff, with only a factor-two loss. -/
theorem exists_original_coarser_dyadic_mesh {epsilon : ℝ}
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    ∃ k : ℕ, epsilon ≤ ProjectionAnnulusEnergy.mesh k ∧
      ProjectionAnnulusEnergy.mesh k ≤ 2*epsilon := by
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one he he1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  refine ⟨k,hhi,?_⟩
  rw [pow_succ] at hlo
  change (1/2:ℝ)^k ≤ 2*epsilon
  linarith only [hlo]

/-- A coarse occupied floor cover has at most four times the fine cover.
The bound holds for the exact original value map, including boundary cells. -/
theorem original_coarse_cover_le {X : Type*} (P : Finset X) (f : X → ℝ)
    {delta epsilon : ℝ} (hd : 0 < delta) (hde : delta ≤ epsilon) :
    ((P.image (fun x => rounded epsilon (f x))).card:ℝ) ≤
      4*(P.image (fun x => rounded delta (f x))).card := by
  have he : 0 < epsilon := hd.trans_le hde
  have ha : |delta/epsilon| ≤ 1 := by
    rw [abs_of_pos (div_pos hd he)]
    exact (div_le_one he).mpr hde
  have hh := bounded_dilation_floor_image P f hd (by norm_num : (0:ℝ)≤1) ha
  have hid : ∀ x : X, rounded delta ((delta/epsilon)*f x)=rounded epsilon (f x) := by
    intro x
    unfold rounded
    congr 1
    calc
      ((delta/epsilon)*f x)/delta=(delta/delta)*(f x/epsilon) := by ring
      _ = f x/epsilon := by rw [div_self hd.ne',one_mul]
  simpa only [hid,show (2:ℝ)*1+2=4 by norm_num] using hh

/-- The normalized profile cutoff and the homogeneous output mesh are
both respected, even when the selected original radius exceeds one. -/
theorem original_homogeneous_mesh (R delta : ℝ) (d : ℕ)
    (hR : 0 < R) (hd : 0 < delta) :
    let base := max (delta/R) (delta/R^d)
    delta/R ≤ base ∧ delta ≤ base*R^d ∧
      base*min R (R^d)=delta := by
  dsimp
  have hpow : 0 < R^d := pow_pos hR d
  refine ⟨le_max_left _ _,?_,?_⟩
  · exact (div_le_iff₀ hpow).mp (le_max_right _ _)
  · rcases le_total R (R^d) with h | h
    · have hdiv : delta/R^d ≤ delta/R := div_le_div_of_nonneg_left hd.le hR h
      rw [max_eq_left hdiv,min_eq_left h,div_mul_cancel₀ _ hR.ne']
    · have hdiv : delta/R ≤ delta/R^d := div_le_div_of_nonneg_left hd.le hpow h
      rw [max_eq_right hdiv,min_eq_right h,div_mul_cancel₀ _ hpow.ne']

/-- A true homogeneous image lower bound at an admissible normalized mesh
transfers to the original mesh. The exact old value map remains the source. -/
theorem original_homogeneous_cover_transfer {X : Type*}
    (P : Finset X) (f : X → ℝ) (d : ℕ) {R delta epsilon L : ℝ}
    (hR : 0 < R) (hd : 0 < delta) (he : 0 < epsilon)
    (hcoarse : delta ≤ epsilon*R^d)
    (hupper : epsilon*min R (R^d) ≤ 2*delta)
    (himage : L ≤ epsilon*((P.image (fun x => rounded epsilon (f x))).card:ℝ)) :
    min R (R^d)*L ≤
      8*delta*((P.image (fun x => rounded delta (R^d*f x))).card:ℝ) := by
  have hpow : 0 < R^d := pow_pos hR d
  have hmin : 0 < min R (R^d) := lt_min hR hpow
  have hh := original_coarse_cover_le P (fun x => R^d*f x) hd hcoarse
  have hid : ∀ x : X, rounded (epsilon*R^d) (R^d*f x)=rounded epsilon (f x) := by
    intro x
    unfold rounded
    congr 1
    rw [mul_comm epsilon (R^d),mul_div_mul_left _ _ hpow.ne']
  simp only [hid] at hh
  have h1 := mul_le_mul_of_nonneg_left hh he.le
  have h2 := mul_le_mul_of_nonneg_left (himage.trans h1) hmin.le
  have h3 := mul_le_mul_of_nonneg_right hupper
    (show 0 ≤ 4*((P.image (fun x => rounded delta (R^d*f x))).card:ℝ) by positivity)
  nlinarith only [h2,h3]

end OriginalPolynomialMeshTransfer
