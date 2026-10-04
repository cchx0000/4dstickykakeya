import Theorems.Thm_StickyKakeya4_original_polynomial_elimination
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalSlabRelation
open ActualRoundedAdditiveEnergy

def shiftPoint {I : Type*} (d : ℝ) (tau : I → ℤ) (x : I → ℝ) : I → ℝ :=
  fun i => x i+2*d*(tau i:ℝ)
def relationCoefficients {I : Type*} (d : ℝ) (tau sigma : I → ℤ)
    (x y : I → ℝ) : I → ℝ :=
  fun i => x i-y i+2*d*((tau i:ℝ)-(sigma i:ℝ))

/-- A collision between literal translated projection cells supplies an
actual original relation, with the full mesh residual retained. -/
theorem original_translated_cell_relation {I : Type*} [Fintype I]
    (v x y : I → ℝ) (tau sigma : I → ℤ) {delta d : ℝ}
    (hd : 0 < delta)
    (hcell : rounded delta (∑ i, v i*shiftPoint d tau x i)=
      rounded delta (∑ i, v i*shiftPoint d sigma y i)) :
    |∑ i, v i*relationCoefficients d tau sigma x y i| ≤ delta := by
  have hx := round_error hd (∑ i, v i*shiftPoint d tau x i)
  have hy := round_error hd (∑ i, v i*shiftPoint d sigma y i)
  rw [hcell] at hx
  have he : (∑ i, v i*relationCoefficients d tau sigma x y i)=
      (∑ i, v i*shiftPoint d tau x i)-(∑ i, v i*shiftPoint d sigma y i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [relationCoefficients,shiftPoint]
    ring
  rw [he]
  exact abs_le.mpr ⟨by linarith only [hx.1,hx.2,hy.1,hy.2],
    by linarith only [hx.1,hx.2,hy.1,hy.2]⟩

/-- Different lattice translates force a coefficient at least as large as
the original diameter, while every coefficient retains an explicit bound. -/
theorem original_relation_coefficient_bounds {I : Type*}
    (x y : I → ℝ) (tau sigma : I → ℤ) {d B : ℝ}
    (hd : 0 < d) (hne : tau≠sigma)
    (hxy : ∀ i, |x i-y i| ≤ d)
    (htau : ∀ i, |(tau i:ℝ)| ≤ B) (hsigma : ∀ i, |(sigma i:ℝ)| ≤ B) :
    (∃ j, d ≤ |relationCoefficients d tau sigma x y j|) ∧
      ∀ i, |relationCoefficients d tau sigma x y i| ≤ d*(1+4*B) := by
  have hw : ∃ j, tau j≠sigma j := by
    by_contra h
    push Not at h
    exact hne (funext h)
  constructor
  · obtain ⟨j,hj⟩ := hw
    have hzInt : (1:ℤ) ≤ |tau j-sigma j| := by
      have hp : (0:ℤ) < |tau j-sigma j| := abs_pos.mpr (sub_ne_zero.mpr hj)
      omega
    have hz : (1:ℝ) ≤ |(tau j:ℝ)-(sigma j:ℝ)| := by exact_mod_cast hzInt
    have he : 2*d*((tau j:ℝ)-(sigma j:ℝ))=
        relationCoefficients d tau sigma x y j-(x j-y j) := by
      dsimp [relationCoefficients]
      ring
    have ht := abs_sub_le (relationCoefficients d tau sigma x y j) 0 (x j-y j)
    simp only [sub_zero,zero_sub,abs_neg] at ht
    rw [← he,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hd] at ht
    have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2*d by positivity)
    exact ⟨j,by nlinarith only [ht,hm,hxy j]⟩
  · intro i
    have hz : |(tau i:ℝ)-(sigma i:ℝ)| ≤ 2*B := by
      have hh := abs_sub_le (tau i:ℝ) 0 (sigma i:ℝ)
      simp only [sub_zero,zero_sub,abs_neg] at hh
      nlinarith only [hh,htau i,hsigma i]
    have ht := abs_add_le (x i-y i) (2*d*((tau i:ℝ)-(sigma i:ℝ)))
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hd] at ht
    have hm := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2*d by positivity)
    change |x i-y i+2*d*((tau i:ℝ)-(sigma i:ℝ))| ≤ _
    nlinarith only [ht,hm,hxy i]

end OriginalSlabRelation
