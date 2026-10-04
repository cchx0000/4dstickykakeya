import Theorems.Thm_StickyKakeya4_original_finite_dimension_reduction
import Theorems.Thm_StickyKakeya4_original_quadratic_words
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace OriginalPureQuadraticDimensionDrop
open ActualRoundedAdditiveEnergy OriginalPolynomialSlab OriginalSlabRelation OriginalSlabCollision
open OriginalTensorFrostman OriginalPolynomialDimensionDrop OriginalFiniteDimensionReduction
open OriginalQuadraticWords

def wordCount (n : ℕ) (d L : ℝ) : ℕ := 2+8*((2*n+1)*slabRadius n d L)

/-- A finite polynomial form of the dimension-reduction step. Choosing the
actual original interval endpoints turns every constructed coefficient into
original differences of products. The new alphabet is a fixed-length sum of
those actual original quadratic differences. -/
theorem exists_original_quadratic_dimension_drop (n : ℕ)
    (A : Finset ℝ) (v : Fin (n+1) → ℝ) {delta lo d L : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hd : 0 < d) (hL : 0 < L)
    (hn : 1 ≤ n) (hv : ∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1)
    (hlo : lo∈A) (hhi : lo+d∈A)
    (hbox : ∀ a∈A, lo ≤ a ∧ a ≤ lo+d)
    (himage : L ≤ delta*((tensor A (n+1)).image
      (fun a => rounded delta (∑ i, v i*a i))).card) :
    ∃ j : Fin (n+1),
      d*L ≤ (2+2*coefficientBound n d L)*(2*(|lo|+d)+4)*delta*
        ((tensor (wordCount n d L • quadraticDifferences A) n).image
          (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card := by
  obtain ⟨tau,htau,sigma,hsigma,x,hx,y,hy,j,_hlarge,hupper,hgrow⟩ :=
    exists_original_finite_dimension_reduction n A v hdelta hdelta1 hd hL hn hv hbox himage
  let T : ℕ := (2*n+1)*slabRadius n d L
  let m : Fin (n+1) → ℤ := fun i => 2*(tau i-sigma i)
  let c := relationCoefficients d tau sigma x y
  have hcoefficient : c=(fun i => x i-y i+d*(m i:ℝ)) := by
    funext i
    dsimp [c,relationCoefficients,m]
    push_cast
    ring
  have htauB : ∀ i, |(tau i:ℝ)| ≤ T := by
    obtain ⟨a,_ha,haeq⟩ := Finset.mem_image.mp htau
    rw [← haeq]
    intro i
    have hb := slabVector_coordinate_bound hv a i
    simpa only [T,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hb
  have hsigmaB : ∀ i, |(sigma i:ℝ)| ≤ T := by
    obtain ⟨a,_ha,haeq⟩ := Finset.mem_image.mp hsigma
    rw [← haeq]
    intro i
    have hb := slabVector_coordinate_bound hv a i
    simpa only [T,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hb
  have hm : ∀ i, |(m i:ℝ)| ≤ (4*T:ℕ) := by
    intro i
    have hh := abs_sub_le (tau i:ℝ) 0 (sigma i:ℝ)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have hb : |(tau i:ℝ)-(sigma i:ℝ)| ≤ 2*(T:ℝ) := by
      nlinarith only [hh,htauB i,hsigmaB i]
    dsimp [m]
    push_cast
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [hb]
  have hsub : reducedAlphabet A c j ⊆ wordCount n d L • quadraticDifferences A := by
    rw [hcoefficient]
    have hh := original_reduced_alphabet_quadratic A x y m j (4*T) hlo hhi
      (Fintype.mem_piFinset.mp hx) (Fintype.mem_piFinset.mp hy) hm
    have he : 2+4*T+4*T=wordCount n d L := by dsimp [wordCount,T]; omega
    rw [he] at hh
    exact hh
  have htensor : tensor (reducedAlphabet A c j) n ⊆
      tensor (wordCount n d L • quadraticDifferences A) n :=
    Fintype.piFinset_subset _ _ (fun _ => hsub)
  have hcard : (((tensor (reducedAlphabet A c j) n).image
      (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card:ℝ) ≤
      ((tensor (wordCount n d L • quadraticDifferences A) n).image
        (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image htensor))
  have hC : 0 ≤ coefficientBound n d L := (abs_nonneg (c j)).trans (hupper j)
  have hfactor : 0 ≤ (2+2*coefficientBound n d L)*(2*(|lo|+d)+4)*delta := by positivity
  exact ⟨j,hgrow.trans (mul_le_mul_of_nonneg_left hcard hfactor)⟩

end OriginalPureQuadraticDimensionDrop
