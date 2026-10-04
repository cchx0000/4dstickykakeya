import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
import Theorems.Thm_StickyKakeya4_original_physical_tube_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThreeDimensionalSliceMaximizer
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalUnitSlabs
open OriginalThreeDimensionalTubeSlab OriginalPhysicalTubeScaleSelection

def enlargedSlice (P : Finset Point3) (rho : ℝ) (d : DirectionLabel) (k : ℤ)
    (D : ℝ) : Finset Point3 :=
  P.filter (fun p => |unitValue rho d p-rho*k/normalLength rho d|≤D)

def sliceScore (Q : Finset Point3) (z : Pair3) (alpha radius : ℝ) : ℝ :=
  (physicalPairTube3 Q radius z).card/radius^alpha

/-- The original Euclidean tube convention is monotone at every width. -/
theorem original_physical_tube3_mono (Q : Finset Point3) (z : Pair3)
    {a b : ℝ} (hab : a≤b) : physicalPairTube3 Q a z⊆physicalPairTube3 Q b z := by
  intro p hp
  obtain ⟨hpQ,l,hl⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpQ,l,hl.trans hab⟩

/-- A genuine inner-menu comparison yields actual annular half-mass.
This lemma deliberately requires the inner radius to belong to the
maximization domain; it makes no lower-endpoint assertion. -/
theorem original_slice_annular_half_mass (Q : Finset Point3) (z : Pair3)
    (alpha tau c : ℝ) (htau : 0<tau) (hc : 0<c) (hc1 : c≤1)
    (hcontract : c^alpha≤1/2)
    (hmax : sliceScore Q z alpha (tau*c)≤ sliceScore Q z alpha tau) :
    ((physicalPairTube3 Q tau z).card : ℝ)/2≤
      ((physicalPairTube3 Q tau z\physicalPairTube3 Q (tau*c) z).card : ℝ) := by
  have hinner := (div_le_div_iff₀ (Real.rpow_pos_of_pos (mul_pos htau hc) alpha)
    (Real.rpow_pos_of_pos htau alpha)).mp hmax
  rw [Real.mul_rpow htau.le hc.le] at hinner
  have hsmall : ((physicalPairTube3 Q (tau*c) z).card : ℝ)≤
      (physicalPairTube3 Q tau z).card*c^alpha := by
    apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos htau alpha)).mp
    nlinarith only [hinner]
  have hhalf := hsmall.trans (mul_le_mul_of_nonneg_left hcontract
    (Nat.cast_nonneg (physicalPairTube3 Q tau z).card))
  have hsub := original_physical_tube3_mono Q z
    (show tau*c≤tau by nlinarith only [mul_le_mul_of_nonneg_left hc1 htau.le])
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hcardR : ((physicalPairTube3 Q tau z\physicalPairTube3 Q (tau*c) z).card : ℝ)+
      (physicalPairTube3 Q (tau*c) z).card=(physicalPairTube3 Q tau z).card := by exact_mod_cast hcard
  linarith only [hhalf,hcardR]

/-- The actual original slice has a maximizing dyadic radius. Its
concentration score and upper scale power are retained. The lower-menu
boundary is sent to the small-radius branch, rather than assigned an
unproved annular mass. -/
theorem exists_original_slice_maximizer_with_boundary
    (P : Finset Point3) (rho D : ℝ) (d : DirectionLabel) (k : ℤ) (z : Pair3)
    (n M j0 : ℕ) (alpha theta : ℝ)
    (hj0 : j0≤n) (_htheta : 0≤theta)
    (hcontract : (dyadicRadius M)^alpha≤1/2)
    (hbottom : dyadicRadius n≤dyadicRadius M*D)
    (hQ : (enlargedSlice P rho d k D).Nonempty)
    (hconcentration : theta*((enlargedSlice P rho d k D).card : ℝ)≤
      (physicalPairTube3 (enlargedSlice P rho d k D) (dyadicRadius j0) z).card) :
    let Q := enlargedSlice P rho d k D
    ∃ j : ℕ, j≤n ∧
      (∀ i≤n, sliceScore Q z alpha (dyadicRadius i)≤ sliceScore Q z alpha (dyadicRadius j)) ∧
      theta*Q.card*(dyadicRadius j/dyadicRadius j0)^alpha≤
        (physicalPairTube3 Q (dyadicRadius j) z).card ∧
      theta*(dyadicRadius j)^alpha≤(dyadicRadius j0)^alpha ∧
      (dyadicRadius j≤D ∨
        j+M≤n ∧
        ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)/2≤
          ((physicalPairTube3 Q (dyadicRadius j) z\
            physicalPairTube3 Q (dyadicRadius (j+M)) z).card : ℝ)) := by
  let Q := enlargedSlice P rho d k D
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range (n+1))
    (fun i => sliceScore Q z alpha (dyadicRadius i)) ⟨0,Finset.mem_range.mpr (by omega)⟩
  have hjn : j≤n := by have hh := Finset.mem_range.mp hj; omega
  have hmax' (i : ℕ) (hi : i≤n) := hmax i (Finset.mem_range.mpr (by omega))
  have hp (i : ℕ) : 0<dyadicRadius i := by dsimp [dyadicRadius]; positivity
  have h0 := hmax' j0 hj0
  have hcross := (div_le_div_iff₀ (Real.rpow_pos_of_pos (hp j0) alpha)
    (Real.rpow_pos_of_pos (hp j) alpha)).mp h0
  have hl := mul_le_mul_of_nonneg_right hconcentration
    (Real.rpow_nonneg (hp j).le alpha)
  have hlow : theta*(Q.card : ℝ)*(dyadicRadius j/dyadicRadius j0)^alpha≤
      (physicalPairTube3 Q (dyadicRadius j) z).card := by
    rw [Real.div_rpow (hp j).le (hp j0).le,← mul_div_assoc]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (hp j0) alpha)).mpr
    change theta*(Q.card : ℝ)*(dyadicRadius j)^alpha≤_
    dsimp [Q] at hcross ⊢
    exact hl.trans hcross
  have hpop : ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)≤Q.card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hQp : 0<(Q.card : ℝ) := by exact_mod_cast hQ.card_pos
  have hupper : theta*(dyadicRadius j)^alpha≤(dyadicRadius j0)^alpha := by
    have hh := hl.trans (hcross.trans (mul_le_mul_of_nonneg_right hpop
      (Real.rpow_nonneg (hp j0).le alpha)))
    apply (mul_le_mul_iff_of_pos_right hQp).mp
    dsimp [Q] at hh ⊢
    nlinarith only [hh]
  refine ⟨j,hjn,hmax',hlow,hupper,?_⟩
  by_cases hinner : j+M≤n
  · right
    have hc1 : dyadicRadius M≤1 := by
      dsimp [dyadicRadius]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have heq : dyadicRadius (j+M)=dyadicRadius j*dyadicRadius M := by
      exact pow_add _ _ _
    refine ⟨hinner,?_⟩
    rw [heq]
    exact original_slice_annular_half_mass Q z alpha (dyadicRadius j) (dyadicRadius M)
      (hp j) (hp M) hc1 hcontract (by simpa only [heq] using hmax' (j+M) hinner)
  · left
    have hpow : dyadicRadius (j+M)≤dyadicRadius n := by
      dsimp [dyadicRadius]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have heq : dyadicRadius (j+M)=dyadicRadius j*dyadicRadius M := pow_add _ _ _
    rw [heq] at hpow
    apply (mul_le_mul_iff_of_pos_right (hp M)).mp
    nlinarith only [hpow,hbottom]

end OriginalThreeDimensionalSliceMaximizer
