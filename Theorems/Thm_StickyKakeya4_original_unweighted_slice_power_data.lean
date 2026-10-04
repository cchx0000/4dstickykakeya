import Theorems.Thm_StickyKakeya4_native_original_unweighted_slice_frame
import Theorems.Thm_StickyKakeya4_original_unweighted_planar_power_transport
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

noncomputable section
namespace OriginalUnweightedSlicePowerData
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalVoronoiFibers
open OriginalThreeDimensionalGridBalancedFibers OriginalProjectedOwnerProfile
open OriginalNormalizedOwnerGraph OriginalNormalizedOwnerQuery NativeOriginalUnweightedSliceFrame
open OriginalThreeDimensionalOwnerCoefficientBudget OriginalUnweightedPlanarPowerTransport

/-- The actual separated planar owner points and actual original-edge
image, with all numerical losses measured at the original fine mesh. -/
def OwnerPowerData (G : Finset Pair3) (b : Frame3) (C : Finset Point3) (hC : C.Nonempty)
    (delta Delta r eta zeta q e2 : ℝ) : Prop :=
  let X := normalizedImage b C
  let J := normalizedOwnerGraph b G C hC
  X.Nonempty ∧ (∀ x∈X,|x.1| ≤ 1 ∧ |x.2| ≤ 1) ∧
    (∀ x∈X,∀ y∈X,x≠y → Delta/32 ≤ PlanarFrostmanBallConversion.euclideanDistance x y) ∧
    (∀ a : ℝ×ℝ,∀ R : ℝ,Delta/32 ≤ R →
      ((X.filter (fun x => PlanarFrostmanBallConversion.euclideanDistance a x ≤ R)).card : ℝ) ≤
        delta^(-21*eta)*R*X.card) ∧
    J⊆X.product X ∧ J.Nonempty ∧ delta^(14*eta)*(X.card : ℝ)^2 ≤ J.card ∧
    ∀ e∈J,e.1≠e.2 ∧
      (∃ z∈G,normalizedPair b (originalOwner C hC z.1) (originalOwner C hC z.2)=e) ∧
      delta^(-zeta/9)*(50*Delta/r)*X.card ≤
        (OriginalPhysicalPairTube.physicalPairTube X (50*Delta/r) e).card ∧
      ((OriginalPhysicalPairTube.physicalPairTube X (q/16) e).card : ℝ) ≤
        delta^(zeta*e2/20)*X.card

/-- The already constructed same-C original slice output supplies these
powers by the genuine fixed-parameter budgets. No new point profile,
graph density, rich population or nonconcentration premise is introduced. -/
theorem original_constructed_slice_power_data (P Q S : Finset Point3)
    (G : Finset Pair3) (b : Frame3) (delta Delta r eta zeta q e2 E L : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hDelta : 0 < Delta)
    (hrdef : r=delta^(2*eta)) (hzeta : 0 < zeta) (he2 : 0 < e2)
    (heta : eta ≤ zeta/1000) (hetaCap : eta ≤ zeta*e2/10000)
    (hE : 0 < E) (hL : 0 < L)
    (hdecay : Delta ≤ 32*delta^(zeta/5)) (howner : 1600*Delta/r ≤ q)
    (henergy : E/L ≤ delta^(-9*eta))
    (hfiber : uniformFiberConstant (delta^(-eta)) ≤ delta^(-2*eta))
    (hconst : 4096*delta^eta ≤ 1)
    (hcapConst : (32:ℝ)^e2*delta^(zeta*e2/10) ≤ 1)
    (hdata : OriginalUnweightedSliceOutput P Q S G b Delta r (delta^(-eta))
      (4*E/L) (L/(32*E)) (delta^(-zeta/8)*Delta) q (Delta^e2)) :
    ∃ C : Finset Point3,∃ hC : C.Nonempty,C⊆S ∧
      OwnerPowerData G b C hC delta Delta r eta zeta q e2 := by
  let A := uniformFiberConstant (delta^(-eta))
  let T := E/L
  let lam := L/(32*E)
  have hT : 0 < T := div_pos hE hL
  have hr : 0 < r := by rw [hrdef]; positivity
  have hcancel : 32*T*lam=1 := by dsimp [T,lam]; field_simp
  obtain ⟨C,hC,M,hCS,_hSU,_hUQ,_hM,hA1,_hweights,_hpartition,
      hX,_hcard,hbox,hsep,hprofile,hJG,hJ,hdensity,hedges⟩ := hdata
  have hA : 0 < A := zero_lt_one.trans_le hA1
  obtain ⟨hcapCoeff,hprofileCoeff,hdensityCoeff⟩ := original_owner_power_coefficients
    delta eta A T hd hA.le hT.le hfiber henergy hconst
  have hprofileId : 32*A*(4*E/L)/(L/(32*E))=4096*A*T^2 := by
    dsimp [T]
    field_simp
    ring
  have hcapPower := original_owner_cap_power delta eta zeta e2 Delta A T hd hd1 hzeta he2
    hDelta.le hdecay hetaCap hcapCoeff hcapConst
  have hrichPower : A*delta^(-zeta/9)*(50*Delta/r) ≤ delta^(-zeta/8)*Delta := by
    rw [hrdef]
    exact original_owner_richness_power delta eta zeta Delta A hd hd1 hDelta.le heta hzeta hfiber hconst
  have hquery : 8*(q/16)+64*Delta/r ≤ q := by
    have hq : 0 ≤ q := (show 0 ≤ 1600*Delta/r by positivity).trans howner
    rw [mul_div_assoc] at howner ⊢
    linarith only [howner,hq]
  have hNraw : ((normalizedImage b C).card : ℝ)^2 ≤
      (32*T*A^2)*(normalizedOwnerGraph b G C hC).card := by
    calc
      _ = (32*T)*(lam*((normalizedImage b C).card : ℝ)^2) := by rw [← mul_assoc,hcancel,one_mul]
      _ ≤ (32*T)*(A^2*(normalizedOwnerGraph b G C hC).card) :=
        mul_le_mul_of_nonneg_left hdensity (by positivity)
      _ = _ := by ring
  have hpowers : delta^(14*eta)*delta^(-14*eta)=1 := by
    rw [← Real.rpow_add hd,show 14*eta+(-14*eta)=0 by ring,Real.rpow_zero]
  have hJmass : delta^(14*eta)*((normalizedImage b C).card : ℝ)^2 ≤
      (normalizedOwnerGraph b G C hC).card := by
    calc
      _ ≤ delta^(14*eta)*((32*T*A^2)*(normalizedOwnerGraph b G C hC).card) :=
        mul_le_mul_of_nonneg_left hNraw (Real.rpow_nonneg hd.le _)
      _ ≤ delta^(14*eta)*(delta^(-14*eta)*(normalizedOwnerGraph b G C hC).card) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdensityCoeff (Nat.cast_nonneg _))
          (Real.rpow_nonneg hd.le _)
      _ = _ := by rw [← mul_assoc,hpowers,one_mul]
  refine ⟨C,hC,hCS,hX,hbox,hsep,?_,hJG,hJ,hJmass,?_⟩
  · intro a R hR
    have hRp : 0 ≤ R := (show 0 ≤ Delta/32 by positivity).trans hR
    have hc : 32*A*(4*E/L)/(L/(32*E)) ≤ delta^(-21*eta) := by
      rw [hprofileId]
      exact hprofileCoeff
    exact (hprofile a R hR).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hRp) (Nat.cast_nonneg _))
  · intro e he
    obtain ⟨hne,hwitness,hrich,hcap⟩ := hedges e he
    refine ⟨hne,hwitness,?_,?_⟩
    · apply (mul_le_mul_iff_of_pos_left hA).mp
      calc
        _ = (A*delta^(-zeta/9)*(50*Delta/r))*(normalizedImage b C).card := by ring
        _ ≤ (delta^(-zeta/8)*Delta)*(normalizedImage b C).card :=
          mul_le_mul_of_nonneg_right hrichPower (Nat.cast_nonneg _)
        _ ≤ _ := hrich
    · have hraw : ((OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) (q/16) e).card : ℝ) ≤
          ((32*A*T)*Delta^e2)*(normalizedImage b C).card := by
        calc
          _ = (32*T)*(lam*(OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) (q/16) e).card) := by
            rw [← mul_assoc,hcancel,one_mul]
          _ ≤ (32*T)*(A*Delta^e2*(normalizedImage b C).card) :=
            mul_le_mul_of_nonneg_left (hcap (q/16) hquery) (by positivity)
          _ = _ := by ring
      exact hraw.trans (mul_le_mul_of_nonneg_right hcapPower (Nat.cast_nonneg _))

end OriginalUnweightedSlicePowerData
