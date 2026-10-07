/- UNVERIFIED fixed top-interval source reader. Tau and its planar
alignment remain unchanged; only source support counts use depth6. -/
import Theorems.Thm_StickyKakeya4_native_joint_cell_phase_population
import Theorems.Thm_StickyKakeya4_native_relative_label_ancestry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeJointTopPhasePopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSourceCoherenceEngine NativePaidMeshAngularUpper NativeFixedCompactKakeyaExponent
open NativeLocalParentSource NativeMiddleGrainParentBudget NativeNormalizedCellRelativeMenu
open NativeRelativeParentLabels NativeJointKeyDescent

/-- The exact coarser phase labels descend from the depth15 support.
The fixed512^3 factor here pays kappa≤3 and tau≥1/512; it is NOT a
three-dimensional fiber bound for the six-dimensional phase map. -/
theorem from_reference (K : ℕ) (amin loss seedCap deltaUpper : ℝ)
    (Hupper : HasUpperEngine K amin loss seedCap deltaUpper)
    {n : ℕ} (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L g : ℕ)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta) (hetaSeed : eta ≤ seed/8)
    (hzseed : zeta ≤ seed/256) (hseed : seed ≤ seedCap) (hsmall : D.thickness ≤ deltaUpper)
    (ref : Reference h tau htau seed e zeta L g)
    (Hcaller : HasCallerUniformities ref (factory g K))
    (i : Fin (g+1)) (hstop : 6 ≤ (ref.schedule i).val)
    (m : ℕ) (hm : m = middleDepth (ref.schedule i).val)
    (r power : ℝ) (hr : 0 < r) (hrscale : r ≤ D.thickness^power) (hpower : amin ≤ power)
    (hdelta : 64*D.thickness ≤ r^2) (hMiddle : 3072*r ≤ (64/((2^m:ℕ):ℝ))^2)
    (p : Parent) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (hParent : ∀ z ∈ E, parentLabel D ref.a (2^m) z.1 = p)
    (cell : Index) (hCell : ∀ z ∈ E, physicalCell D ref.a (2^m) (2^6) p z.2 = cell)
    (localEta profile : ℝ)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h ref.R ref.E1 ref.a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h ref.R ref.E1 ref.a m p).thickness ^ profile ≤ D.thickness ^ zeta)
    (hmb : m+15 ≤ ref.level) (b : ℕ) (hb : 6 ≤ b) (hb15 : b ≤ 15) :
    ((E.image (fun z => relativeLabel D ref.a (2^m) p (2^b) z.1)).card:ℝ) ≤
      ((512:ℝ)^3*(64:ℝ)^3*(5832*130^3)*meshAngularConstant*
        (source h ref.R ref.E1 ref.a m p).thickness^(-profile)*r^(-loss))*
        (64/((2^b:ℕ):ℝ))^(-extremalExponent) := by
  have hbase := NativeJointCellPhasePopulation.from_reference K amin loss seedCap deltaUpper Hupper
    D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall ref Hcaller i hstop
    m hm 6 (by norm_num) (by omega) r power hr hrscale hpower hdelta hMiddle
    p E hE hParent cell hCell localEta profile hReferenceNative hbudget hmb
  norm_num only [show (2:ℕ)^6=64 by norm_num,Nat.cast_ofNat,div_self (by norm_num : (64:ℝ)≠0)] at hbase
  have hcard := relative_image_card_antitone D ref.a (2^m) p (E.image Prod.fst) 15 b hb15
  simp only [image_image,Function.comp_apply] at hcard
  have htop : (64:ℝ)/((2^b:ℕ):ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hp := Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hb
    norm_num only [show (2:ℕ)^6=64 by norm_num] at hp
    exact_mod_cast hp
  have hone := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by positivity : (0:ℝ)<64/((2^b:ℕ):ℝ)) htop (neg_nonpos.mpr extremalExponent_nonneg)
  have hpow : (1/512:ℝ)^(-extremalExponent) ≤ (512:ℝ)^3 := by
    rw [one_div,Real.inv_rpow (by norm_num),←Real.rpow_neg (by norm_num),neg_neg]
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      simpa only [Nat.cast_ofNat] using extremalExponent_le_three)
  have hpow' : (1/512:ℝ)^(-extremalExponent) ≤
      (512:ℝ)^3*(64/((2^b:ℕ):ℝ))^(-extremalExponent) := hpow.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (by positivity : (0:ℝ)≤512^3))
  have heps := hReferenceNative.1.2.1
  have hMC : 0 ≤ meshAngularConstant := by
    norm_num [meshAngularConstant,NativeSameSourceConditionalAngularUpper.conditionalConstant]
  calc
    _ ≤ ((E.image (fun z => relativeLabel D ref.a (2^m) p (2^15) z.1)).card:ℝ) := by exact_mod_cast hcard
    _ ≤ ((64:ℝ)^3*(5832*130^3)*meshAngularConstant*
        (source h ref.R ref.E1 ref.a m p).thickness^(-profile)*r^(-loss))*(1/512:ℝ)^(-extremalExponent) := hbase
    _ ≤ ((64:ℝ)^3*(5832*130^3)*meshAngularConstant*
        (source h ref.R ref.E1 ref.a m p).thickness^(-profile)*r^(-loss))*
        ((512:ℝ)^3*(64/((2^b:ℕ):ℝ))^(-extremalExponent)) :=
      mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ = _ := by ring

end NativeJointTopPhasePopulation
