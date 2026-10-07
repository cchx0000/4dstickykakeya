/- UNVERIFIED current-source phase-cover reader. It consumes the already
chosen upper engine and the same E1 reference; it chooses no new menu. -/
import Theorems.Thm_StickyKakeya4_native_actual_angular_parent_count
import Theorems.Thm_StickyKakeya4_native_source_coherence_engine
import Theorems.Thm_StickyKakeya4_native_angular_dyadic_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeJointCellPhasePopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration NativeConditionalReferenceMenu
open NativeSourceCoherenceEngine NativePaidMeshAngularUpper NativeFixedCompactKakeyaExponent
open NativeLocalParentSource NativeOriginalParentDensityCore NativeMiddleGrainParentBudget
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeAngularDyadicInterpolation
open NativeActualAngularParentCount NativeRelativeParentLabels

/-- Exact parent count in one actual prepared cell. The fixed64^3 term
refines angular width64*tau to widthtau. The separate5832*130^3 reference
cap then counts phase parents at slope mesh tau/64; neither cost is omitted. -/
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
    (depth : ℕ) (hdepth : 6 ≤ depth) (hdepthm : depth ≤ m+6)
    (r power : ℝ) (hr : 0 < r) (hrscale : r ≤ D.thickness^power) (hpower : amin ≤ power)
    (hdelta : 64*D.thickness ≤ r^2) (hMiddle : 3072*r ≤ (64/((2^m:ℕ):ℝ))^2)
    (p : Parent) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (hParent : ∀ z ∈ E, parentLabel D ref.a (2^m) z.1 = p)
    (cell : Index) (hCell : ∀ z ∈ E, physicalCell D ref.a (2^m) (2^depth) p z.2 = cell)
    (localEta profile : ℝ)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h ref.R ref.E1 ref.a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h ref.R ref.E1 ref.a m p).thickness ^ profile ≤ D.thickness ^ zeta)
    (hmb : m + (depth+9) ≤ ref.level) :
    ((E.image (fun z => relativeLabel D ref.a (2^m) p (2^(depth+9)) z.1)).card : ℝ) ≤
      ((64 : ℝ)^3 * (5832*130^3) * meshAngularConstant *
        (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) * r^(-loss)) *
        ((64/((2^depth:ℕ):ℝ))/512)^(-extremalExponent) := by
  let I := E.image Prod.fst
  have hI : I ⊆ parentLabels D ref.R ref.a (2^m) p := by
    intro j hj
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hj
    have hR := ((retained_spec ref.original ref.R z).mp (ref.core.1 (hE hz))).1
    exact (mem_parentLabels D ref.R ref.a (2^m) p z.1).mpr ⟨hR, hParent z hz⟩
  have hphase := same_original_parent_count h ref.original ref.R ref.level ref.backbone ref.E1
    m (depth-3) (by omega) p hReferenceNative hbudget I hI
  have hpd : depth-3+12 = depth+9 := by omega
  have had : depth-3+9 = depth+6 := by omega
  rw [hpd, had] at hphase
  simp only [I, image_image, Function.comp_apply] at hphase
  have hdesc := bottom_angular_interpolation D (2^m) p E
    (m:=depth) (s:=depth+6) (by omega) (by omega)
  have H := Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseed hsmall
    ref Hcaller i hstop
  rw [← hm] at H
  have hupper := (H depth hdepth hdepthm r power hr hrscale hpower hdelta hMiddle
    p E hE hParent cell hCell).1
  have hwide : ((64/((2^depth:ℕ):ℝ)))^(-extremalExponent) ≤
      ((64/((2^depth:ℕ):ℝ))/512)^(-extremalExponent) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
      (show (64/((2^depth:ℕ):ℝ))/512 ≤ 64/((2^depth:ℕ):ℝ) by
        have hp : (0:ℝ) < 64/((2^depth:ℕ):ℝ) := by positivity
        linarith only [hp])
      (neg_nonpos.mpr extremalExponent_nonneg)
  have hMesh : 0 ≤ meshAngularConstant := by
    norm_num [meshAngularConstant, NativeSameSourceConditionalAngularUpper.conditionalConstant]
  have heps := hReferenceNative.1.2.1
  calc
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        (E.image (fun z => angularCell D (2^m) (2^(depth+6)) p z.1)).card := hphase
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        ((64 : ℝ)^3 * (E.image (fun z => angularCell D (2^m) (2^depth) p z.1)).card) :=
      mul_le_mul_of_nonneg_left hdesc (by positivity)
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        ((64 : ℝ)^3 * (meshAngularConstant * r^(-loss) *
          (64/((2^depth:ℕ):ℝ))^(-extremalExponent))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper (by norm_num)) (by positivity)
    _ ≤ (5832*130^3 : ℝ) * (source h ref.R ref.E1 ref.a m p).thickness ^ (-profile) *
        ((64 : ℝ)^3 * (meshAngularConstant * r^(-loss) *
          ((64/((2^depth:ℕ):ℝ))/512)^(-extremalExponent))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwide (mul_nonneg hMesh (by positivity))) (by norm_num)) (by positivity)
    _ = _ := by ring

end NativeJointCellPhasePopulation
