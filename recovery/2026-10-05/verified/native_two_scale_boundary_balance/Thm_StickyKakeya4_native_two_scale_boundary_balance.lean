import Theorems.Thm_StickyKakeya4_native_two_axis_conditional_transfer
import Theorems.Thm_StickyKakeya4_native_two_scale_boundary_window
import Theorems.Thm_StickyKakeya4_native_conditional_parent_boundary

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeTwoScaleBoundaryBalance
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeIncidenceMultiplicityTower
open NativeConditionalCoarseInterpolation NativeConditionalParentBoundary
open NativeTwoScaleConfiguration NativeTwoAxisPowerInterpolation NativeTwoAxisConditionalTransfer
open NativeFixedCompactKakeyaExponent NativeTwoScaleBoundaryWindow

lemma depthPower_mono {kappa : ℝ} (hk : 0 ≤ kappa) {m d b f : ℕ}
    (hmd : m ≤ d) (hbf : b ≤ f) : depthPower kappa d b ≤ depthPower kappa m f := by
  unfold depthPower
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hmdR : (m:ℝ) ≤ d := by exact_mod_cast hmd
  have hbfR : (b:ℝ) ≤ f := by exact_mod_cast hbf
  nlinarith

/-- Extending one actual middle pair to the two boundaries costs six outer
phase powers and ten inner physical powers. The same full global-R shadow
and the exact original parent subsets occur throughout. -/
theorem boundary_pair_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a loss s : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences original)
    (hER : ∀z∈E,z.1∈R) (level m d b f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hmd : m ≤ d) (hdb : d ≤ b) (hbf : b ≤ f) (hfl : f ≤ level) (hs : 0 ≤ s)
    (hgapD : ((d-m:ℕ):ℝ) ≤ s*level) (hgapF : ((f-b:ℕ):ℝ) ≤ s*level)
    (hconstant : (729:ℝ) ≤ D.thickness^(-loss))
    (HM : HasConditionalTwoScale h R E a level d b loss) :
    HasConditionalTwoScale h R E a level m f (2*loss+16*s) := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  let rD := ((2^(d-m):ℕ):ℝ)
  let rF := ((2^(f-b):ℕ):ℝ)
  have hrD : 0 ≤ rD := by dsimp [rD]; positivity
  have hrF : 0 ≤ rF := by dsimp [rF]; positivity
  have hratioD : rD ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapD
  have hratioF : rF ≤ D.thickness^(-s) := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgapF
  have hpowD := nat_power_cost hd hrD hratioD 6
  have hpowF := nat_power_cost hd hrF hratioF 10
  have hPower := depthPower_mono extremalExponent_nonneg hmd hbf
  intro p hp
  change D.thickness^(2*loss+16*s)*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤ _ ∧ _
  rw [conditional_full_eq_image h R E a level m f hER p,←depthPower_eq_relative]
  let Ep := parentEdges D a (2^m) E p
  have hEp : Ep⊆NativeCubicalIncidenceCounts.incidences original := (filter_subset _ _).trans hE
  have hEpR : ∀z∈Ep,z.1∈R := fun z hz => hER z (mem_filter.mp hz).1
  have hP := (depthPower_pos extremalExponent m f).le
  constructor
  · have hLower := coarser_outer_parent_lower h R E a level m d b hmd hdb
      (D.thickness^loss*depthPower extremalExponent d b)
      (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le)
      (fun q hq => (scheduled_image_bounds h R E a level d b loss hER HM q hq).1) p hp
    have hForward := NativeCoarseScaleInterpolation.actual_multiplicity_le h original horiginal ha
      R Ep hEp hEpR level b f hdy hbf hfl
    have hh := lower_transfer hd hrF hratioF hconstant
      (NativeSameSourceMultiplicityBalance.multiplicity_nonneg _)
      (lower_menu_power hdy extremalExponent_nonneg hmd hbf hgapD hgapF) hLower hForward
    have hkS := mul_le_mul_of_nonneg_left extremalExponent_le_three hs
    have hmargin : 2*loss+s*(4+2*extremalExponent) ≤ 2*loss+16*s := by nlinarith
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hmargin) hP).trans hh
  · have hUpper := coarser_outer_parent_upper h R E a level m d b hmd hdb
      (D.thickness^(-loss)*depthPower extremalExponent d b)
      (mul_nonneg (Real.rpow_pos_of_pos hd _).le (depthPower_pos _ _ _).le)
      (fun q hq => (scheduled_image_bounds h R E a level d b loss hER HM q hq).2) p
    have hReverse := NativeCoarseScaleReverse.actual_multiplicity_le h original horiginal ha
      R Ep hEp hEpR level b f hdy hbf hfl
    have hCost : (729:ℝ)*rF^10*rD^6 ≤ D.thickness^(-(loss+16*s)) := by
      calc
        _ ≤ (D.thickness^(-loss)*D.thickness^(-s*(10:ℝ)))*D.thickness^(-s*(6:ℝ)) :=
          mul_le_mul (mul_le_mul hconstant hpowF (pow_nonneg hrF 10)
            (Real.rpow_pos_of_pos hd _).le) hpowD (pow_nonneg hrD 6) (by positivity)
        _ = _ := by rw [←Real.rpow_add hd,←Real.rpow_add hd]; congr 1; ring
    calc
      _ ≤ 729*rF^10*multiplicity (Ep.image (physicalPair h R a level b)) := hReverse
      _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower extremalExponent d b)) :=
        mul_le_mul_of_nonneg_left hUpper (by positivity)
      _ ≤ 729*rF^10*(rD^6*(D.thickness^(-loss)*depthPower extremalExponent m f)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPower (by positivity))
            (pow_nonneg hrD 6)) (by positivity)
      _ = (729*rF^10*rD^6)*(D.thickness^(-loss)*depthPower extremalExponent m f) := by ring
      _ ≤ D.thickness^(-(loss+16*s))*(D.thickness^(-loss)*depthPower extremalExponent m f) :=
        mul_le_mul_of_nonneg_right hCost (mul_nonneg (Real.rpow_pos_of_pos hd _).le hP)
      _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring

/-- Every original dyadic pair is controlled by the same middle witness.
Boundary clamping and the diagonal bound are deterministic operations on E. -/
theorem all_pair_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences original)
    (hER : ∀z∈E,z.1∈R) (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (w loss target : ℝ) (hw : 0 < w) (hwsmall : w ≤ 1/8) (hlarge : 4 ≤ w*(level:ℝ))
    (hconstant : (729:ℝ) ≤ D.thickness^(-loss)) (hdiag : 48*w ≤ target)
    (hmargin : 2*loss+32*w ≤ target)
    (HM : ∀d b : ℕ,d ≤ b → w*(level:ℝ) ≤ d → (b:ℝ) ≤ (1-w)*(level:ℝ) →
      HasConditionalTwoScale h R E a level d b loss)
    (m f : ℕ) (hmf : m ≤ f) (hfl : f ≤ level) :
    HasConditionalTwoScale h R E a level m f target := by
  by_cases hNear : ((f-m:ℕ):ℝ) ≤ 8*w*(level:ℝ)
  · intro p hp
    change D.thickness^target*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤ _ ∧ _
    rw [conditional_full_eq_image h R E a level m f hER p,←depthPower_eq_relative]
    have hh := NativeConditionalCoarseDiagonal.actual_short_gap_power h R E a level m f hmf hdy
      (8*w) extremalExponent (by positivity) extremalExponent_nonneg
      (extremalExponent_le_three.trans (by norm_num)) hNear p hp
    rw [←depthPower_eq_nat hmf] at hh
    have he : 6*(8*w) ≤ target := by linarith
    have hP := (depthPower_pos extremalExponent m f).le
    exact ⟨(mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 he) hP).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 (by linarith : -target ≤ -6*(8*w))) hP)⟩
  · obtain ⟨d,b,hmd,hdb,hbf,hdlo,hbhi,hgapD,hgapF⟩ :=
      exists_clamped_depths w hw hwsmall level m f hlarge hmf hfl (lt_of_not_ge hNear)
    have hh := boundary_pair_bounds h original horiginal ha R E hE hER level m d b f hdy
      hmd hdb hbf hfl (by positivity : (0:ℝ) ≤ 2*w) hgapD hgapF hconstant (HM d b hdb hdlo hbhi)
    intro p hp
    obtain ⟨hlo,hup⟩ := hh p hp
    have he : 2*loss+16*(2*w) ≤ target := by linarith
    have hP : 0 ≤ ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) := by positivity
    exact ⟨(mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 he) hP).trans hlo,
      hup.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1 (neg_le_neg he)) hP)⟩

end NativeTwoScaleBoundaryBalance
