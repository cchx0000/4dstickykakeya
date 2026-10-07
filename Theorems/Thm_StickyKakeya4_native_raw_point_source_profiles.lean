import Theorems.Thm_StickyKakeya4_native_raw_shadow_point_comparison
import Theorems.Thm_StickyKakeya4_native_same_source_coarse_selection
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeRawPointSourceProfiles
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeCoarseShadingCapacity NativeCoarsePointMultiplicity
open NativeSpatialAngularGeometry NativeRawShadowPointComparison NativeFullCoarseShadow
open NativeCoarseDyadicShading NativeCoarseDirectionThinning NativeCoarseShadingPruning
open NativeSameSourceCoarseSelection NativeMiddleWindowBalance
open scoped BigOperators ENNReal

/-- Literal occupied raw64/2^m cubes of the original cell centers. -/
def rawPointCount {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (m : ℕ) : ℕ :=
  (E.image (fun z => spatialLabel D (2^m) z.2)).card

/-- Actual occupied point labels of the full shadow on the fixed original R. -/
def shadowPointCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) : ℕ :=
  (E.image (pointLabel D a (2^m) (block level m) (representative h R a (2^m)))).card

/-- Exact mass equals multiplicity times actual occupied cell count times
cell volume. The shadow representatives and original incidence set stay fixed. -/
lemma full_mass_eq_multiplicity_point_volume {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (E : Finset (Fin n × Index)) (hE : E.Nonempty) (hR : ∀z∈E,z.1∈R)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    (wzTotalShadingVolume (fullSource h R a level m E)).toReal =
      (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal*
        (shadowPointCount h R E a level m:ℝ)*(32/((2^m:ℕ):ℝ))^4 := by
  let rep := representative h R a (2^m)
  let C := NativeCoarseShadingCapacity.coarse D a (2^m) (block level m) rep E
  have hmass := coarse_shading_real h.1.2.1 a (2^m) (block level m) (block_pos level m)
    rep E (R.image (parentLabel D a (2^m))) (fun z hz => mem_image_of_mem _ (hR z hz))
  rw [block_mesh hdy hm] at hmass
  have hmass' : (wzTotalShadingVolume (fullSource h R a level m E)).toReal=
      (C.card:ℝ)*(32/((2^m:ℕ):ℝ))^4 := by
    rw [full_mass_real]
    exact hmass
  have hs : (C.image Prod.snd).card=shadowPointCount h R E a level m := by
    simp only [C,NativeCoarseShadingCapacity.coarse,image_image,Function.comp_def,
      NativeCoarseShadingCapacity.label,shadowPointCount,rep]
    rfl
  have hp : (0:ℝ)<shadowPointCount h R E a level m := by
    exact_mod_cast card_pos.mpr (hE.image _)
  rw [hmass',full_source_multiplicity_real h R a level m E hR]
  change (C.card:ℝ)*(32/((2^m:ℕ):ℝ))^4=
    ((C.card:ℝ)/(C.image Prod.snd).card)*(shadowPointCount h R E a level m:ℝ)*_
  rw [hs,div_mul_cancel₀ _ hp.ne']

/-- Global raw point upper counts follow from the ORIGINAL AD lower
population and the existing full-shadow multiplicity lower bound. -/
theorem raw_point_upper {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (hEn : E.Nonempty) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m)
    (H : ∀p,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ))
    (L : ℝ) (hL : 0<L)
    (hlower : L ≤ (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal) :
    (rawPointCount D E m:ℝ)  ≤ 
      ((2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)*D.thickness^(-zeta))/
        (L*(32/((2^m:ℕ):ℝ))^4) := by
  have hER : ∀z∈E,z.1∈R := fun z hz => ((retained_spec original R z).mp (hE hz)).1
  have hEO : E⊆incidences original := hE.trans (filter_subset _ _)
  have hraw : (rawPointCount D E m:ℝ)  ≤  (2051:ℝ)^4*shadowPointCount h R E a level m := by
    exact_mod_cast (same_R_point_image_card_comparison h original horiginal ha R E hEO hER level m hdy hm).2
  have hmass := full_mass_eq_multiplicity_point_volume h R a E hEn hER level m hdy hm
  have hupper := full_mass_upper h original horiginal ha R level m hdy hm h6 E
    (fun z hz => ((retained_spec original R z).mp (hE hz)).2) H
  apply (le_div_iff₀ (show 0<L*(32/((2^m:ℕ):ℝ))^4 by positivity)).mpr
  calc
    _  ≤  ((2051:ℝ)^4*(shadowPointCount h R E a level m:ℝ))*
        (L*(32/((2^m:ℕ):ℝ))^4) := mul_le_mul_of_nonneg_right hraw (by positivity)
    _ = (2051:ℝ)^4*(L*(shadowPointCount h R E a level m:ℝ)*(32/((2^m:ℕ):ℝ))^4) := by ring
    _  ≤  (2051:ℝ)^4*((NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal*
        (shadowPointCount h R E a level m:ℝ)*(32/((2^m:ℕ):ℝ))^4) := by gcongr
    _ = (2051:ℝ)^4*(wzTotalShadingVolume (fullSource h R a level m E)).toReal := by rw [hmass]
    _  ≤  (2051:ℝ)^4*((373248*64^3*NativeOriginalPrunedMass.volumeConstant)*D.thickness^(-zeta)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = _ := by ring

/-- The literal global incidence retention loss is preserved in the raw
point lower bound. Only original AD populations and actual shadow upper
multiplicity are used; there is no lower-density assumption on raw points. -/
theorem raw_point_lower_with_retention {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (hEn : E.Nonempty) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (H : ∀p,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ)  ≤ 
        D.thickness^(-zeta)*((1/((2^m:ℕ):ℝ))/D.thickness)^3)
    (lambda F U : ℝ) (_hlambda : 0 ≤ lambda) (hF : 0<F) (hU : 0<U)
    (hret : lambda*((incidences original).card:ℝ)  ≤  F*E.card)
    (hupper : (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal ≤ U) :
    (lambda*(wzTotalShadingVolume D).toReal)/
      (F*43*D.thickness^(-zeta)*U*2401*(32/((2^m:ℕ):ℝ))^4)  ≤ 
        (rawPointCount D E m:ℝ) := by
  have hER : ∀z∈E,z.1∈R := fun z hz => ((retained_spec original R z).mp (hE hz)).1
  have hEO : E⊆incidences original := hE.trans (filter_subset _ _)
  have hshadow : (shadowPointCount h R E a level m:ℝ)  ≤  2401*(rawPointCount D E m:ℝ) := by
    exact_mod_cast (same_R_point_image_card_comparison h original horiginal ha R E hEO hER level m hdy hm).1
  have hmass := full_mass_eq_multiplicity_point_volume h R a E hEn hER level m hdy hm
  have hcoarse := selected_dyadic_shading_transfer h original horiginal ha R E hE level m hdy hm H
    (representative h R a (2^m))
  rw [←full_mass_real] at hcoarse
  have hsource : (wzTotalShadingVolume D).toReal=((incidences original).card:ℝ)*(D.thickness/2)^4 := by
    rw [total_shading_eq_incidence_volume D (half_pos h.1.2.1) original horiginal]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (half_pos h.1.2.1).le]
  apply (div_le_iff₀ (show 0<F*43*D.thickness^(-zeta)*U*2401*(32/((2^m:ℕ):ℝ))^4 by
    have hd := h.1.2.1
    positivity)).mpr
  calc
    _ = (lambda*((incidences original).card:ℝ))*(D.thickness/2)^4 := by rw [hsource]; ring
    _  ≤  (F*(E.card:ℝ))*(D.thickness/2)^4 := mul_le_mul_of_nonneg_right hret (by positivity)
    _ = F*((E.card:ℝ)*(D.thickness/2)^4) := by ring
    _  ≤  F*(43*D.thickness^(-zeta)*(wzTotalShadingVolume (fullSource h R a level m E)).toReal) :=
      mul_le_mul_of_nonneg_left hcoarse hF.le
    _ = F*43*D.thickness^(-zeta)*
        ((NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E)).toReal*
          (shadowPointCount h R E a level m:ℝ)*(32/((2^m:ℕ):ℝ))^4) := by rw [hmass]; ring
    _  ≤  F*43*D.thickness^(-zeta)*(U*(2401*(rawPointCount D E m:ℝ))*(32/((2^m:ℕ):ℝ))^4) := by
      have hd := h.1.2.1
      gcongr
    _ = _ := by ring

/-- Both global raw point profiles at an arbitrary middle depth are actual
consequences of the original E1 fields. Apply separately at m and2m-6 for
rho and rho squared when both lie in the existing middle window. -/
theorem middle_raw_point_profile {n : ℕ} {D : FiniteScaleSource n} {eta a zeta tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (hEn : E.Nonempty) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (F : ℕ) (hF : 0<F)
    (hret : (incidences original).card ≤ F*E.card)
    (H : ∀p,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3  ≤ 
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ) ∧
      ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ)  ≤ 
        D.thickness^(-zeta)*((1/((2^m:ℕ):ℝ))/D.thickness)^3)
    (HM : HasMiddleScale h R E a level m tau) :
    let rho := 64/((2^m:ℕ):ℝ)
    (wzTotalShadingVolume D).toReal/
      ((F:ℝ)*43*D.thickness^(-zeta)*(D.thickness^(-tau)*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent))*
        2401*(rho/2)^4)  ≤  (rawPointCount D E m:ℝ) ∧
    (rawPointCount D E m:ℝ)  ≤ 
      ((2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)*D.thickness^(-zeta))/
        ((D.thickness^tau*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent))*(rho/2)^4) := by
  have hd := h.1.2.1
  have hmsh : (64/((2^m:ℕ):ℝ))/2=32/((2^m:ℕ):ℝ) := by ring
  dsimp only
  rw [hmsh]
  constructor
  · have hh := raw_point_lower_with_retention h original horiginal ha R E hE hEn level m hdy hm
      (fun p hp => (H p hp).2) 1 F
      (D.thickness^(-tau)*(64/((2^m:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent))
      (by norm_num) (by exact_mod_cast hF) (by positivity) (by simpa only [one_mul] using (show ((incidences original).card:ℝ) ≤ (F:ℝ)*E.card by exact_mod_cast hret)) HM.2.1
    simpa only [one_mul] using hh
  · exact raw_point_upper h original horiginal ha R E hE hEn level m hdy hm h6
      (fun p hp => (H p hp).1) _ (by positivity) HM.1

/-- Composition of the original E1 loss with the literal E2 retention.
The rank-dependent lambda is retained explicitly and never silently absorbed. -/
lemma two_stage_incidence_retention {n : ℕ} (original : Fin n → Finset Index)
    (E1 E2 : Finset (Fin n × Index)) (F1 G : ℕ) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hfirst : (incidences original).card ≤ F1*E1.card)
    (hsecond : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card) :
    lambda*((incidences original).card:ℝ) ≤ ((F1:ℝ)*G)*E2.card := by
  have hfirstR : ((incidences original).card:ℝ) ≤ (F1:ℝ)*E1.card := by exact_mod_cast hfirst
  calc
    _  ≤  lambda*((F1:ℝ)*E1.card) := mul_le_mul_of_nonneg_left hfirstR hlambda
    _ = (F1:ℝ)*(lambda*(E1.card:ℝ)) := by ring
    _  ≤  (F1:ℝ)*((G:ℝ)*E2.card) := mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg _)
    _ = _ := by ring

end NativeRawPointSourceProfiles
