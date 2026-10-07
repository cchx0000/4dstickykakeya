import Theorems.Thm_StickyKakeya4_native_raw_point_rank_four_ratio
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_raw_point_global_profiles
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries
import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativePhysicalReferenceData
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeRawPointSourceProfiles NativeRawPointGlobalProfiles NativeFullCoarseShadow
open NativeCoarsePointMultiplicity NativeBalancedConfiguration NativeMiddleWindowBalance
open NativeConditionalCoarseInterpolation NativeSquaredGrainQueries
open scoped BigOperators ENNReal

open NativeGenericReferenceData NativeRawPointRankFourRatio

/-- The actual mandatory global shadow relations, kept separately from the
conditioned relation fields in the generic first-reference record. -/
def HasPhysicalUniformities {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) : Prop :=
  ∀j,HasUniformFibers ref.E1 (coreRadix ref.original ref.R L)
      (physicalPair h ref.R ref.a ref.level (ref.schedule j).val) ∧
    HasUniformFibers ref.E1 (coreRadix ref.original ref.R L)
      (physicalPoint h ref.R ref.a ref.level (ref.schedule j).val)

lemma retained_scheduled_upper {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (Hphysical : HasPhysicalUniformities ref)
    (E2 : Finset (Fin n × Index)) (h21 : E2⊆ref.E1) (j : Fin (g+1)) :
    (NativeFiniteKakeyaCounts.multiplicity (fullSource h ref.R ref.a ref.level (ref.schedule j).val E2)).toReal ≤
      (coreRadix ref.original ref.R L:ℝ)^4*
        (D.thickness^(-seed)*(64/((2^(ref.schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent)) := by
  have hR1 : ∀z∈ref.E1,z.1∈ref.R := fun z hz => (mem_filter.mp (ref.core.1 hz)).2
  have hR2 : ∀z∈E2,z.1∈ref.R := fun z hz => hR1 z (h21 hz)
  obtain ⟨hPair,hPoint⟩ := Hphysical j
  have hh := subset_image_multiplicity ref.E1 E2 h21 (physicalPair h ref.R ref.a ref.level (ref.schedule j).val)
    (coreRadix ref.original ref.R L) hPair hPoint
  have hB := (ref.scales j).2.2.1
  rw [full_source_multiplicity_real h ref.R ref.a ref.level (ref.schedule j).val ref.E1 hR1] at hB
  rw [full_source_multiplicity_real h ref.R ref.a ref.level (ref.schedule j).val E2 hR2]
  exact hh.trans (mul_le_mul_of_nonneg_left hB (by positivity))

/-- Dimension-range raw ratio on the actual generic reference. Its global
physical relations are supplied by the same source producer, and all other
profiles are read from the unchanged reference record. -/
theorem squared_raw_ratio_of_middle {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (Hphysical : HasPhysicalUniformities ref)
    (E2 : Finset (Fin n × Index)) (h21 : E2⊆ref.E1) (hE2ne : E2.Nonempty)
    (j : Fin (g+1)) (hm6 : 6 ≤ (ref.schedule j).val)
    (hstop : (ref.schedule j).val ≤ ref.level/4) (hsmall : D.thickness ≤ 1/8)
    (hlo : NativeAllTwoScaleConfiguration.boundaryWindow tau*(ref.level:ℝ) ≤ (ref.schedule j).val)
    (G : ℕ) (hG : 0<G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(ref.E1.card:ℝ) ≤ (G:ℝ)*E2.card) :
    let m := (ref.schedule j).val
    let rho := 64/((2^m:ℕ):ℝ)
    lambda*D.thickness^(2*eta+2*zeta+seed+tau/16)*rho^4*(rawPointCount D E2 (phaseDepth m):ℝ) ≤
      pointRatioConstant*(factor ref.dimension (g+1) L:ℝ)*G*(coreRadix ref.original ref.R L:ℝ)^4*
        rho^NativeFixedCompactKakeyaExponent.extremalExponent*(rawPointCount D E2 m:ℝ) := by
  let a := ref.a
  let level := ref.level
  let original := ref.original
  let R := ref.R
  let E1 := ref.E1
  let schedule := ref.schedule
  let t := tau/16
  have Hbackbone := ref.backbone
  have Hcore := ref.core
  have hw : NativeAllTwoScaleConfiguration.boundaryWindow tau ≤ 1/2 :=
    (min_le_right _ _).trans (by norm_num : (1/8:ℝ) ≤ 1/2)
  have hwindow := squared_depth_in_middle (NativeAllTwoScaleConfiguration.boundaryWindow tau)
    hw (ref.schedule j).val ref.level hm6 hstop hlo
  have hb := (phaseDepth_bounds (ref.schedule j).val (ref.schedule j).val ref.level hm6 le_rfl hstop).2
  have HM := ref.middle _ hwindow.1 hwindow.2
  obtain ⟨horiginal,hdy,ha,_hRn,_hcard,_hshade,_hden,_hCW,Hpop⟩ := Hbackbone
  let m := (schedule j).val
  let b := phaseDepth m
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
  let F1 := factor ref.dimension (g+1) L
  let Q1 := coreRadix original R L
  let A : ℝ := (F1:ℝ)*G*43*2401*(Q1:ℝ)^4
  let B : ℝ := (2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)
  have hd := h.1.2.1
  have hr : 0<rho := by dsimp [rho]; positivity
  have hE1old : E1⊆incidences original := Hcore.1.trans (filter_subset _ _)
  have hE2ret : E2⊆NativeCoarseShadingCapacity.retained original R := h21.trans Hcore.1
  have hF1 : 0<F1 := by
    obtain ⟨z,hz⟩ := Hcore.2.1
    have hi : 0<(incidences original).card := card_pos.mpr ⟨z,hE1old hz⟩
    have hh := Hcore.2.2.1
    change (incidences original).card ≤ F1*E1.card at hh
    by_contra hf
    have he : F1=0 := Nat.eq_zero_of_not_pos hf
    rw [he,zero_mul] at hh
    omega
  have hQ1 : 0<Q1 := lt_of_lt_of_le (by norm_num : 0<4)
    (NativeSourceSizeBounds.radix_four_le (NativeOriginalParentDensityCore.retained original R).card L)
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by
    have hp := NativeOriginalPrunedMass.volumeConstant_pos
    dsimp [B]
    positivity
  have hm : m ≤ level := Nat.le_of_lt_succ (schedule j).isLt
  have hb6 : 6 ≤ b := by dsimp [b,phaseDepth,m,schedule]; omega
  have hmesh (d' : ℕ) : 32/((2^d':ℕ):ℝ)=(64/((2^d':ℕ):ℝ))/2 := by ring
  have hRet := two_stage_incidence_retention original E1 E2 F1 G lambda hlambda Hcore.2.2.1 hret
  have hMu := retained_scheduled_upper ref Hphysical E2 h21 j
  have hLow := raw_point_lower_with_retention h original horiginal ha R E2 hE2ret hE2ne level m hdy hm
    (fun p hp => (Hpop ⟨m,Nat.lt_succ_of_le hm⟩ p hp).2) lambda ((F1:ℝ)*G)
    ((Q1:ℝ)^4*(D.thickness^(-seed)*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent)))
    hlambda (by positivity) (by positivity) hRet hMu
  have hLow' := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (original_shading_mass_lower h original horiginal hsmall) hlambda)
      (by positivity)).trans hLow
  rw [hmesh m] at hLow'
  have hCoarse : (lambda*(D.thickness^(2*eta)/16))/
      (A*D.thickness^(-zeta)*(D.thickness^(-seed)*rho^(-NativeFixedCompactKakeyaExponent.extremalExponent))*(rho/2)^4) ≤
        (rawPointCount D E2 m:ℝ) := by
    simpa only [A,rho,mul_assoc,mul_comm,mul_left_comm] using hLow'
  have hFine1 := raw_point_upper h original horiginal ha R E1 Hcore.1 Hcore.2.1 level b hdy hb hb6
    (fun p hp => (Hpop ⟨b,Nat.lt_succ_of_le hb⟩ p hp).1)
    (D.thickness^t*(64/((2^b:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent))
    (by positivity) HM.1
  have hFine2 : (rawPointCount D E2 b:ℝ) ≤ (rawPointCount D E1 b:ℝ) := by
    exact_mod_cast raw_point_count_mono D E1 E2 h21 b
  have hFine := hFine2.trans hFine1
  rw [hmesh b,squared_scale_identity m hm6] at hFine
  have hFine' : (rawPointCount D E2 b:ℝ) ≤ (B*D.thickness^(-zeta))/
      ((D.thickness^t*(rho^2)^(-NativeFixedCompactKakeyaExponent.extremalExponent))*(rho^2/2)^4) := hFine
  have hh := squared_profile_cross hd hr hlambda hA hB.le hCoarse hFine'
  apply hh.trans_eq
  dsimp [A,B,F1,Q1,pointRatioConstant]
  ring


end NativePhysicalReferenceData
