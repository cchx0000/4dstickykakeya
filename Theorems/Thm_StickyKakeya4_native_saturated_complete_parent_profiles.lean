import Theorems.Thm_StickyKakeya4_native_saturated_population_parent_profiles
import Theorems.Thm_StickyKakeya4_native_source_parent_population_profile

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeSaturatedCompleteParentProfiles
open NativeSharpMixedGrainCore NativeSaturatedMixedGrainCore
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSquaredGrainQueries NativeActualProjectedGrainCount
open NativeQueriedVertexWeights NativeOriginalPacketReference NativeCompatibleNodeDirections
open NativeDirectionRankDichotomy NativeActualGrainHistory NativeHistoryGrainCount NativeHistoryGrainCleanup
open NativeParentGrainIncidenceCleanup NativeSourceParentGrainCleanup NativeSaturatedMixedGrainCore
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeMiddleWindowBalance NativeFixedCompactKakeyaExponent NativeFullCoarseShadow
open NativeRetainedFinePairDensity RichDirectionalLayers WeightedRichDirectionalLayers
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeActivePhasePopulation
open NativeCombinedParentProfiles NativeLocalPairFibers
open NativeSaturatedMixedGrainCore
open scoped BigOperators

open NativeSaturatedPopulationParentProfiles NativePhaseHeightPopulation

def HasSaturatedCompleteParentProfiles {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (plane : Index → Submodule ℝ E4) (points : Finset Index) (q : ℝ) (ell Q2 F1 G Lgrain : ℕ)
    (lambda zeta tau seed c2 : ℝ) (depths : Fin K → ℕ) : Prop :=
  let W := mass points (pointWeight E2)
  let theta := lambda*(W:ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let retain := mu/rowConstant
  0 < theta ∧ 0 < mu ∧ 0 < retain ∧
    ∃H⊆cutEdges E2 points,H.Nonempty ∧ W ≤ 2*H.card ∧
      ∃p∈R.image (parentLabel D a (2^m)),(parentEdges D a (2^m) H p).Nonempty ∧
        mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*(parentEdges D a (2^m) H p).card ∧
        (∀I⊆retained original R,retain*(parentEdges D a (2^m) I p).card ≤ (parentEdges D a (2^m) H p).card) ∧
        (∀x∈parentEdges D a (2^m) H p,
          lambda*D.thickness^(2*eta+3*zeta+7*tau)*(W:ℝ)*Lgrain <
            parentGrainConstant*transverseCost q ell*(Q2:ℝ)^2*(F1:ℝ)*G*E2.card*
              (mixedVertices D a m (phaseDepth m) plane ell (parentEdges D a (2^m) H p)
                (mixedLabel D a m plane ell x)).card) ∧
        HasMixedIncidenceThreshold D a m plane ell E2 points (parentEdges D a (2^m) H p) ∧
        HasPointSaturation (parentEdges D a (2^m) E2 p) (parentEdges D a (2^m) H p) ∧
        (∀u,HasParentProfiles h R E1 E2 a level m (depths u) p retain lambda tau seed c2) ∧
        (∀u,
          let relative := (64/((2^(depths u):ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
          let M := (NativeFiniteKakeyaCounts.multiplicity
            (fullSource h R a level (depths u) (parentEdges D a (2^m) H p))).toReal
          retain*D.thickness^(tau+seed/8+10*min (boundaryWindow tau) ((tau/16)/1000))*relative^(-extremalExponent) ≤ M ∧
            M ≤ D.thickness^(-(3*tau))*relative^(-extremalExponent)) ∧
        mu ≤ (43904*(64/((2^m:ℕ):ℝ)))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ∧
        (64/((2^m:ℕ):ℝ))*(heightLabels D a (64/((2^m:ℕ):ℝ)) (parentEdges D a (2^m) E2 p)).card ≤ 10 ∧
        ∀f : ℕ,m ≤ f → f ≤ level →
          (mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            rowConstant*(activePhases D a f (parentEdges D a (2^m) E2 p)).card ∧
          ((activePhases D a f (parentEdges D a (2^m) E2 p)).card:ℝ) ≤
            D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3) ∧
          mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
            (43904*(64/((2^m:ℕ):ℝ)))*
              (phaseHeightLabels D a (64/((2^m:ℕ):ℝ)) f (parentEdges D a (2^m) E2 p)).card

/-- Complete the readbacks on the ALREADY selected p. No second parent
averaging or selection occurs. All original K/H/profile witnesses remain. -/
theorem complete_saturated_selected_parent_profiles {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (plane : Index → Submodule ℝ E4) (points : Finset Index) (q : ℝ) (ell Q2 F1 G Lgrain : ℕ)
    (lambda zeta tau seed c2 : ℝ) (depths : Fin K → ℕ)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (h2R : E2⊆retained original R) (hm6 : 6 ≤ m) (hm : m ≤ level)
    (H : HasSaturatedPopulationParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths) :
    HasSaturatedCompleteParentProfiles h original R E1 E2 a level m plane points q ell Q2 F1 G Lgrain
      lambda zeta tau seed c2 depths := by
  obtain ⟨htheta,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hmin,hsat,hprofiles,hcleaned⟩ := H
  let theta := lambda*(mass points (pointWeight E2):ℝ)/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ))
  let mu := theta*D.thickness^eta
  let rho := 64/((2^m:ℕ):ℝ)
  have hE2 : E⊆E2 := hEK.trans (cutEdges_subset E2 points)
  have hEp2 : parentEdges D a (2^m) E p⊆parentEdges D a (2^m) E2 p := filter_subset_filter _ hE2
  have hFp : (parentEdges D a (2^m) E2 p).Nonempty := hEpn.mono hEp2
  have hFR : parentEdges D a (2^m) E2 p⊆retained original R := (filter_subset _ _).trans h2R
  have hparent : ∀z∈parentEdges D a (2^m) E2 p,parentLabel D a (2^m) z.1=p :=
    fun _z hz => (mem_filter.mp hz).2
  have hpopF : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E2 p).card :=
    hpop.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hEp2)) h.1.2.1.le)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm6
    norm_num only [show (2:ℕ)^6=64 by norm_num] at hh
    exact_mod_cast hh
  refine ⟨htheta,hmu,hretain,E,hEK,hEn,hhalf,p,hp,hEpn,hpop,href,hgrain,hmin,hsat,hprofiles,hcleaned,?_,?_,?_⟩
  · exact parent_height_population h original R level Hbackbone m hm
      (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hpopF
  · apply height_population_upper h original Hbackbone.1 Hbackbone.2.2.1 rho hrho hrho1
    exact hFR.trans (filter_subset _ _)
  · intro f hmf hfl
    exact ⟨active_phase_population h original R level Hbackbone m f hmf hfl
        (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hmu.le hpopF,
      phase_height_population h original R level Hbackbone m f hmf hfl
        (parentEdges D a (2^m) E2 p) hFR hFp p hparent mu hmu.le hpopF⟩

end NativeSaturatedCompleteParentProfiles
