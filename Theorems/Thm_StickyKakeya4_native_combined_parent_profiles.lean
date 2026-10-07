import Theorems.Thm_StickyKakeya4_native_window_paid_parent_lower
import Theorems.Thm_StickyKakeya4_native_reference_hereditary_upper
import Theorems.Thm_StickyKakeya4_native_anisotropic_global_source_bridge
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeCombinedParentProfiles
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeCoarseShadingUniformity
open NativeCoarseDirectionThinning NativeConditionedPairMenu NativeAllTwoScaleConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeFullCoarseShadow
open NativeFixedCompactKakeyaExponent NativeLocalPairFibers NativeSquaredGrainQueries
open NativeAnisotropicGlobalSourceBridge NativeCubicalIncidenceCounts

/-- All profiles refer to the same global D/R source and the same parent p. -/
def HasParentProfiles {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (p : Parent)
    (theta lambda tau seed c2 : ℝ) : Prop :=
  let relative := (64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
  let M1 := (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level f (parentEdges D a (2^m) E1 p))).toReal
  let M2 := (NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level f (parentEdges D a (2^m) E2 p))).toReal
  let C := NativeIncidenceMultiplicityTower.multiplicity ((parentEdges D a (2^m) E2 p).image (columnPair D a m f p))
  let eps := lambda*D.thickness^(seed/8+3*c2)
  let lower := theta*D.thickness^(tau+seed/8+10*min (boundaryWindow tau) ((tau/16)/1000))*relative^(-extremalExponent)
  let upper := D.thickness^(-(3*tau))*relative^(-extremalExponent)
  D.thickness^tau*relative^(-extremalExponent) ≤ M1 ∧ M1 ≤ D.thickness^(-tau)*relative^(-extremalExponent) ∧
    lower ≤ M2 ∧ M2 ≤ upper ∧
    eps/comparisonCost*M2 ≤ C ∧ C ≤ comparisonCost/eps*M2 ∧
    eps/comparisonCost*lower ≤ C ∧ C ≤ comparisonCost/eps*upper

lemma horizontal_window (m f : ℕ) (hm6 : 6 ≤ m) (hf : f ≤ phaseDepth m) :
    (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ) := by
  rw [←squared_scale_identity m hm6]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hf

/-- E1 lower/upper, paid E2 lower, hereditary E2 upper, and the actual
anisotropic reference comparison are all derived from original source fields. -/
theorem source_parent_profiles {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau c2 theta lambda : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (F2 G Q2 : ℕ) (hG : 0 < G) (hQ2 : 0 < Q2) (hGF : G ≤ F2) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
      (16384*(((factor d (g+1) L:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card)
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (m f : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m)
    (hhalf : (f:ℝ) ≤ (level:ℝ)/2)
    (HF : HasUniformFibers E2 Q2 (fixedPair D a level f f (representative h R a (2^f))))
    (HC : HasUniformFibers E2 Q2 (fixedPair D a level f m (representative h R a (2^f))))
    (p : Parent) (hp : (parentEdges D a (2^m) E2 p).Nonempty)
    (htheta : 0 < theta)
    (hret : theta*((parentEdges D a (2^m) E1 p).card:ℝ) ≤ (parentEdges D a (2^m) E2 p).card) :
    HasParentProfiles h R E1 E2 a level m f p theta lambda tau seed c2 := by
  have hfL : f ≤ level := by exact_mod_cast (show (f:ℝ) ≤ level by have hh := Nat.cast_nonneg level (α:=ℝ); linarith)
  have hE1 : E1⊆incidences original := Hcore.1.trans (filter_subset _ _)
  have hER1 : ∀z∈E1,z.1∈R := fun z hz => (mem_filter.mp (Hcore.1 hz)).2
  have hF1 : 0 < factor d (g+1) L := by dsimp [factor,NativeLocalPairUniformCore.retentionCost]; positivity
  have hQ1 : 1 ≤ coreRadix original R L := (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  have hp1 : (parentEdges D a (2^m) E1 p).Nonempty := hp.mono (filter_subset_filter _ h21)
  have href := hreference m f hmf hfL p hp1
  have hlo := NativeWindowPaidParentLower.master_parent_power_lower h heta htau original Hbackbone.1
    Hbackbone.2.2.1 R E1 E2 hE1 hER1 h21 level m f Hbackbone.2.1 hmf hhalf g hg hgrid hgl
    (coreRadix original R L) (factor d (g+1) L) hF1 hcost
    (by simpa only [hschedule] using hconditioned) hreference p hp1 htheta hret
  have hhi := NativeReferenceHereditaryUpper.from_master_reference h original R E1 schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference E2 h21 m f hmf hfL p
  have haniso := queried_global_source_comparison h original Hbackbone.1 Hbackbone.2.2.1 R E2
    (h21.trans hE1) (fun z hz => hER1 z (h21 hz)) (factor d (g+1) L) F2 G (coreRadix original R L) Q2
    hF1 hG hQ2 hQ1 hGF heta Hbackbone.2.1 hlambda hRich hcost hcost2
    f m hmf hfL hm6 (horizontal_window m f hm6 hfb) HF HC p hp
  have heps : 0 < lambda*D.thickness^(seed/8+3*c2) := by have hd := h.1.2.1; positivity
  have hC := comparisonCost_pos
  refine ⟨href.1,href.2,hlo,hhi,haniso.1,haniso.2,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hlo (by positivity)).trans haniso.1
  · exact haniso.2.trans (mul_le_mul_of_nonneg_left hhi (by positivity))

end NativeCombinedParentProfiles
