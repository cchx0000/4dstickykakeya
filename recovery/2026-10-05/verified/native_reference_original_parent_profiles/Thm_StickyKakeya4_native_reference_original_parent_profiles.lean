import Theorems.Thm_StickyKakeya4_native_full_depth_extension
import Theorems.Thm_StickyKakeya4_native_actual_mesoscopic_rank_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeReferenceOriginalParentProfiles
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeMiddleWindowBalance
open NativeFullDepthExtension NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration
open NativeFixedCompactKakeyaExponent NativeLocalMenuInterpolation

/-- The existing first-refinement cost already pays the absolute constant
needed for endpoint extension. No further small-delta assumption is added. -/
theorem endpoint_constant_from_first_cost {delta eta seed tau : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (heta : 0≤ eta) (htau : 0< tau)
    (hseed : seed≤ tau/16384) (F Q : ℕ) (hF : 0< F) (hQ : 1≤ Q)
    (H : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta)≤ delta^(-(seed/8))) :
    (64:ℝ)^3≤ delta^(-(tau/16)) := by
  have hFr : (1:ℝ)≤ F := by exact_mod_cast hF
  have hQr : (1:ℝ)≤ Q := by exact_mod_cast hQ
  have hQsq : (1:ℝ)≤ (Q:ℝ)^2 := by nlinarith only [hQr]
  have hFQ : (1:ℝ)≤ (F:ℝ)*(Q:ℝ)^2 := by nlinarith only [hFr,hQsq]
  have hpow := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hproduct : (1:ℝ)≤ (F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by nlinarith only [hFQ,hpow]
  have hC : (64:ℝ)^3≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by
    nlinarith only [hproduct]
  exact (hC.trans H).trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hseed,htau]))

/-- Read all-depth bounds for original fine-point multiplicities from the
CURRENT source's middle profiles and its existing first cost. The global
R, E1, representatives and source remain unchanged. -/
theorem actual_all_parent_profiles {n : ℕ} {D : FiniteScaleSource n} {eta a zeta tau seed : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (E1 : Finset (Fin n × Index)) (hE1 : E1⊆ retained original R) (hE1n : E1.Nonempty)
    (heta : 0≤ eta) (htau : 0< tau) (hseed : seed≤ tau/16384)
    (g F1 Q1 : ℕ) (hg : 0< g) (hgl : g≤ level) (hF1 : 0< F1) (hQ1 : 1≤ Q1)
    (hgrid : 1/(g:ℝ)< rankWindow tau/4)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)))
    (HM : ∀m : ℕ,boundaryWindow tau*(level:ℝ)≤ m → (m:ℝ)≤ (1-boundaryWindow tau)*(level:ℝ) →
      HasMiddleScale h R E1 a level m (tau/16)) :
    ∀m : ℕ,m≤ level → ∀p : Parent,(parentEdges D a (2^m) E1 p).Nonempty →
      D.thickness^tau*(localScale D.thickness m)^(-extremalExponent)≤ 
        NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ∧
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p)≤ 
        D.thickness^(-tau)*(localScale D.thickness m)^(-extremalExponent) := by
  have hv := NativeAllTwoScaleConfiguration.boundaryWindow_pos htau
  have hvquarter : boundaryWindow tau≤ 1/4 := (min_le_right _ _).trans (by norm_num)
  have hlarge := large_level_of_grid (rankWindow tau) (rankWindow_pos htau) g level hg hgrid hgl
  have hlarge' : 4≤ boundaryWindow tau*(level:ℝ) := hlarge.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg level))
  have hbudget : 2*(tau/16)+20*boundaryWindow tau≤ tau := by
    have hvsmall : boundaryWindow tau≤ tau/1000 := min_le_left _ _
    linarith only [hvsmall,htau]
  have hconstant := endpoint_constant_from_first_cost h.1.2.1 h.1.2.2.1 heta htau hseed F1 Q1 hF1 hQ1 H1
  have hfull := full_from_middle h original Hbackbone.1 Hbackbone.2.2.1 R E1
    (hE1.trans (filter_subset _ _)) (fun z hz => (mem_filter.mp (hE1 hz)).2) hE1n level Hbackbone.2.1
    (boundaryWindow tau) (tau/16) tau hv hvquarter (by positivity) hlarge' hbudget hconstant HM
  exact fun m hm p hp => (hfull m hm).2.2 p hp

end NativeReferenceOriginalParentProfiles
