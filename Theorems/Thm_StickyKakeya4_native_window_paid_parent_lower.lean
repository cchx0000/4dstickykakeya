import Theorems.Thm_StickyKakeya4_native_paid_parent_multiplicity_lower
import Theorems.Thm_StickyKakeya4_native_paid_parent_scale_budget
import Theorems.Thm_StickyKakeya4_native_early_window_successor
import Theorems.Thm_StickyKakeya4_native_all_two_scale_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeWindowPaidParentLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeFixedCompactKakeyaExponent
open NativeTwoScaleConfiguration NativePaidParentMultiplicityLower NativePaidParentScaleBudget
open NativeEarlyWindowSuccessor NativeFixedSizeScaleMenu NativeAllTwoScaleConfiguration

/-- A fixed first-stage schedule and its ACTUAL source cost supply the
retained conditional lower at every requested first-half depth. This includes
depths below the first clipped menu point and assumes no off-menu uniformity. -/
theorem window_parent_power_lower {n : ℕ} {D : FiniteScaleSource n}
    {eta a theta tau cost : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index))
    (hE1 : E1⊆incidences original) (hER : ∀z∈E1,z.1∈R) (hE21 : E2⊆E1)
    (level m f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmf : m ≤ f)
    (hhalf : (f:ℝ) ≤ (level:ℝ)/2)
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2) (g : ℕ) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < w/4) (hgl : g ≤ level) (Q factor : ℕ) (hfactor : 0 < factor)
    (hcost : (125*175616*16384:ℝ)*(factor:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-cost))
    (HU : ∀j : Fin (g+1),HasUniformFibers E1 Q
      (conditionedGlobalPair h R a level (windowSchedule w hw.le g level j).val
        (windowSchedule w hw.le g level j).val))
    (p : Parent) (hp : (parentEdges D a (2^m) E1 p).Nonempty)
    (htheta : 0 < theta)
    (hret : theta*((parentEdges D a (2^m) E1 p).card:ℝ) ≤ (parentEdges D a (2^m) E2 p).card)
    (Hreference : HasConditionalTwoScale h R E1 a level m f tau) :
    theta*D.thickness^(tau+cost+10*w)*
        ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E2 p))).toReal := by
  obtain ⟨j,hfj,hratio⟩ := exists_early_successor_power w hw hwsmall g level f hg hgrid hgl hhalf hdy
  let fine := (windowSchedule w hw.le g level j).val
  have hQ : 0 < Q := uniform_radix_pos E1 (hp.mono (filter_subset _ _)) _ Q (HU j)
  have hrad := geometry_radix_cost h.1.2.1 h.1.2.2.1 heta factor Q hfactor hcost
  have hden := transfer_denominator_cost h.1.2.1
    (show (0:ℝ)≤((2^(fine-f):ℕ):ℝ) by positivity) Q hratio hrad
  have hnear := parent_conditional_power_lower h original horiginal ha R E1 E2 hE1 hER hE21
    level m f fine hdy hmf hfj (Nat.le_of_lt_succ (windowSchedule w hw.le g level j).isLt)
    Q (HU j) p hp htheta hret Hreference
  exact absorbed_lower h.1.2.1 htheta.le (by positivity : (0:ℝ)<((2^(fine-f):ℕ):ℝ)) Q hQ
    (by positivity) hden hnear

/-- Direct consumer of the actual all-two-scale first-stage fields. Its
diagonal relation is selected from the SAME fixed fullSchedule; the paid
parent-retention coefficient is kept literal for the later cleanup caller. -/
theorem master_parent_power_lower {n : ℕ} {D : FiniteScaleSource n}
    {eta a theta tau cost : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta) (htau : 0 < tau)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 E2 : Finset (Fin n × Index))
    (hE1 : E1⊆incidences original) (hER : ∀z∈E1,z.1∈R) (hE21 : E2⊆E1)
    (level m f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmf : m ≤ f)
    (hhalf : (f:ℝ) ≤ (level:ℝ)/2) (g : ℕ) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4) (hgl : g ≤ level)
    (Q factor : ℕ) (hfactor : 0 < factor)
    (hcost : (125*175616*16384:ℝ)*(factor:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-cost))
    (Hconditioned : ∀i j : Fin (g+1),HasUniformFibers E1 Q
        (conditionedGlobalPair h R a level (fullSchedule tau htau g level i).val
          (fullSchedule tau htau g level j).val) ∧
      HasUniformFibers E1 Q
        (conditionedGlobalPoint h R a level (fullSchedule tau htau g level i).val
          (fullSchedule tau htau g level j).val))
    (Hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (p : Parent) (hp : (parentEdges D a (2^m) E1 p).Nonempty)
    (htheta : 0 < theta)
    (hret : theta*((parentEdges D a (2^m) E1 p).card:ℝ) ≤ (parentEdges D a (2^m) E2 p).card) :
    theta*D.thickness^(tau+cost+10*min (boundaryWindow tau) ((tau/16)/1000))*
        ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E2 p))).toReal := by
  let w := min (boundaryWindow tau) ((tau/16)/1000)
  have hw : 0 < w := lt_min (boundaryWindow_pos htau) (by positivity)
  have hsmall : w < 1/2 :=
    ((min_le_left _ _).trans (min_le_right (tau/1000) (1/8))).trans_lt (by norm_num)
  have hfL : f ≤ level := by
    have hln : (0:ℝ)≤level := Nat.cast_nonneg _
    have hh : (f:ℝ)≤level := by linarith only [hhalf,hln]
    exact_mod_cast hh
  apply window_parent_power_lower h heta original horiginal ha R E1 E2 hE1 hER hE21
    level m f hdy hmf hhalf w hw hsmall g hg hgrid hgl Q factor hfactor hcost
    (fun j => ?_) p hp htheta hret (Hreference m f hmf hfL)
  simpa only [fullSchedule,NativeMiddleWindowBalance.canonicalSchedule] using (Hconditioned j j).1

end NativeWindowPaidParentLower
