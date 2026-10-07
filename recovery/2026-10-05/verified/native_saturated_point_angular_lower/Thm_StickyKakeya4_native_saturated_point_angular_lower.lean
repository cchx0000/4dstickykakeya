import Theorems.Thm_StickyKakeya4_native_original_point_saturation
import Theorems.Thm_StickyKakeya4_native_original_point_angular_lower
import Theorems.Thm_StickyKakeya4_native_same_source_multiplicity_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000

noncomputable section
namespace NativeSaturatedPointAngularLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalPointSaturation NativeJointUniformCoarseRelations NativeActualAngularMenuLower
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointAngularLower NativeIncidenceMultiplicityTower NativeSameSourceMultiplicityBalance
open NativeOriginalCoarseTupleMenu
open scoped BigOperators

/-- Selecting complete original-point fibers retains their original average
degree up to the reference point-uniformity constant, independently of the
number of selected spatial points. -/
theorem saturated_multiplicity_lower {A X : Type*} [DecidableEq A] [DecidableEq X]
    (E S : Finset (A × X)) (HS : Saturated E S Prod.snd) (hSn : S.Nonempty)
    (Q : ℕ) (HU : HasUniformFibers E Q Prod.snd) :
    multiplicity E ≤ (Q:ℝ)^2*multiplicity S := by
  have hEach (k : X) (hk : k∈S.image Prod.snd) :
      multiplicity E ≤ (Q:ℝ)^2*((S.filter (fun z => z.2=k)).card:ℝ) := by
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    have hEq := original_fiber_eq E S Prod.snd HS z hz
    rw [hEq]
    exact mean_le_point_fiber E Q HU z.2 (mem_image_of_mem _ (HS.1 hz))
  have hsum : (∑k∈S.image Prod.snd,((S.filter (fun z => z.2=k)).card:ℝ))=(S.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image Prod.snd S).symm
  have hcross : multiplicity E*((S.image Prod.snd).card:ℝ) ≤ (Q:ℝ)^2*(S.card:ℝ) := by
    calc
      _ = ∑_k∈S.image Prod.snd,multiplicity E := by simp [mul_comm]
      _ ≤ ∑k∈S.image Prod.snd,(Q:ℝ)^2*((S.filter (fun z => z.2=k)).card:ℝ) :=
        sum_le_sum hEach
      _ = _ := by rw [←mul_sum,hsum]
  have hpoints : (0:ℝ)< (S.image Prod.snd).card := by
    exact_mod_cast (hSn.image Prod.snd).card_pos
  change multiplicity E ≤ (Q:ℝ)^2*((S.card:ℝ)/(S.image Prod.snd).card)
  rw [←mul_div_assoc]
  exact (le_div_iff₀ hpoints).mpr hcross

/-- A single subsequent third refinement pays only its literal edge
retention factor. No native-source admission of T is used. -/
theorem saturated_refined_multiplicity_lower {A X : Type*} [DecidableEq A] [DecidableEq X]
    (E S T : Finset (A × X)) (HS : Saturated E S Prod.snd) (hTS : T⊆S)
    (hTn : T.Nonempty) (Q F : ℕ) (hF : 0< F)
    (HU : HasUniformFibers E Q Prod.snd) (hret : S.card≤F*T.card) :
    multiplicity E ≤ ((Q:ℝ)^2*F)*multiplicity T := by
  have hS := saturated_multiplicity_lower E S HS (hTn.mono hTS) Q HU
  have hT := selected_multiplicity_retention S T hTS F hF hret
  exact hS.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hT (sq_nonneg (Q:ℝ)))

/-- The current original-point angular menu lower is now measured against
the same reference E2-parent used for the spatial-cell angular-union upper.
The E1 angular-fiber cap and every refinement factor remain explicit. -/
theorem saturated_reference_point_angular_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E S T : Finset (Fin n × Index)) (HS : Saturated E S Prod.snd) (hTS : T⊆S)
    (hT1 : T⊆E1) (hT : T⊆incidences original)
    (m ell : ℕ) (hell : 3≤ell) (hscale : ((2^(m+ell-3):ℕ):ℝ)*D.thickness≤1)
    (p : Parent) (Q1 Q2 Q3 F3 : ℕ) (hF3 : 0< F3)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a (m+ell-3)))
    (HReferencePoint : HasUniformFibers E Q2 Prod.snd)
    (HPoint : HasUniformFibers T Q3 Prod.snd) (hret : S.card≤F3*T.card)
    (U : ℝ) (hU : 0≤U)
    (hUpper : ∀t,(parentEdges D a (2^(m+ell-3)) E1 t).Nonempty →
      multiplicity (parentEdges D a (2^(m+ell-3)) E1 t)≤U)
    (k : Index) (hk : k∈T.image Prod.snd) :
    multiplicity E≤343*(Q2:ℝ)^2*F3*(Q1:ℝ)^2*(Q3:ℝ)^2*U*(pointMenu D m ell p T k).card := by
  have hTn : T.Nonempty := (image_nonempty).mp ⟨k,hk⟩
  have hlow := saturated_refined_multiplicity_lower E S T HS hTS hTn Q2 F3 hF3 HReferencePoint hret
  have hmenu := original_point_angular_lower h original horiginal ha E1 T hT1 hT m ell hell hscale
    p Q1 Q3 HRef HPoint U hU hUpper k hk
  exact hlow.trans (by
    have hh := mul_le_mul_of_nonneg_left hmenu (show 0≤(Q2:ℝ)^2*F3 by positivity)
    convert hh using 1
    ring)

end NativeSaturatedPointAngularLower
