import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation
import Theorems.Thm_StickyKakeya4_native_endpoint_parent_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeConditionalParentBoundary
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeDyadicParentCells
open NativeConditionalCoarseInterpolation NativeIncidenceMultiplicityTower NativeEndpointParentBounds

/-- Count the actual d-parent labels occurring after the fixed global
f-projection of one original m-parent. The image contains no new labels. -/
lemma conditional_ancestor_image_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m d f : ℕ)
    (hmd : m ≤ d) (hdf : d ≤ f) (p : Parent) :
    (((parentEdges D a (2^m) E p).image (physicalPair h R a level f)).image
      (fun z => ancestor f d z.1)).card ≤ (2^(d-m))^6 := by
  have he : ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)).image
      (fun z => ancestor f d z.1) =
        (parentEdges D a (2^m) E p).image (fun z => parentLabel D a (2^d) z.1) := by
    rw [image_image]
    apply Finset.image_congr
    intro z _hz
    exact parent_ancestor_eq D a hdf z.1
  rw [he]
  exact active_descendants_card_le D a E hmd p

/-- Upper bounds for the genuine finer outer-parent images extend to their
literal union, with only the exact six-dimensional descendant count. Both
outer scales use the same global-f physical map and full-R representatives. -/
theorem coarser_outer_parent_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m d f : ℕ)
    (hmd : m ≤ d) (hdf : d ≤ f) (U : ℝ) (hU : 0 ≤ U)
    (H : ∀q,(parentEdges D a (2^d) E q).Nonempty →
      multiplicity ((parentEdges D a (2^d) E q).image (physicalPair h R a level f)) ≤ U)
    (p : Parent) :
    multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ≤
      (((2^(d-m):ℕ):ℝ)^6)*U := by
  let I := (parentEdges D a (2^m) E p).image (physicalPair h R a level f)
  have hchild : ∀q∈I.image (fun z => ancestor f d z.1),
      multiplicity (parent I (ancestor f d) q) ≤ U := by
    intro q hq
    have hne := parent_nonempty I (ancestor f d) hq
    change (parent ((parentEdges D a (2^m) E p).image (physicalPair h R a level f))
      (ancestor f d) q).Nonempty at hne
    rw [←physical_image_parent h R (parentEdges D a (2^m) E p) a level d f hdf q] at hne
    have hraw : (parentEdges D a (2^d) (parentEdges D a (2^m) E p) q).Nonempty :=
      image_nonempty.mp hne
    have he := NativeScaleMenuSuccessor.nested_parentEdges_eq D a E hmd p q hraw
    change multiplicity (parent ((parentEdges D a (2^m) E p).image
      (physicalPair h R a level f)) (ancestor f d) q) ≤ U
    rw [←physical_image_parent h R (parentEdges D a (2^m) E p) a level d f hdf q,he]
    exact H q (he ▸ hraw)
  have hprod := multiplicity_le_parent_upper I (ancestor f d) U hchild
  have hcoarse := multiplicity_le_tube_card (coarse I (ancestor f d))
  rw [coarse_parents] at hcoarse
  have hc : ((I.image (fun z => ancestor f d z.1)).card:ℝ) ≤ ((2^(d-m):ℕ):ℝ)^6 := by
    exact_mod_cast conditional_ancestor_image_card h R E a level m d f hmd hdf p
  exact hprod.trans ((mul_le_mul_of_nonneg_left (hcoarse.trans hc) hU).trans_eq (by ring))

end NativeConditionalParentBoundary
