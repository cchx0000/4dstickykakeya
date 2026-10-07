import Theorems.Thm_StickyKakeya4_native_original_coarse_tuple_menu
import Theorems.Thm_StickyKakeya4_native_local_menu_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalTupleParentInterpolation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeDyadicParentCells NativeJointUniformCoarseRelations
open NativeIncidentRankSelection NativeDirectionRankDichotomy NativeOriginalCoarseTupleMenu

/-- Actual point fibers retain the same old-cell coordinate under dyadic
parent nesting. No pointwise uniformity at the off-menu depth is asserted. -/
theorem point_parent_fiber_subset_ancestor {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (a : ℝ)
    {c m : ℕ} (hcm : c ≤ m) (k : Index) (p : Parent) :
    (pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p) ⊆
      (pointSet E1 k).filter (fun z => parentLabel D a (2^c) z.1=ancestor m c p) := by
  intro z hz
  obtain ⟨hzPoint,hzp⟩ := mem_filter.mp hz
  obtain ⟨hzE,hzk⟩ := mem_filter.mp hzPoint
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨h21 hzE,hzk⟩,?_⟩
  rw [←parent_ancestor_eq D a hcm z.1,hzp]

/-- A reference relation installed at c supplies a genuine pointwise upper
for every finer target parent at m. Only the original c-parent average is used. -/
theorem point_parent_fiber_upper_of_ancestor {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (a : ℝ)
    {c m : ℕ} (hcm : c ≤ m) (Q : ℕ)
    (Href : HasUniformFibers E1 Q (formalPair D a c)) (U : ℝ) (hU : 0 ≤ U)
    (hupper : ∀p,(parentEdges D a (2^c) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^c) E1 p) ≤ U)
    (k : Index) (p : Parent) :
    (((pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p)).card:ℝ) ≤
      (Q:ℝ)^2*U := by
  have hs := point_parent_fiber_subset_ancestor D E1 E2 h21 a hcm k p
  exact (show (((pointSet E2 k).filter (fun z => parentLabel D a (2^m) z.1=p)).card:ℝ) ≤
      ((pointSet E1 k).filter (fun z => parentLabel D a (2^c) z.1=ancestor m c p)).card by
    exact_mod_cast card_le_card hs).trans
      (reference_point_parent_fiber_upper D E1 a c Q Href U hU hupper k (ancestor m c p))

/-- Deterministic off-menu tuple readback. The numerator is the actual fine
chain family itself, and the denominator is derived from the installed original
ancestor. A proved fine-chain lower bound can therefore be consumed directly,
without an off-menu uniformity or arbitrary tuple-cover certificate. -/
theorem coarse_menu_lower_of_ancestor {n : ℕ} (D : FiniteScaleSource n)
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2 ⊆ E1) (a : ℝ)
    {c m : ℕ} (hcm : c ≤ m) (Q : ℕ)
    (Href : HasUniformFibers E1 Q (formalPair D a c)) (U : ℝ) (hU : 0 ≤ U)
    (hupper : ∀p,(parentEdges D a (2^c) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^c) E1 p) ≤ U)
    (k : Index) (hk : k∈E2.image Prod.snd) (q : ℝ) (ell : ℕ) :
    0 < (Q:ℝ)^2*U ∧
      ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q ell).card:ℝ)/
          (((Q:ℝ)^2*U)^ell) ≤ ((coarseMenu D a m E2 k q ell).card:ℝ) := by
  let A := pointSet E2 k
  let C := chains A (fun z => slopeVector D z.1) q ell
  let f := fun z : Fin n × Index => parentLabel D a (2^m) z.1
  have hfiber (p : Parent) : ((A.filter (fun z => f z=p)).card:ℝ) ≤ (Q:ℝ)^2*U :=
    point_parent_fiber_upper_of_ancestor D E1 E2 h21 a hcm Q Href U hU hupper k p
  have hB : 0 < (Q:ℝ)^2*U := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    have hzA : z∈A := mem_filter.mpr ⟨hz,hzk⟩
    have hn : (A.filter (fun w => f w=f z)).Nonempty :=
      ⟨z,mem_filter.mpr ⟨hzA,rfl⟩⟩
    have hp : (0:ℝ) < (A.filter (fun w => f w=f z)).card := by
      exact_mod_cast card_pos.mpr hn
    exact hp.trans_le (hfiber (f z))
  refine ⟨hB,?_⟩
  exact NativeFiniteTupleFibers.coarse_tuple_card_lower A C f ell
    (fun xs hxs => chains_length _ _ _ _ xs hxs)
    (fun xs hxs => chains_labels _ _ _ _ xs hxs)
    ((Q:ℝ)^2*U) hB hfiber (C.card:ℝ) le_rfl

end NativeOriginalTupleParentInterpolation
