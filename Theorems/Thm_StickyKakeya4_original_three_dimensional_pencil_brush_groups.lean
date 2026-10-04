import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_partition
import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_unit_slabs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPencilBrushGroups
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalPencilGeometry OriginalThreeDimensionalPencilPartition
open OriginalThreeDimensionalPencilUnitSlabs

def originalPencilSlab (P : Finset Point3) (rho : ℝ) (stem : Pair3)
    (e : Equiv.Perm (Fin 3)) (v : Pair3) : Finset Point3 :=
  let c := pencilChart stem v e
  let t := pencilScalar stem v e
  P.filter (fun x => |(∑ j, pencilUnitNormal stem e c t j*x j)-
    rawPencilCenter stem e c t/pencilNormalLength stem e c t| ≤ 100*rho)

/-- Construct whole original brush groups in actual stem planes. The
finite overlap is derived for exact raw bands before unit normalization,
and every selected plane contains full original tube populations. -/
theorem exists_original_pencil_brush_groups (P X : Finset Point3) (B : Finset Pair3)
    (Y : Pair3 → Finset Point3) (rho s : ℝ) (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (hrho : 0 < rho) (hs : 0 < s) (hs1 : s ≤ 1)
    (hXP : X⊆P) (hout : ∀ x∈X, x∉physicalTube3 stem.1 stem.2 s)
    (hY : ∀ z∈B, Y z⊆X)
    (hYtube : ∀ z∈B, Y z⊆physicalPairTube3 P (8*rho) z)
    (hsne : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hsbox : ∀ j, |stem.1 j| ≤ 1) (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hne : ∀ z∈B, z.2 (e 2)-z.1 (e 2) ≠ 0)
    (hmax : ∀ z∈B, ∀ j, |z.2 j-z.1 j| ≤ |z.2 (e 2)-z.1 (e 2)|)
    (htrans : ∀ z∈B, ∃ j, slope z (e 2) j ≠ slope stem (e 2) j)
    (hmeet : ∀ z∈B, ∃ p∈P, p∈physicalTube3 stem.1 stem.2 (8*rho) ∧
      p∈physicalTube3 z.1 z.2 (8*rho)) :
    ∃ R : Finset Pair3, R⊆B ∧ Set.InjOn (pencilCell rho stem e) R ∧
      R.image (pencilCell rho stem e)=B.image (pencilCell rho stem e) ∧
      B.card=∑ v∈R, (pencilGroup B rho stem e v).card ∧
      (∀ z∈B, ∃ v∈R, z∈pencilGroup B rho stem e v) ∧
      (∑ v∈R, ((pencilShadeUnion B rho stem e Y v).card : ℝ)) ≤ 4000/s*X.card ∧
      ∀ v∈R,
        (∑ j, (pencilUnitNormal stem e (pencilChart stem v e) (pencilScalar stem v e) j)^2)=1 ∧
        (∀ l : ℝ, pencilValue stem e (pencilChart stem v e) (pencilScalar stem v e)
          (linePoint3 stem.1 stem.2 l)=0) ∧
        ∀ z∈pencilGroup B rho stem e v,
          physicalPairTube3 P (8*rho) z⊆originalPencilSlab P rho stem e v ∧
          ∀ x∈physicalPairTube3 P (8*rho) z,
            |pencilValue stem e (pencilChart stem v e) (pencilScalar stem v e) x| ≤ 100*rho := by
  obtain ⟨R,hR,hinj,himage,hcard,hcover⟩ := exists_original_pencil_representatives B rho stem e
  refine ⟨R,hR,hinj,himage,hcard,hcover,?_,?_⟩
  · exact original_pencil_shade_union_budget P X B R Y rho s stem e hrho hs hs1
      hR hinj hXP hout hY hYtube hsne hsmax hsbox hbox hne hmax htrans hmeet
  · intro v _hv
    have hunit := original_pencil_unit_slab stem e (pencilChart stem v e) (pencilScalar stem v e)
    refine ⟨hunit.1,fun l => original_pencil_contains_stem stem e _ _ l hsne,?_⟩
    intro z hz
    have hraw := original_pencil_group_full_population P B rho stem v e hrho hsne hsmax
      hsbox hbox hne hmax htrans hmeet z hz
    refine ⟨?_,hraw⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hunit.2.2 rho hrho.le x (hraw x hx)⟩

end OriginalThreeDimensionalPencilBrushGroups
