import Theorems.Thm_StickyKakeya4_original_three_dimensional_narrow_slab_overlap
import Theorems.Thm_StickyKakeya4_original_three_dimensional_slice_maximizer
import Theorems.Thm_StickyKakeya4_original_three_dimensional_unit_normals
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped Matrix BigOperators
namespace OriginalThreeDimensionalAnnularSlabCharge
open Classical Matrix OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalUnitSlabs
open OriginalThreeDimensionalUnitNormals OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalCrossGeometry
open OriginalThreeDimensionalSlabOverlap OriginalThreeDimensionalNarrowSlabOverlap

def sliceAnnulus (P : Finset Point3) (rho D outer inner : ℝ) (z : Pair3)
    (d : DirectionLabel) (k : ℤ) : Finset Point3 :=
  physicalPairTube3 (enlargedSlice P rho d k D) outer z\
    physicalPairTube3 (enlargedSlice P rho d k D) inner z

/-- Actual separated original slab labels have disjoint original annular
supports. This is proved from their real Euclidean normals and original
endpoints, rather than assumed as an overlap certificate. -/
theorem original_separated_slab_annuli_disjoint
    (P : Finset Point3) (z : Pair3) (rho D r outer inner : ℝ)
    (d e : DirectionLabel) (kd ke : ℤ)
    (hrho : 0 ≤ rho) (hD : 0 < D) (hr : 0 < r) (hinner : 0 < inner) (hwidth : 3*rho ≤ D) (hscale : 54*rho ≤ D*r)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hsep : r ≤ distance3 z.1 z.2)
    (hd : z.1∈slabPoints P rho d kd ∧ z.2∈slabPoints P rho d kd)
    (he : z.1∈slabPoints P rho e ke ∧ z.2∈slabPoints P rho e ke)
    (hgap : 30*D/inner ≤  min (distance3 (unitNormal rho d) (unitNormal rho e))
      (distance3 (unitNormal rho d) (-unitNormal rho e))) :
    Disjoint (sliceAnnulus P rho D outer inner z d kd) (sliceAnnulus P rho D outer inner z e ke) := by
  apply Finset.disjoint_left.mpr
  intro x hxd hxe
  obtain ⟨hxout,hxnot⟩ := Finset.mem_sdiff.mp hxd
  have hxQd := (Finset.mem_filter.mp hxout).1
  have hxQe := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hxe).1).1
  have hxP : x∈P := (Finset.mem_filter.mp hxQd).1
  have hnx (u : DirectionLabel) (k : ℤ) (hxQ : x∈enlargedSlice P rho u k D) :
      |unitNormal rho u ⬝ᵥ x-rho*k/normalLength rho u| ≤ D := by
    rw [dotProduct,original_unit_normal_dot]
    exact (Finset.mem_filter.mp hxQ).2
  have hn (u : DirectionLabel) : normSq3 (unitNormal rho u)=1 := by
    simpa only [normSq3,dotProduct,pow_two] using original_unit_normal_square rho u
  have hnp (u : DirectionLabel) (k : ℤ) (p : Point3) (hp : p∈slabPoints P rho u k) :
      |unitNormal rho u ⬝ᵥ p-rho*k/normalLength rho u| ≤ 3*rho := by
    rw [dotProduct,original_unit_normal_dot]
    exact original_slab_in_unit_slab P rho u k hrho p hp
  have hout : x∉physicalTube3 z.1 z.2 inner := by
    intro hx
    exact hxnot (Finset.mem_filter.mpr ⟨hxQd,hx⟩)
  have hclose := original_shared_narrow_slab_point_forces_close_normals z.1 z.2 x
    (unitNormal rho d) (unitNormal rho e) (rho*kd/normalLength rho d) (rho*ke/normalLength rho e)
    rho D r inner hrho hD hr hinner hwidth hscale (hn d) (hn e)
    (hbox z.1 (Finset.mem_filter.mp hd.1).1) (hbox x hxP) hsep (hnp d kd z.1 hd.1) (hnp d kd z.2 hd.2) (hnx d kd hxQd)
    (hnp e ke z.1 he.1) (hnp e ke z.2 he.2) (hnx e ke hxQe) hout
  exact (not_lt_of_ge hgap) hclose

/-- Sum the actual annular source populations of a separated family of
original slabs into the unchanged original physical tube population. -/
theorem original_separated_annular_slab_sum
    (P : Finset Point3) (z : Pair3) (S : Finset DirectionLabel)
    (k : DirectionLabel→ℤ) (rho D r outer inner : ℝ)
    (hrho : 0 ≤ rho) (hD : 0 < D) (hr : 0 < r) (hinner : 0 < inner) (hwidth : 3*rho ≤ D) (hscale : 54*rho ≤ D*r)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hsep : r ≤ distance3 z.1 z.2)
    (hslabs : ∀ d∈S, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d))
    (hgap : ∀ d∈S, ∀ e∈S, d≠e →
      30*D/inner ≤  min (distance3 (unitNormal rho d) (unitNormal rho e))
        (distance3 (unitNormal rho d) (-unitNormal rho e))) :
    ∑ d∈S, (sliceAnnulus P rho D outer inner z d (k d)).card ≤ (physicalPairTube3 P outer z).card := by
  let B := fun d => sliceAnnulus P rho D outer inner z d (k d)
  have hdis : ∀ d∈S, ∀ e∈S, d≠e → Disjoint (B d) (B e) := by
    intro d hd e he hne
    exact original_separated_slab_annuli_disjoint P z rho D r outer inner d e (k d) (k e)
      hrho hD hr hinner hwidth hscale hbox hsep (hslabs d hd) (hslabs e he) (hgap d hd e he hne)
  have hsub : S.biUnion B⊆physicalPairTube3 P outer z := by
    intro x hx
    obtain ⟨d,_hd,hxd⟩ := Finset.mem_biUnion.mp hx
    have hh := Finset.mem_filter.mp (Finset.mem_sdiff.mp hxd).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh.1).1,hh.2⟩
  have hcard := Finset.card_biUnion hdis
  change ∑ d∈S, (B d).card ≤ _
  rw [← hcard]
  exact Finset.card_le_card hsub

end OriginalThreeDimensionalAnnularSlabCharge
