import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_query_tube
import Theorems.Thm_StickyKakeya4_original_balanced_owner_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace OriginalThreeDimensionalOwnerTubeCap
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalTubeGraphPairGeometry
open OriginalThreeDimensionalOwnerTubeGeometry OriginalThreeDimensionalOwnerQueryTube
open OriginalBalancedOwnerCounts OriginalFiniteCellWeights

/-- An owner-query tube pulls back to the SAME original pair tube. The
inverse original separation is explicit and no arbitrary-tube cap is used. -/
theorem original_reverse_owner_tube (p q u v x y : Point3) (Delta r R : ℝ)
    (hDelta : 0 < Delta) (hsmall : Delta ≤ r) (hr : 0 < r) (hR : R ≤ 1)
    (hp : ∀ j,|p j| ≤ 1) (hq : ∀ j,|q j| ≤ 1)
    (hu : ∀ j,|u j| ≤ 1) (hy : ∀ j,|y j| ≤ 1)
    (hsep : r ≤ distance3 p q)
    (hpu : distance3 p u ≤ Delta/4) (hqv : distance3 q v ≤ Delta/4)
    (hxy : distance3 x y ≤ Delta/4) (htube : y∈physicalTube3 u v R) :
    x∈physicalTube3 p q (R+20*Delta/r) := by
  have howner := original_owner_pair_separation p q u v Delta r hsep hsmall hpu hqv
  have hup : distance3 u p ≤ Delta/4 := by
    simpa only [distance3_eq_euclidean,dist_comm] using hpu
  have hvq : distance3 v q ≤ Delta/4 := by
    simpa only [distance3_eq_euclidean,dist_comm] using hqv
  have hyx : distance3 y x ≤ Delta/4 := by
    simpa only [distance3_eq_euclidean,dist_comm] using hxy
  have ht := original_pair_owner_tube_perturbation u v p q y R (r/2) (Delta/4)
    (by positivity) (by positivity) hR hu (fun j => (hy j).trans (by norm_num))
    howner hup hvq htube
  obtain ⟨t,ht⟩ := original_query_tube_movement p q y x
    (R+2*(Delta/4)+32*(Delta/4)/(r/2)) (Delta/4) hyx ht
  have hr4 := hsep.trans (original_box_distance_le_four p q hp hq)
  refine ⟨t,ht.trans ?_⟩
  have he : R+2*(Delta/4)+32*(Delta/4)/(r/2)+Delta/4=
      R+3*Delta/4+16*Delta/r := by field_simp; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hr4 hDelta.le
  have herr : 3*Delta/4 ≤ 4*Delta/r := by
    apply (le_div_iff₀ hr).mpr
    nlinarith only [hm,hDelta]
  calc
    R+3*Delta/4+16*Delta/r ≤ R+4*Delta/r+16*Delta/r := by
      exact add_le_add (add_le_add (le_refl R) herr) (le_refl (16*Delta/r))
    _ = R+20*Delta/r := by ring

/-- Every full original owner fiber over the owner-query tube is charged
in the tube of its inherited original pair. -/
theorem original_owner_tube_preimage (Q U C : Finset Point3) (owner : Point3 → Point3)
    (p q : Point3) (Delta r R : ℝ)
    (hDelta : 0 < Delta) (hsmall : Delta ≤ r) (hr : 0 < r) (hR : R ≤ 1)
    (hUQ : U⊆Q) (hCQ : C⊆Q) (hmap : ∀ x∈U,owner x∈C)
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1) (hp : p∈U) (hq : q∈U)
    (hclose : ∀ x∈U,distance3 x (owner x) ≤ Delta/4)
    (hsep : r ≤ distance3 p q) :
    U.filter (fun x => owner x∈physicalTube3 (owner p) (owner q) R) ⊆
      Q.filter (fun x => x∈physicalTube3 p q (R+20*Delta/r)) := by
  intro x hx
  obtain ⟨hxU,hxt⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hUQ hxU,?_⟩
  exact original_reverse_owner_tube p q (owner p) (owner q) x (owner x) Delta r R
    hDelta hsmall hr hR (hbox p (hUQ hp)) (hbox q (hUQ hq))
    (hbox (owner p) (hCQ (hmap p hp))) (hbox (owner x) (hCQ (hmap x hxU)))
    hsep (hclose p hp) (hclose q hq) (hclose x hxU) hxt

/-- Balanced FULL original fibers transfer an inherited pairwise cap to
actual unweighted owners, with exactly the balance and ambient-mass loss. -/
theorem original_unweighted_owner_tube_cap (Q U C : Finset Point3)
    (owner : Point3 → Point3) (p q : Point3) (Delta r R M A lam B : ℝ)
    (hDelta : 0 < Delta) (hsmall : Delta ≤ r) (hr : 0 < r) (hR : R ≤ 1)
    (hM : 0 < M) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hUQ : U⊆Q) (hCQ : C⊆Q) (hmap : ∀ x∈U,owner x∈C)
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1) (hp : p∈U) (hq : q∈U)
    (hclose : ∀ x∈U,distance3 x (owner x) ≤ Delta/4)
    (hsep : r ≤ distance3 p q)
    (hmin : ∀ c∈C,M ≤ pointWeight U owner c)
    (hmax : ∀ c∈C,pointWeight U owner c ≤ A*M)
    (hambient : lam*Q.card ≤ (U.card : ℝ))
    (hcap : ((Q.filter (fun x => x∈physicalTube3 p q (R+20*Delta/r))).card : ℝ) ≤ B*Q.card) :
    lam*(C.filter (fun y => y∈physicalTube3 (owner p) (owner q) R)).card ≤ A*B*C.card := by
  let D := C.filter (fun y => y∈physicalTube3 (owner p) (owner q) R)
  apply original_owner_region_count Q U C D owner M A lam B hM hB hlam
    (Finset.filter_subset _ _) hmap hmin hmax hambient
  have hsub : U.filter (fun x => owner x∈D) ⊆
      Q.filter (fun x => x∈physicalTube3 p q (R+20*Delta/r)) := by
    intro x hx
    obtain ⟨hxU,hxD⟩ := Finset.mem_filter.mp hx
    have ht := (Finset.mem_filter.mp hxD).2
    apply original_owner_tube_preimage Q U C owner p q Delta r R hDelta hsmall hr hR
      hUQ hCQ hmap hbox hp hq hclose hsep
    exact Finset.mem_filter.mpr ⟨hxU,ht⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcap

end OriginalThreeDimensionalOwnerTubeCap
