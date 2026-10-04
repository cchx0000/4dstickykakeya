import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_tube_cap
import Theorems.Thm_StickyKakeya4_original_three_dimensional_projected_query_lift
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
noncomputable section
namespace OriginalThreeDimensionalProjectedOwnerCap
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalProjectionCells OriginalThreeDimensionalPlanarBoxProjection
open OriginalThreeDimensionalPlanarTubeProjection OriginalThreeDimensionalPlanarTubeLift
open OriginalThreeDimensionalProjectedQueryLift OriginalPlanarTubeParameters
open OriginalThreeDimensionalOwnerTubeGeometry OriginalThreeDimensionalOwnerQueryTube
open OriginalThreeDimensionalOwnerTubeCap OriginalTubeGraphPairGeometry
open OriginalBalancedOwnerCounts OriginalFiniteCellWeights

/-- A query around the ACTUAL projected owner pair lifts to the same
inherited original pair. All endpoint, normal and fiber errors are charged
before using the original pairwise tube cap. R is the unnormalized radius. -/
theorem original_projected_owner_preimage_tube (b : Frame3) (swap : Bool)
    (p q u v x y : Point3) (c rho Delta r R qcap : ℝ)
    (hrho : 0 ≤ rho) (hDelta : 0 < Delta) (hDelta1 : 2*Delta ≤ 1)
    (hDr : Delta ≤ r) (hr : 0 < r) (hsmall : 54*rho/r ≤ Delta)
    (hbudget : 2*R+64*Delta/r ≤ qcap) (hqcap : qcap ≤ 1)
    (hpbox : ∀ j,|p j| ≤ 1) (hqbox : ∀ j,|q j| ≤ 1)
    (hubox : ∀ j,|u j| ≤ 1) (hvbox : ∀ j,|v j| ≤ 1)
    (hybox : ∀ j,|y j| ≤ 1)
    (hu : |frameCoordinate b 2 u-c| ≤ 3*rho)
    (hv : |frameCoordinate b 2 v-c| ≤ 3*rho)
    (hy : |frameCoordinate b 2 y-c| ≤ 3*rho)
    (hsep : r ≤ distance3 p q)
    (hpu : distance3 p u ≤ Delta/4) (hqv : distance3 q v ≤ Delta/4)
    (hxy : distance3 x y ≤ Delta/4)
    (hmax : |(chartProject b swap v).2-(chartProject b swap u).2| ≤
      |(chartProject b swap v).1-(chartProject b swap u).1|)
    (hquery : EuclideanPairTube (projectedPair b swap u v) R (chartProject b swap y)) :
    x∈physicalTube3 p q qcap := by
  have howner := original_owner_pair_separation p q u v Delta r hsep hDr hpu hqv
  have hdouble : 54*rho/(r/2) ≤ 2*Delta := by
    have he : 54*rho/(r/2)=2*(54*rho/r) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hraw := original_raw_width_le_expanded p q rho Delta r hr hDelta.le hsmall hpbox hqbox hsep
  have hyt := original_projected_query_tube_lifts b swap u v y c rho (2*Delta) (r/2) R
    hrho (by positivity) (by positivity) hDelta1 hdouble hubox hvbox hybox hu hv
    (hy.trans (by linarith only [hraw,hDelta])) howner hmax hquery
  have hr4 := hsep.trans (original_box_distance_le_four p q hpbox hqbox)
  have hden : 0 ≤ Delta/r := div_nonneg hDelta.le hr.le
  have h40 : 10*Delta ≤ 40*Delta/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_left hr4 (show 0 ≤ 10*Delta by positivity)
    nlinarith only [hh]
  have hwide : 2*R+10*Delta+20*Delta/r ≤ qcap := by
    calc
      2*R+10*Delta+20*Delta/r ≤ 2*R+40*Delta/r+20*Delta/r := by
        exact add_le_add (add_le_add (le_refl (2*R)) h40) (le_refl (20*Delta/r))
      _ = 2*R+60*(Delta/r) := by ring
      _ ≤ 2*R+64*(Delta/r) := by linarith only [hden]
      _ = 2*R+64*Delta/r := by ring
      _ ≤ qcap := hbudget
  have hR1 : 2*R+10*Delta ≤ 1 := by
    have h20 : 0 ≤ 20*Delta/r := div_nonneg (by positivity) hr.le
    linarith only [hwide,hqcap,h20]
  have hyt' : y∈physicalTube3 u v (2*R+10*Delta) := by
    simpa only [show 5*(2*Delta)=10*Delta by ring] using hyt
  obtain ⟨t,ht⟩ := original_reverse_owner_tube p q u v x y Delta r (2*R+10*Delta)
    hDelta hDr hr hR1 hpbox hqbox hubox hybox hsep hpu hqv hxy hyt'
  exact ⟨t,ht.trans hwide⟩

/-- Actual balanced full fibers and the original pair cap give the
unnormalized projected-owner cap. The normalized project/4 adapter can
substitute4R without suppressing that factor. -/
theorem original_projected_owner_tube_cap (Q U C : Finset Point3)
    (owner : Point3 → Point3) (b : Frame3) (swap : Bool) (p q : Point3)
    (c rho Delta r R qcap M A lam B : ℝ)
    (hrho : 0 ≤ rho) (hDelta : 0 < Delta) (hDelta1 : 2*Delta ≤ 1)
    (hDr : Delta ≤ r) (hr : 0 < r) (hsmall : 54*rho/r ≤ Delta)
    (hbudget : 2*R+64*Delta/r ≤ qcap) (hqcap : qcap ≤ 1)
    (hM : 0 < M) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hUQ : U⊆Q) (hCQ : C⊆Q) (hmap : ∀ x∈U,owner x∈C)
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1)
    (hraw : ∀ y∈C,|frameCoordinate b 2 y-c| ≤ 3*rho)
    (hp : p∈U) (hq : q∈U)
    (hclose : ∀ x∈U,distance3 x (owner x) ≤ Delta/4)
    (hsep : r ≤ distance3 p q)
    (hmaxchart : |(chartProject b swap (owner q)).2-(chartProject b swap (owner p)).2| ≤
      |(chartProject b swap (owner q)).1-(chartProject b swap (owner p)).1|)
    (hmin : ∀ y∈C,M ≤ pointWeight U owner y)
    (hmax : ∀ y∈C,pointWeight U owner y ≤ A*M)
    (hambient : lam*Q.card ≤ (U.card : ℝ))
    (hcap : ((Q.filter (fun x => x∈physicalTube3 p q qcap)).card : ℝ) ≤ B*Q.card) :
    lam*(C.filter (fun y => EuclideanPairTube (projectedPair b swap (owner p) (owner q))
      R (chartProject b swap y))).card ≤ A*B*C.card := by
  let D := C.filter (fun y => EuclideanPairTube (projectedPair b swap (owner p) (owner q))
    R (chartProject b swap y))
  apply original_owner_region_count Q U C D owner M A lam B hM hB hlam
    (Finset.filter_subset _ _) hmap hmin hmax hambient
  have hsub : U.filter (fun x => owner x∈D) ⊆ Q.filter (fun x => x∈physicalTube3 p q qcap) := by
    intro x hx
    obtain ⟨hxU,hxD⟩ := Finset.mem_filter.mp hx
    have hup := hmap p hp
    have hvq := hmap q hq
    have hy := hmap x hxU
    refine Finset.mem_filter.mpr ⟨hUQ hxU,?_⟩
    exact original_projected_owner_preimage_tube b swap p q (owner p) (owner q) x (owner x)
      c rho Delta r R qcap hrho hDelta hDelta1 hDr hr hsmall hbudget hqcap
      (hbox p (hUQ hp)) (hbox q (hUQ hq))
      (hbox (owner p) (hCQ hup)) (hbox (owner q) (hCQ hvq)) (hbox (owner x) (hCQ hy))
      (hraw _ hup) (hraw _ hvq) (hraw _ hy) hsep (hclose p hp) (hclose q hq)
      (hclose x hxU) hmaxchart (Finset.mem_filter.mp hxD).2
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcap

end OriginalThreeDimensionalProjectedOwnerCap
