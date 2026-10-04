import Theorems.Thm_StickyKakeya4_original_three_dimensional_owner_graph_richness
import Theorems.Thm_StickyKakeya4_original_normalized_owner_physical_bridge
import Theorems.Thm_StickyKakeya4_original_three_dimensional_projected_owner_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000

noncomputable section
namespace OriginalNormalizedOwnerGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalLiteralSlabCover
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalVoronoiFibers
open OriginalThreeDimensionalOwnerGraphRichness OriginalProjectedOwnerProfile
open OriginalNormalizedOwnerQuery OriginalNormalizedOwnerPhysicalBridge
open OriginalThreeDimensionalProjectedOwnerCap OriginalThreeDimensionalPlanarTubeProjection
open OriginalPlanarTubeParameters OriginalFiniteCellWeights

abbrev Pair2 := Point2 × Point2

def normalizedOwnerGraph (b : Frame3) (G : Finset Pair3) (C : Finset Point3)
    (hC : C.Nonempty) : Finset Pair2 :=
  occupied (ownerGraph G C hC) (pairCode (normalizedProject b))

theorem original_normalized_owner_graph_subset (b : Frame3) (G : Finset Pair3)
    (C : Finset Point3) (hC : C.Nonempty) :
    normalizedOwnerGraph b G C hC⊆(normalizedImage b C).product (normalizedImage b C) := by
  intro e he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (original_owner_graph_subset G C hC hz)
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz1,Finset.mem_image_of_mem _ hz2⟩

/-- Exact injectivity of the same original center net preserves the number
of owner edges under normalization; no second center family is chosen. -/
theorem original_normalized_owner_graph_card (b : Frame3) (G : Finset Pair3)
    (C : Finset Point3) (hC : C.Nonempty) (hinj : Set.InjOn (normalizedProject b) C) :
    (normalizedOwnerGraph b G C hC).card=(ownerGraph G C hC).card := by
  apply Finset.card_image_of_injOn
  intro z hz w hw he
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (original_owner_graph_subset G C hC hz)
  obtain ⟨hw1,hw2⟩ := Finset.mem_product.mp (original_owner_graph_subset G C hC hw)
  apply Prod.ext
  · exact hinj hz1 hw1 (congrArg Prod.fst he)
  · exact hinj hz2 hw2 (congrArg Prod.snd he)

/-- Actual original rich owner points enter the literal frozen A1 tube
under the exact factor-four normalization, with unchanged point counts. -/
theorem original_normalized_owner_tube_population (b : Frame3) (C : Finset Point3)
    (e : Pair3) (W A k : ℝ) (hA : 0 ≤ A)
    (hinj : Set.InjOn (normalizedProject b) C)
    (hrich : k*C.card ≤ A*(physicalPairTube3 C W e).card) :
    k*(normalizedImage b C).card ≤ A*(OriginalPhysicalPairTube.physicalPairTube
      (normalizedImage b C) (W/4) (normalizedPair b e.1 e.2)).card := by
  have hsub : (physicalPairTube3 C W e).image (normalizedProject b)⊆
      OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) (W/4) (normalizedPair b e.1 e.2) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyC,hyt⟩ := Finset.mem_filter.mp hy
    exact original_physical_tube_normalized_membership b C e.1 e.2 y W hyC hyt
  have hcard : ((physicalPairTube3 C W e).image (normalizedProject b)).card=
      (physicalPairTube3 C W e).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
  have hh : (((physicalPairTube3 C W e).image (normalizedProject b)).card : ℝ) ≤
      (OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) (W/4) (normalizedPair b e.1 e.2)).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  rw [hcard] at hh
  rw [show (normalizedImage b C).card=C.card from Finset.card_image_of_injOn hinj]
  exact hrich.trans (mul_le_mul_of_nonneg_left hh hA)

/-- The normalized graph retains a literal original edge witness and its
proved physical richness. The query width is fifty Delta/r, not Delta. -/
theorem original_normalized_owner_graph_richness (b : Frame3) (G : Finset Pair3)
    (C : Finset Point3) (hC : C.Nonempty) (Delta r A k : ℝ) (hA : 0 ≤ A)
    (hinj : Set.InjOn (normalizedProject b) C)
    (hrich : ∀ e∈ownerGraph G C hC,∃ z∈G,pairCode (originalOwner C hC) z=e ∧
      r/2 ≤ distance3 e.1 e.2 ∧ k*C.card ≤ A*(physicalPairTube3 C (200*Delta/r) e).card) :
    ∀ e∈normalizedOwnerGraph b G C hC,∃ z∈G,
      normalizedPair b (originalOwner C hC z.1) (originalOwner C hC z.2)=e ∧
      k*(normalizedImage b C).card ≤ A*(OriginalPhysicalPairTube.physicalPairTube
        (normalizedImage b C) (50*Delta/r) e).card := by
  intro e he
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨z,hz,hzu,_hgap,hpop⟩ := hrich u hu
  have hn := original_normalized_owner_tube_population b C u (200*Delta/r) A k hA hinj hpop
  have hw : (200*Delta/r)/4=50*Delta/r := by ring
  rw [hw] at hn
  refine ⟨z,hz,?_,hn⟩
  exact congrArg (pairCode (normalizedProject b)) hzu

/-- The exact normalized owner graph inherits the ORIGINAL pairwise cap
through its actual edge witnesses. This asserts no cap for unrelated lines. -/
theorem original_normalized_owner_graph_cap (P Q C : Finset Point3) (hC : C.Nonempty)
    (G : Finset Pair3) (b : Frame3) (c rho Delta r qcap M A lam B : ℝ)
    (hrho : 0 ≤ rho) (hDelta : 0 < Delta) (hDelta1 : 2*Delta ≤ 1)
    (hDr : Delta ≤ r) (hr : 0 < r) (hsmall : 54*rho/r ≤ Delta) (h48 : 48*rho ≤ Delta)
    (hqcap : qcap ≤ 1) (hM : 0 < M) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hUQ : originalCarrier P C hC (Delta/4)⊆Q) (hCQ : C⊆Q)
    (hG : G⊆(originalCarrier P C hC (Delta/4)).product (originalCarrier P C hC (Delta/4)))
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1)
    (hraw : ∀ y∈C,|frameCoordinate b 2 y-c| ≤ 3*rho)
    (hsepC : ∀ x∈C,∀ y∈C,x≠y → Delta/4 ≤ distance3 x y)
    (hsep : ∀ z∈G,r ≤ distance3 z.1 z.2)
    (hmin : ∀ y∈C,M ≤ ((originalFiber P C hC (Delta/4) y).card : ℝ))
    (hmax : ∀ y∈C,((originalFiber P C hC (Delta/4) y).card : ℝ) ≤ A*M)
    (hambient : lam*Q.card ≤ ((originalCarrier P C hC (Delta/4)).card : ℝ))
    (hcap : ∀ z∈G,((physicalPairTube3 Q qcap z).card : ℝ) ≤ B*Q.card) :
    ∀ e∈normalizedOwnerGraph b G C hC,∀ R : ℝ,8*R+64*Delta/r ≤ qcap →
      lam*(OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) R e).card ≤
        A*B*(normalizedImage b C).card := by
  intro e he R hbudget
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
  let f := originalOwner C hC
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (hG hz)
  obtain ⟨swap,hchart⟩ : ∃ swap : Bool,
      |(chartProject b swap (f z.2)).2-(chartProject b swap (f z.1)).2| ≤
        |(chartProject b swap (f z.2)).1-(chartProject b swap (f z.1)).1| := by
    by_cases hh : |(project b (f z.2)).2-(project b (f z.1)).2| ≤
        |(project b (f z.2)).1-(project b (f z.1)).1|
    · exact ⟨false,by simpa only [chartProject,chart,Bool.false_eq_true,if_false] using hh⟩
    · exact ⟨true,by simpa only [chartProject,chart,if_true,Prod.fst_swap,Prod.snd_swap] using (lt_of_not_ge hh).le⟩
  have hcount := original_projected_owner_tube_cap Q (originalCarrier P C hC (Delta/4)) C f b swap
    z.1 z.2 c rho Delta r (4*R) qcap M A lam B hrho hDelta hDelta1 hDr hr hsmall
    (by nlinarith only [hbudget]) hqcap hM hB hlam hUQ hCQ
    (fun x _hx => original_owner_mem C hC x) hbox hraw hz1 hz2
    (fun x hx => (Finset.mem_filter.mp hx).2.le) (hsep z hz) hchart hmin hmax hambient (hcap z hz)
  have hread : (OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) R
      (normalizedPair b (f z.1) (f z.2))).card=
      (C.filter (fun y => OriginalThreeDimensionalProjectedQueryLift.EuclideanPairTube
        (projectedPair b swap (f z.1) (f z.2)) (4*R) (chartProject b swap y))).card := by
    have heq : OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) R
        (normalizedPair b (f z.1) (f z.2))=
        (normalizedImage b C).filter (OriginalThreeDimensionalProjectedQueryLift.EuclideanPairTube
          (normalizedPair b (f z.1) (f z.2)) R) := by
      ext x
      simp only [original_a1_physical_pair_tube_iff,Finset.mem_filter]
    rw [heq]
    exact original_normalized_query_card_readback b swap C c rho Delta hDelta h48 hraw hsepC (f z.1) (f z.2) R
  change lam*(OriginalPhysicalPairTube.physicalPairTube (normalizedImage b C) R
    (normalizedPair b (f z.1) (f z.2))).card ≤ _
  rw [hread,original_normalized_owner_card b c rho Delta C hDelta h48 hraw hsepC]
  exact hcount

end OriginalNormalizedOwnerGraph
