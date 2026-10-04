import Theorems.Thm_StickyKakeya4_original_three_dimensional_planar_tube_lift
import Theorems.Thm_StickyKakeya4_original_planar_core_richness
import Theorems.Thm_StickyKakeya4_original_planar_tube_chart
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalThreeDimensionalPhysicalCoreRichness
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalPlanarBoxProjection OriginalThreeDimensionalPlanarTubeProjection
open OriginalThreeDimensionalPlanarTubeLift OriginalThreeDimensionalAveragedSliceEnergy
open OriginalPlanarTubeParameters OriginalPlanarTubeChart OriginalPlanarCoreRichness
open OriginalPlanarTubeEnergy

lemma original_raw_projected_pair_ne (b : Frame3) (p q : Point3)
    (c rho Delta r : ℝ) (hrho : 0 ≤ rho) (hr : 0 < r) (hDelta1 : Delta ≤ 1)
    (hsmall : 54*rho/r ≤ Delta)
    (hp : |frameCoordinate b 2 p-c| ≤ 3*rho)
    (hq : |frameCoordinate b 2 q-c| ≤ 3*rho) (hsep : r ≤ distance3 p q) :
    project b p≠project b q := by
  have hm := (div_le_iff₀ hr).mp hsmall
  have hD := mul_le_mul_of_nonneg_right hDelta1 hr.le
  have hscale : 4*(3*rho) ≤ r := by nlinarith only [hm,hD,hrho]
  have hg := original_projected_pair_separation b c (3*rho) r p q hp hq hscale hsep
  intro he
  rw [he] at hg
  simp only [PlanarStripIntersection.boxDistance,sub_self,abs_zero,max_self] at hg
  linarith only [hr,hg]

/-- Original ambient physical tube richness and an original I1 energy
budget produce a retained graph rich in its actual physical core. The
common chart, projected strip richness and tube-cell energy are all
constructed internally, preserving every original point and pair label. -/
theorem exists_original_physical_core_rich_graph (Q S : Finset Point3)
    (G : Finset (Point3 × Point3)) (b : Frame3) (c Delta rho r m ell : ℝ)
    (hDelta : 0 < Delta) (hDelta1 : Delta ≤ 1) (hrho : 0 ≤ rho) (hr : 0 < r)
    (hsmall : 54*rho/r ≤ Delta) (hm : 0 < m)
    (hSQ : S⊆Q) (hG : G⊆S.product S)
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1)
    (hslab : ∀ x∈Q,|frameCoordinate b 2 x-c| ≤ Delta)
    (hraw : ∀ e∈G,|frameCoordinate b 2 e.1-c| ≤ 3*rho ∧
      |frameCoordinate b 2 e.2-c| ≤ 3*rho)
    (hsep : ∀ e∈G,r ≤ distance3 e.1 e.2)
    (hrich : ∀ e∈G,m ≤ ((physicalPairTube3 Q rho e).card : ℝ))
    (hbudget : 480000*sliceEnergy Q Delta*ell^2 ≤ m^2*G.card) :
    ∃ G' : Finset (Point3 × Point3),G'⊆G ∧ (G.card : ℝ) ≤ 4*G'.card ∧
      ∀ e∈G',ell ≤ ((physicalPairTube3 S (32*Delta) e).card : ℝ) := by
  by_cases hGne : G.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hGne
    refine ⟨∅,Finset.empty_subset _,?_,?_⟩
    · simp [he]
    · simp
  obtain ⟨e0,he0⟩ := hGne
  obtain ⟨he01,he02⟩ := Finset.mem_product.mp (hG he0)
  have hwidth := original_raw_width_le_expanded e0.1 e0.2 rho Delta r hr hDelta.le hsmall
    (hbox e0.1 (hSQ he01)) (hbox e0.2 (hSQ he02)) (hsep e0 he0)
  have hrhoDelta : rho ≤ Delta := by linarith only [hwidth,hrho]
  have hne (e : Point3 × Point3) (he : e∈G) : project b e.1≠project b e.2 :=
    original_raw_projected_pair_ne b e.1 e.2 c rho Delta r hrho hr hDelta1 hsmall
      (hraw e he).1 (hraw e he).2 (hsep e he)
  obtain ⟨swap,hchartG,hchartkeep⟩ := exists_original_common_planar_chart G (project b) hne
  let GC := chartPairs G (project b) swap
  have hGC : GC⊆S.product S := hchartG.trans hG
  have hchartkeepR : (G.card : ℝ) ≤ 2*GC.card := by exact_mod_cast hchartkeep
  have hneC (e : Point3 × Point3) (he : e∈GC) :
      (chartProject b swap e.2).1-(chartProject b swap e.1).1≠0 :=
    (Finset.mem_filter.mp he).2.1
  have hmaxC (e : Point3 × Point3) (he : e∈GC) :
      |(chartProject b swap e.2).2-(chartProject b swap e.1).2| ≤
        |(chartProject b swap e.2).1-(chartProject b swap e.1).1| :=
    (Finset.mem_filter.mp he).2.2
  have hstriprich (e : Point3 × Point3) (he : e∈GC) :
      m ≤ ((stripPoints Q (chartProject b swap) rho e).card : ℝ) := by
    have hsub : physicalPairTube3 Q rho e⊆stripPoints Q (chartProject b swap) rho e := by
      intro x hx
      obtain ⟨hxQ,hxtube⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxQ,?_⟩
      exact original_pair_tube_scalar_strip b swap e.1 e.2 x rho (hneC e he) (hmaxC e he) hxtube
    exact (hrich e (hchartG he)).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have hchartbudget : 240000*sliceEnergy Q Delta*ell^2 ≤ m^2*GC.card := by
    have hh := mul_le_mul_of_nonneg_left hchartkeepR (sq_nonneg m)
    nlinarith only [hbudget,hh]
  obtain ⟨G',hG'GC,hkeep,hpop⟩ := exists_original_core_rich_planar_graph Q S GC b swap
    c Delta rho m ell hDelta hDelta1 hrhoDelta hm hSQ hGC hbox hslab hneC hmaxC hstriprich hchartbudget
  refine ⟨G',hG'GC.trans hchartG,?_,?_⟩
  · linarith only [hchartkeepR,hkeep]
  · intro e he
    have heC := hG'GC he
    have heG := hchartG heC
    obtain ⟨hep,heq⟩ := Finset.mem_product.mp (hG heG)
    have hsub : tubePoints S (chartProject b swap) Delta
        (cellMap (chartProject b swap) Delta e)⊆physicalPairTube3 S (32*Delta) e := by
      intro x hx
      obtain ⟨hxS,hxcell⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS,?_⟩
      exact original_projected_cell_tube_lifts b swap e.1 e.2 x c rho Delta r hrho hr
        hDelta hDelta1 hsmall (hbox e.1 (hSQ hep)) (hbox e.2 (hSQ heq))
        (hbox x (hSQ hxS)) (hraw e heG).1 (hraw e heG).2 (hslab x (hSQ hxS))
        (hsep e heG) (hmaxC e heC) hxcell
    exact (hpop e he).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))

end OriginalThreeDimensionalPhysicalCoreRichness
