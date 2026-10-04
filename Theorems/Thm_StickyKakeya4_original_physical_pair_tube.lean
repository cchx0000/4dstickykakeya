import Theorems.Thm_StickyKakeya4_original_pair_strip_geometry
import Theorems.Thm_StickyKakeya4_native_rich_pair_tube_family
import Theorems.Thm_StickyKakeya4_planar_frostman_ball_conversion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

noncomputable section
namespace OriginalPhysicalPairTube
open OriginalPairStripGeometry NativeRichPairTubeFamily PlanarFrostmanBallConversion

/-- Actual original points at Euclidean distance at most Delta from a point
of the genuine affine line through the original ordered pair. -/
def physicalPairTube (Pts : Finset Point) (Delta : ℝ) (z : Pair) : Finset Point := by
  classical
  exact Pts.filter (fun p => ∃ s : ℝ, euclideanDistance (linePoint z s) p≤Delta)

/-- Coordinate bounds follow from the literal Euclidean distance formula. -/
theorem coordinates_le_euclidean (p q : Point) :
    |q.1-p.1|≤euclideanDistance p q ∧ |q.2-p.2|≤euclideanDistance p q := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [sq_abs (q.1-p.1),sq_nonneg (q.2-p.2)]
  · apply Real.le_sqrt_of_sq_le
    nlinarith only [sq_abs (q.2-p.2),sq_nonneg (q.1-p.1)]

/-- Physical pair tubes are covered by twice-width normalized strips;
no rounded line, direction center, or substitute pair is used. -/
theorem physical_pair_tube_subset (Pts : Finset Point) (Delta : ℝ) (z : Pair)
    (hne : z.1≠z.2) :
    physicalPairTube Pts Delta z⊆pairSupport Pts (2*Delta) z := by
  classical
  intro p hp
  obtain ⟨hpP,s,hs⟩ := Finset.mem_filter.mp hp
  have hcoords := coordinates_le_euclidean (linePoint z s) p
  exact Finset.mem_filter.mpr ⟨hpP,near_original_pair_line z hne p s Delta
    (hcoords.1.trans hs) (hcoords.2.trans hs)⟩

theorem physical_pair_tube_card (Pts : Finset Point) (Delta : ℝ) (z : Pair)
    (hne : z.1≠z.2) :
    (physicalPairTube Pts Delta z).card≤(pairSupport Pts (2*Delta) z).card :=
  Finset.card_le_card (physical_pair_tube_subset Pts Delta z hne)

end OriginalPhysicalPairTube
