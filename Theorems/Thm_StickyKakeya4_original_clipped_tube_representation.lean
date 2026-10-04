import Theorems.Thm_StickyKakeya4_original_clipped_unit_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalClippedTubeRepresentation
open OriginalPairStripGeometry OriginalUnitLineParameters OriginalClippedUnitTube

def rectanglePoint (z : Pair) (t s : ℝ) : Point :=
  ((corePoint z t).1+s*unitX z,(corePoint z t).2+s*unitY z)

/-- The displayed clipped set is exactly the unit-length-coordinate
Euclidean rectangle on the original unit normal and perpendicular. -/
theorem original_clipped_rectangle_representation (z : Pair) (hz : z.1≠z.2)
    (w : ℝ) (p : Point) :
    p∈clippedTube z w ↔ ∃ t s : ℝ, |t|≤1 ∧ |s|≤w ∧ p=rectanglePoint z t s := by
  have hunit := original_unit_normal_square z hz
  have hcoord (t s : ℝ) : scaledResidual z (rectanglePoint z t s)=s ∧
      longitudinal z (rectanglePoint z t s)=t := by
    constructor
    · calc
        _ = (unitOffset z/2+s)*(unitX z^2+unitY z^2)-unitOffset z/2 := by
          dsimp [scaledResidual,rectanglePoint,corePoint]; ring
        _ = s := by rw [hunit]; ring
    · calc
        _ = t*(unitX z^2+unitY z^2) := by
          dsimp [longitudinal,rectanglePoint,corePoint]; ring
        _ = t := by rw [hunit,mul_one]
  constructor
  · intro hp
    refine ⟨longitudinal z p,scaledResidual z p,hp.2,hp.1,?_⟩
    apply Prod.ext
    · calc
        p.1 = p.1*(unitX z^2+unitY z^2) := by rw [hunit,mul_one]
        _ = _ := by dsimp [rectanglePoint,corePoint,longitudinal,scaledResidual]; ring
    · calc
        p.2 = p.2*(unitX z^2+unitY z^2) := by rw [hunit,mul_one]
        _ = _ := by dsimp [rectanglePoint,corePoint,longitudinal,scaledResidual]; ring
  · rintro ⟨t,s,ht,hs,rfl⟩
    exact ⟨by simpa only [(hcoord t s).1] using hs,by simpa only [(hcoord t s).2] using ht⟩

theorem original_half_point_injective : Function.Injective halfPoint := by
  intro p q heq
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  apply Prod.ext
  · change p.1/2=q.1/2 at h1
    linarith only [h1]
  · change p.2/2=q.2/2 at h2
    linarith only [h2]

/-- The fixed spatial normalization preserves exact ORIGINAL shading mass. -/
theorem original_half_shading_card (Pts : Finset Point) :
    (Pts.image halfPoint).card=Pts.card := by
  classical
  exact Finset.card_image_of_injective _ original_half_point_injective

end OriginalClippedTubeRepresentation
