import Definitions.Def_sticky_kakeya4_core

open MeasureTheory Set

namespace StickyKakeya4

/-- The direction projection restricted to a measurable one-line-per-direction
selector is a measurable embedding.  This is the Lusin--Souslin step needed
to make the inverse direction parametrization measurable. -/
theorem selector_direction_measurableEmbedding
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    MeasurableEmbedding (selector.domRestrict direction) := by
  apply ContinuousOn.measurableEmbedding hmeasurable
  · exact (continuous_fst.comp continuous_fst).continuousOn
  · intro line₁ hline₁ line₂ hline₂ hdir
    obtain ⟨line, hline, hunique⟩ :=
      hselector (direction line₁) (hvalid line₁ hline₁).1
    exact (hunique line₁ ⟨hline₁, rfl⟩).trans
      (hunique line₂ ⟨hline₂, hdir.symm⟩).symm

/-- The image of the selector direction projection is exactly the unit
sphere. -/
theorem range_selector_direction
    (selector : Set MarkedLine)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Set.range (selector.domRestrict direction) = {theta : E4 | ‖theta‖ = 1} := by
  ext theta
  constructor
  · rintro ⟨line, rfl⟩
    exact (hvalid line.1 line.2).1
  · intro htheta
    obtain ⟨line, ⟨hline, hdir⟩, _⟩ := hselector theta htheta
    exact ⟨⟨line, hline⟩, hdir⟩

/-- Regard a unit direction as a point in the range of the selector's
direction projection. -/
def sphereAsSelectorDirectionRange
    (selector : Set MarkedLine)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (theta : {theta : E4 // ‖theta‖ = 1}) :
    Set.range (selector.domRestrict direction) :=
  ⟨theta.1, by
    rw [range_selector_direction selector hvalid hselector]
    exact theta.2⟩

theorem measurable_sphereAsSelectorDirectionRange
    (selector : Set MarkedLine)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (sphereAsSelectorDirectionRange selector hvalid hselector) := by
  exact
    (measurable_subtype_coe :
      Measurable (fun theta : {theta : E4 // ‖theta‖ = 1} => (theta : E4))).subtype_mk

/-- The canonical measurable line selected by a unit direction. -/
noncomputable def selectorLine
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    {theta : E4 // ‖theta‖ = 1} → selector :=
  (selector_direction_measurableEmbedding selector hmeasurable hvalid hselector).equivRange.symm ∘
    sphereAsSelectorDirectionRange selector hvalid hselector

theorem measurable_selectorLine
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (selectorLine selector hmeasurable hvalid hselector) := by
  exact
    (selector_direction_measurableEmbedding selector hmeasurable hvalid hselector).equivRange.symm.measurable.comp
      (measurable_sphereAsSelectorDirectionRange selector hvalid hselector)

theorem direction_selectorLine
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (theta : {theta : E4 // ‖theta‖ = 1}) :
    direction (selectorLine selector hmeasurable hvalid hselector theta) = theta := by
  have hinverse :=
    (selector_direction_measurableEmbedding selector hmeasurable hvalid hselector).equivRange.apply_symm_apply
      (sphereAsSelectorDirectionRange selector hvalid hselector theta)
  have hval := congrArg Subtype.val hinverse
  rw [MeasurableEmbedding.equivRange_apply] at hval
  change
    direction
        ((selector_direction_measurableEmbedding selector hmeasurable hvalid hselector).equivRange.symm
          (sphereAsSelectorDirectionRange selector hvalid hselector theta) : selector) = (theta : E4)
  exact hval

end StickyKakeya4
