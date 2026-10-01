import Theorems.Thm_StickyKakeya4_measurable_selector_parametrization

open MeasureTheory Set

namespace StickyKakeya4

/-- The physical unit front, parametrized by a unit direction and displacement
inside the retained affine fibre interval. -/
noncomputable def frontParametrization
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ({theta : E4 // ‖theta‖ = 1} × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) → E4 :=
  fun z =>
    let line := selectorLine selector hmeasurable hvalid hselector z.1
    offset line + (mark line + (z.2 : ℝ)) • direction line

theorem measurable_frontParametrization
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (frontParametrization selector hmeasurable hvalid hselector) := by
  have hline : Measurable (fun z :
      {theta : E4 // ‖theta‖ = 1} × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      ((selectorLine selector hmeasurable hvalid hselector z.1 : selector) : MarkedLine)) :=
    measurable_subtype_coe.comp
      ((measurable_selectorLine selector hmeasurable hvalid hselector).comp measurable_fst)
  have ht : Measurable (fun z :
      {theta : E4 // ‖theta‖ = 1} × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact hline.fst.snd.add ((hline.snd.add ht).smul hline.fst.fst)

/-- The measurable parametrization has exactly the physical front as its
range; in particular it does not forget the affine fibre mark. -/
theorem range_frontParametrization
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Set.range (frontParametrization selector hmeasurable hvalid hselector) =
      unitFront selector := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨selectorLine selector hmeasurable hvalid hselector z.1,
      (selectorLine selector hmeasurable hvalid hselector z.1).property,
      (z.2 : ℝ), z.2.property, rfl⟩
  · rintro ⟨line, hline, t, ht, rfl⟩
    let theta : {theta : E4 // ‖theta‖ = 1} :=
      ⟨direction line, (hvalid line hline).1⟩
    obtain ⟨chosen, hchosen, hunique⟩ :=
      hselector (direction line) (hvalid line hline).1
    have hsame :
        (selectorLine selector hmeasurable hvalid hselector theta : MarkedLine) = line :=
      (hunique _ ⟨(selectorLine selector hmeasurable hvalid hselector theta).property,
        direction_selectorLine selector hmeasurable hvalid hselector theta⟩).trans
        (hunique line ⟨hline, rfl⟩).symm
    refine ⟨⟨theta, ⟨t, ht⟩⟩, ?_⟩
    simp [frontParametrization, hsame]

end StickyKakeya4
