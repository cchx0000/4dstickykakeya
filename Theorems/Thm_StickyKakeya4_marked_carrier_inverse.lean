import Theorems.Thm_StickyKakeya4_front_parameter_probability
import Theorems.Thm_StickyKakeya4_selector_carrier_measure

open MeasureTheory Set

noncomputable section

namespace StickyKakeya4

theorem selector_nonempty
    (selector : Set MarkedLine)
    (hselector : IsDirectionSelector selector) : Nonempty selector := by
  let e : E4 := EuclideanSpace.single (0 : Fin 4) 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨line, hline, _⟩ := hselector e he
  exact ⟨⟨line, hline.1⟩⟩

/-- The measurable inverse of the selector's carrier embedding.  Outside the
carrier it takes the harmless default supplied by `invFun`; on the carrier it
recovers the unique marked selector line, including its affine mark. -/
noncomputable def selectorLineFromCarrier
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : E4 × E4 → selector := by
  letI : Nonempty selector := selector_nonempty selector hselector
  exact
    (selector_carrierProjection_measurableEmbedding
      selector hmeasurable hvalid hselector).invFun

theorem measurable_selectorLineFromCarrier
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (selectorLineFromCarrier selector hmeasurable hvalid hselector) := by
  letI : Nonempty selector := selector_nonempty selector hselector
  exact
    (selector_carrierProjection_measurableEmbedding
      selector hmeasurable hvalid hselector).measurable_invFun

/-- On the genuine carrier, the inverse line has exactly the requested
direction and offset. -/
theorem carrier_selectorLineFromCarrier
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (carrier : E4 × E4) (hcarrier : carrier ∈ lineCarrier selector) :
    (direction (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier),
      offset (selectorLineFromCarrier selector hmeasurable hvalid hselector carrier)) =
      carrier := by
  letI : Nonempty selector := selector_nonempty selector hselector
  let f := selector.domRestrict (fun line => (direction line, offset line))
  have hex : ∃ line : selector, f line = carrier := by
    rcases hcarrier with ⟨line, hline, rfl⟩
    exact ⟨⟨line, hline⟩, rfl⟩
  let hf := selector_carrierProjection_measurableEmbedding
    selector hmeasurable hvalid hselector
  change f (hf.invFun carrier) = carrier
  obtain ⟨line, rfl⟩ := hex
  rw [hf.leftInverse_invFun line]

/-- Physical front coordinates rebuilt from carrier coordinates and a fibre
displacement.  The recovered selector line supplies the affine mark. -/
noncomputable def markedCarrierFrontParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ((E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) → E4 :=
  fun z =>
    let line := selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
    offset line + (mark line + (z.2 : ℝ)) • direction line

theorem measurable_markedCarrierFrontParam
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable (markedCarrierFrontParam selector hmeasurable hvalid hselector) := by
  have hline : Measurable (fun z :
      (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      ((selectorLineFromCarrier selector hmeasurable hvalid hselector z.1 : selector) :
        MarkedLine)) :=
    measurable_subtype_coe.comp
      ((measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector).comp
        measurable_fst)
  have ht : Measurable (fun z :
      (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) =>
      (z.2 : ℝ)) := measurable_subtype_coe.comp measurable_snd
  exact hline.fst.snd.add ((hline.snd.add ht).smul hline.fst.fst)

theorem markedCarrierFrontParam_mem_unitFront
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (z : (E4 × E4) × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    markedCarrierFrontParam selector hmeasurable hvalid hselector z ∈
      unitFront selector := by
  let line := selectorLineFromCarrier selector hmeasurable hvalid hselector z.1
  exact ⟨line, line.property, (z.2 : ℝ), z.2.property, rfl⟩

end StickyKakeya4
