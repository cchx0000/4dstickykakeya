import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface
import Theorems.Thm_StickyKakeya4_dimension_witness_extraction
import Theorems.Thm_StickyKakeya4_carrier_piece_probability
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

open Filter MeasureTheory Set Metric Module
open scoped ENNReal Function RealInnerProductSpace InnerProductSpace Topology

namespace StickyKakeya4

/-!
Finite counting lemmas for the cover-adapted carrier pruning.  They are
stated independently of geometry so the dyadic line-parameter cells used in
the readback can instantiate them directly.
-/

/-- Continuous half-mass truncation for the cover-layer readback.  If an
activity function takes values in `[0,1]`, then the directions on which its
activity is at least half of its mean carry at least half of that mean.  This
is the measure-theoretic replacement for an abstract active-direction
hypothesis: in the marked-line application `activity line` is the normalized
fibre time assigned to the selected Hausdorff-cover layer. -/
theorem probability_measure_active_half_mass
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (activity : X → ENNReal)
    (hmeasurable : Measurable activity)
    (hbounded : ∀ x, activity x ≤ 1) :
    (∫⁻ x, activity x ∂mu) / 2 ≤
      mu {x | (∫⁻ y, activity y ∂mu) / 2 ≤ activity x} := by
  let mass : ENNReal := ∫⁻ x, activity x ∂mu
  let active : Set X := {x | mass / 2 ≤ activity x}
  have hactive : MeasurableSet active := by
    exact measurableSet_le measurable_const hmeasurable
  have hmass_le_one : mass ≤ 1 := by
    calc
      mass = ∫⁻ x, activity x ∂mu := rfl
      _ ≤ ∫⁻ _x : X, (1 : ENNReal) ∂mu :=
        lintegral_mono hbounded
      _ = 1 := by simp
  have hmass_ne_top : mass ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hmass_le_one
  have hactivePart :
      (∫⁻ x in active, activity x ∂mu) ≤ mu active := by
    calc
      (∫⁻ x in active, activity x ∂mu) ≤
          ∫⁻ _x : X in active, (1 : ENNReal) ∂mu := by
        exact lintegral_mono hbounded
      _ = mu active := setLIntegral_one active
  have hinactivePart :
      (∫⁻ x in activeᶜ, activity x ∂mu) ≤ mass / 2 := by
    calc
      (∫⁻ x in activeᶜ, activity x ∂mu) ≤
          ∫⁻ _x : X in activeᶜ, mass / 2 ∂mu := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hactive.compl] with x hx
        exact le_of_not_ge hx
      _ = (mass / 2) * mu activeᶜ := by
        rw [lintegral_const]
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp
      _ ≤ (mass / 2) * 1 := by
        gcongr
        calc
          mu activeᶜ ≤ mu Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      _ = mass / 2 := by simp
  have hsplit :
      mass = (∫⁻ x in active, activity x ∂mu) +
        ∫⁻ x in activeᶜ, activity x ∂mu := by
    calc
      mass = ∫⁻ x, activity x
          ∂(mu.restrict active + mu.restrict activeᶜ) := by
        rw [Measure.restrict_add_restrict_compl hactive]
      _ = (∫⁻ x in active, activity x ∂mu) +
          ∫⁻ x in activeᶜ, activity x ∂mu :=
        lintegral_add_measure activity
          (mu.restrict active) (mu.restrict activeᶜ)
  have htotal : mass ≤ mu active + mass / 2 := by
    calc
      mass = (∫⁻ x in active, activity x ∂mu) +
          ∫⁻ x in activeᶜ, activity x ∂mu := hsplit
      _ ≤ mu active + mass / 2 := add_le_add hactivePart hinactivePart
  have hhalf_ne_top : mass / 2 ≠ ⊤ :=
    ENNReal.div_ne_top hmass_ne_top (by norm_num)
  have hcancel : mass / 2 ≤ mu active := by
    apply (ENNReal.add_le_add_iff_right hhalf_ne_top).mp
    simpa only [ENNReal.add_halves] using htotal
  simpa only [mass, active] using hcancel

/-- Fibre times at which a marked line visits an arbitrary physical target.
The definition is written as a section of `markedLineFibreFrontParam`; this
makes the Fubini measurability needed by the cover-layer argument explicit. -/
def markedLineSetFibreSet
    (line : MarkedLine) (target : Set E4) :
    Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  Prod.mk line ⁻¹' (markedLineFibreFrontParam ⁻¹' target)

theorem measurableSet_markedLineSetFibreSet
    (line : MarkedLine) {target : Set E4}
    (htarget : MeasurableSet target) :
    MeasurableSet (markedLineSetFibreSet line target) := by
  exact (htarget.preimage measurable_markedLineFibreFrontParam).preimage
    (measurable_const.prodMk measurable_id)

/-- The fibre-time spent in a measurable physical layer is a measurable
function of the marked line. -/
theorem measurable_markedLineSetFibreProbability
    {target : Set E4} (htarget : MeasurableSet target) :
    Measurable fun line : MarkedLine =>
      (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet line target) := by
  let S : Set (MarkedLine × Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
    markedLineFibreFrontParam ⁻¹' target
  have hS : MeasurableSet S :=
    htarget.preimage measurable_markedLineFibreFrontParam
  have hm := measurable_measure_prodMk_left
    (ν := (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))) hS
  simpa [S, markedLineSetFibreSet, markedLineFibreFrontParam] using hm

/-- Fubini readback for an arbitrary measurable cover layer: its physical
mass is the mean, over the normalized marked-line law, of the assigned fibre
time. -/
theorem markedCarrierPieceFrontProbability_apply_eq_lintegral
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) (target : Set E4)
    (htarget : MeasurableSet target) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target =
      ∫⁻ line, (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet line target)
        ∂(markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
          Measure MarkedLine) := by
  rw [← markedCarrierPieceLineFrontProbability_eq selector hmeasurable hvalid
    hselector piece]
  rw [markedCarrierPieceLineFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_markedLineFibreFrontParam htarget]
  rw [ProbabilityMeasure.toMeasure_prod]
  rw [Measure.prod_apply
    (htarget.preimage measurable_markedLineFibreFrontParam)]
  rfl

/-- Fubini readback for the canonical direction--fibre front probability.
The outer variable is the actual unit direction and the inner section is the
time spent by its uniquely selected marked line in the physical target. -/
theorem selectorFrontProbability_apply_eq_lintegral
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (target : Set E4) (htarget : MeasurableSet target) :
    (selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) target =
      ∫⁻ theta,
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet
            ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
              MarkedLine) target)
        ∂(normSphereProbability :
          Measure {theta : E4 // ‖theta‖ = 1}) := by
  rw [selectorFrontProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_frontParametrization selector hmeasurable hvalid hselector)
    htarget]
  rw [frontParameterProbability, ProbabilityMeasure.toMeasure_prod]
  rw [Measure.prod_apply
    (htarget.preimage
      (measurable_frontParametrization selector hmeasurable hvalid hselector))]
  rfl

/-- A measurable physical layer of the canonical selector front retains half
its mass on directions whose marked fibre spends at least half the mean time
inside that layer. -/
theorem selector_active_directions_half_front_mass
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (target : Set E4) (htarget : MeasurableSet target) :
    (selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) target / 2 ≤
      (normSphereProbability :
        Measure {theta : E4 // ‖theta‖ = 1})
        {theta |
          (selectorFrontProbability selector hmeasurable hvalid hselector :
              Measure E4) target / 2 ≤
            (fibreIntervalProbability :
              Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
              (markedLineSetFibreSet
                ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
                  MarkedLine) target)} := by
  let activity : {theta : E4 // ‖theta‖ = 1} → ENNReal := fun theta =>
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
      (markedLineSetFibreSet
        ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
          MarkedLine) target)
  have hlineMeasurable : Measurable fun theta : {theta : E4 // ‖theta‖ = 1} =>
      ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
        MarkedLine) :=
    measurable_subtype_coe.comp
      (measurable_selectorLine selector hmeasurable hvalid hselector)
  have hactivityMeasurable : Measurable activity :=
    (measurable_markedLineSetFibreProbability htarget).comp hlineMeasurable
  have hactivityBounded : ∀ theta, activity theta ≤ 1 := by
    intro theta
    calc
      activity theta ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hhalf := probability_measure_active_half_mass
    (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
    activity hactivityMeasurable hactivityBounded
  have hmean : (∫⁻ theta, activity theta
      ∂(normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})) =
      (selectorFrontProbability selector hmeasurable hvalid hselector :
        Measure E4) target := by
    exact (selectorFrontProbability_apply_eq_lintegral
      selector hmeasurable hvalid hselector target htarget).symm
  rw [hmean] at hhalf
  exact hhalf

/-- A measurable cover layer canonically produces its active marked lines.
The active threshold and the retained line mass are both half the actual
physical layer mass, so no independent active-direction hypothesis remains. -/
theorem markedCarrierPiece_active_lines_half_front_mass
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) (target : Set E4)
    (htarget : MeasurableSet target) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target / 2 ≤
      (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
        Measure MarkedLine)
        {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) target / 2 ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineSetFibreSet line target)} := by
  let mu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let activity : MarkedLine → ENNReal := fun line =>
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
      (markedLineSetFibreSet line target)
  have hactivityMeasurable : Measurable activity := by
    exact measurable_markedLineSetFibreProbability htarget
  have hactivityBounded : ∀ line, activity line ≤ 1 := by
    intro line
    calc
      activity line ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hhalf := probability_measure_active_half_mass
    mu activity hactivityMeasurable hactivityBounded
  have hmean : (∫⁻ line, activity line ∂mu) =
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid
        hselector piece : Measure E4) target := by
    exact (markedCarrierPieceFrontProbability_apply_eq_lintegral
      selector hmeasurable hvalid hselector piece target htarget).symm
  rw [hmean] at hhalf
  exact hhalf

/-- A finite cover converts a uniform mass cap into a cardinality bound.  No
measurability of the covering sets is required: finite subadditivity is an
outer-measure statement.  This is the continuous analogue of the finite
assignment-fibre count used below. -/
theorem measure_le_card_mul_of_finite_cover
    {alpha beta : Type*} [MeasurableSpace alpha]
    (nu : Measure alpha) (active : Set alpha)
    (centers : Finset beta) (cover : beta → Set alpha) (cap : ENNReal)
    (hsubset : active ⊆ ⋃ b ∈ centers, cover b)
    (hcap : ∀ b ∈ centers, nu (cover b) ≤ cap) :
    nu active ≤ (centers.card : ENNReal) * cap := by
  calc
    nu active ≤ nu (⋃ b ∈ centers, cover b) := measure_mono hsubset
    _ ≤ ∑ b ∈ centers, nu (cover b) := measure_biUnion_finset_le centers cover
    _ ≤ ∑ _b ∈ centers, cap := by
      exact Finset.sum_le_sum fun b hb => hcap b hb
    _ = (centers.card : ENNReal) * cap := by simp

/-- The canonical active marked lines supplied by the half-mass truncation
obey the exact finite counting inequality required for the WZ readback.  The
retained objects are marked lines, not bare directions, so their affine fibre
marks survive.  Once the active set is covered by their direction balls, a
uniform direction-ball cap pays for at least half of the physical layer mass.
-/
theorem markedCarrierPiece_active_mass_le_card_mul_direction_cap
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4)) (target : Set E4)
    (htarget : MeasurableSet target)
    (retained : Finset MarkedLine) (delta : ℝ) (cap : ENNReal)
    (hcover :
      {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) target / 2 ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineSetFibreSet line target)} ⊆
        ⋃ line ∈ retained, lineDirectionBall (direction line) delta)
    (hcap : ∀ line ∈ retained,
      (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
        Measure MarkedLine)
          (lineDirectionBall (direction line) delta) ≤ cap) :
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
      Measure E4) target / 2 ≤
      (retained.card : ENNReal) * cap := by
  calc
    (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target / 2 ≤
        (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
          Measure MarkedLine)
          {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                hselector piece : Measure E4) target / 2 ≤
            (fibreIntervalProbability :
              Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
              (markedLineSetFibreSet line target)} :=
      markedCarrierPiece_active_lines_half_front_mass selector hmeasurable hvalid
        hselector piece target htarget
    _ ≤ (retained.card : ENNReal) * cap :=
      measure_le_card_mul_of_finite_cover
        (markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece :
          Measure MarkedLine)
        {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
              hselector piece : Measure E4) target / 2 ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineSetFibreSet line target)}
        retained (fun line => lineDirectionBall (direction line) delta) cap hcover hcap

/-- Every finite family has an image-separated subfamily which still covers
the original family at the same scale.  The proof is nonrecursive: maximize
cardinality among the separated subfamilies, then maximality forces the net
property.  Keeping the domain `alpha` separate from the metric target `beta`
is important for the marked-line application, where points are retained
marked lines but separation is imposed only on their directions. -/
theorem exists_maximal_image_separated_subfamily
    {alpha beta : Type*} [PseudoMetricSpace beta]
    (points : Finset alpha) (image : alpha → beta)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      (∀ a ∈ retained, ∀ b ∈ retained,
        a ≠ b → delta ≤ dist (image a) (image b)) ∧
      ∀ a ∈ points, ∃ b ∈ retained, dist (image a) (image b) < delta := by
  classical
  let separatedSubfamilies : Finset (Finset alpha) :=
    points.powerset.filter fun family =>
      ∀ a ∈ family, ∀ b ∈ family,
        a ≠ b → delta ≤ dist (image a) (image b)
  have hempty : (∅ : Finset alpha) ∈ separatedSubfamilies := by
    simp [separatedSubfamilies]
  obtain ⟨retained, hretainedGood, hmaximal⟩ :=
    Finset.exists_max_image separatedSubfamilies
      (fun family => family.card) ⟨∅, hempty⟩
  have hretainedData := Finset.mem_filter.mp hretainedGood
  have hretained : retained ⊆ points :=
    Finset.mem_powerset.mp hretainedData.1
  have hseparated :
      ∀ a ∈ retained, ∀ b ∈ retained,
        a ≠ b → delta ≤ dist (image a) (image b) :=
    hretainedData.2
  refine ⟨retained, hretained, hseparated, ?_⟩
  intro a ha
  by_contra hnotCovered
  push Not at hnotCovered
  have haNotMem : a ∉ retained := by
    intro haRetained
    have := hnotCovered a haRetained
    simpa using (lt_of_lt_of_le hdelta this)
  have hinsertGood : insert a retained ∈ separatedSubfamilies := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.insert_subset ha hretained)
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact (hxy rfl).elim
        · exact hnotCovered y hy
      · rcases hy with rfl | hy
        · simpa [dist_comm] using hnotCovered x hx
        · exact hseparated x hx y hy hxy
  have hcardMax := hmaximal (insert a retained) hinsertGood
  have hstrictCard : retained.card < (insert a retained).card := by
    simp [haNotMem]
  exact (not_lt_of_ge hcardMax) hstrictCard

/-- Marked-line specialization of the maximal-net lemma.  The retained
objects keep their affine-fibre marks, while the separation and covering
statements are exactly in the direction metric required by the finite WZ
interface. -/
theorem exists_direction_separated_marked_subfamily
    (lines : Finset MarkedLine) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ retained : Finset MarkedLine,
      retained ⊆ lines ∧
      (∀ line ∈ retained, ∀ line' ∈ retained,
        line ≠ line' →
          delta ≤ dist (direction line) (direction line')) ∧
      ∀ line ∈ lines, ∃ line' ∈ retained,
        dist (direction line) (direction line') < delta := by
  exact exists_maximal_image_separated_subfamily lines direction hdelta

/-- Every set of valid marked lines admits a finite direction net whose
centers are actual members of the set.  Compactness is used only after
projecting to the unit direction sphere.  A finite set of direction centers
is first chosen inside the direction image, and finite surjective choice then
lifts each center back to an active marked line.  Consequently the affine
marks of the selected centers are genuine active marks. -/
theorem exists_finite_marked_direction_cover
    (active : Set MarkedLine)
    (hvalid : ∀ line ∈ active, IsValidLine line)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ retained : Finset MarkedLine,
      (↑retained : Set MarkedLine) ⊆ active ∧
      (∀ line ∈ retained, IsValidLine line) ∧
      active ⊆ ⋃ line ∈ retained,
        lineDirectionBall (direction line) delta := by
  classical
  have himageSphere :
      direction '' active ⊆ Metric.sphere (0 : E4) 1 := by
    rintro theta ⟨line, hline, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact (hvalid line hline).1
  have hclosureCompact : IsCompact (closure (direction '' active)) := by
    apply (isCompact_sphere (0 : E4) 1).of_isClosed_subset isClosed_closure
    exact closure_minimal himageSphere Metric.isClosed_sphere
  obtain ⟨t, htimage, htfinite, htcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hclosureCompact hdelta
  let dirs : Finset E4 := htfinite.toFinset
  let domain : Set MarkedLine :=
    active ∩ direction ⁻¹' (↑dirs : Set E4)
  have hsurj : domain.SurjOn direction (↑dirs : Set E4) := by
    intro theta htheta
    have hthetaT : theta ∈ t := by
      simpa [dirs] using htheta
    obtain ⟨line, hline, hdirection⟩ := htimage hthetaT
    refine ⟨line, ?_, hdirection⟩
    constructor
    · exact hline
    · change direction line ∈ (↑dirs : Set E4)
      rw [hdirection]
      exact htheta
  obtain ⟨retained, hretainedDomain, _hinj, himageEq⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn domain dirs hsurj
  refine ⟨retained, ?_, ?_, ?_⟩
  · intro line hline
    exact (hretainedDomain hline).1
  · intro line hline
    exact hvalid line ((hretainedDomain hline).1)
  · intro line hline
    have hdirimage : direction line ∈ direction '' active :=
      ⟨line, hline, rfl⟩
    have hcovered := htcover hdirimage
    simp only [Set.mem_iUnion] at hcovered ⊢
    obtain ⟨theta, hthetaT, hthetaBall⟩ := hcovered
    have hthetaDirs : theta ∈ dirs := by
      simpa [dirs] using hthetaT
    have hthetaImage : theta ∈ retained.image direction := by
      rw [himageEq]
      exact hthetaDirs
    obtain ⟨rep, hrep, hrepDirection⟩ := Finset.mem_image.mp hthetaImage
    refine ⟨rep, hrep, ?_⟩
    change dist (direction line) (direction rep) < delta
    change dist (direction line) theta < delta at hthetaBall
    simpa [hrepDirection] using hthetaBall

/-- Maximal-net pruning of the preceding compact direction cover.  The
returned active marked lines are pairwise direction-separated at scale
`delta`, and their direction balls of radius `2 * delta` cover the entire
active set.  Both the separation and the factor two are explicit. -/
theorem exists_direction_separated_active_marked_cover
    (active : Set MarkedLine)
    (hvalid : ∀ line ∈ active, IsValidLine line)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ retained : Finset MarkedLine,
      (↑retained : Set MarkedLine) ⊆ active ∧
      (∀ line ∈ retained, ∀ line' ∈ retained,
        line ≠ line' →
          delta ≤ dist (direction line) (direction line')) ∧
      active ⊆ ⋃ line ∈ retained,
        lineDirectionBall (direction line) (2 * delta) := by
  obtain ⟨lines, hlinesActive, _hlinesValid, hactiveCover⟩ :=
    exists_finite_marked_direction_cover active hvalid hdelta
  obtain ⟨retained, hretained, hseparated, hlinesCover⟩ :=
    exists_direction_separated_marked_subfamily lines hdelta
  refine ⟨retained, ?_, hseparated, ?_⟩
  · intro line hline
    exact hlinesActive (hretained hline)
  · intro line hline
    have hcovered := hactiveCover hline
    simp only [Set.mem_iUnion] at hcovered ⊢
    obtain ⟨old, holdLines, hlineOld⟩ := hcovered
    obtain ⟨new, hnewRetained, holdNew⟩ := hlinesCover old holdLines
    refine ⟨new, hnewRetained, ?_⟩
    change dist (direction line) (direction new) < 2 * delta
    calc
      dist (direction line) (direction new) ≤
          dist (direction line) (direction old) +
            dist (direction old) (direction new) := dist_triangle _ _ _
      _ < delta + delta := add_lt_add hlineOld holdNew
      _ = 2 * delta := by ring

/-- Canonical selector-front concentration produces a finite family of actual
marked selector lines.  They are separated at the physical tube scale, every
retained line has the required active fibre-time mass, and the cubic sphere-cap
bound converts half of the physical layer mass into a cardinality lower bound. -/
theorem selector_exists_separated_active_family_with_count
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (target : Set E4) (htarget : MeasurableSet target)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : 4 * delta ≤ 1) :
    ∃ retained : Finset MarkedLine,
      (↑retained : Set MarkedLine) ⊆
        selector ∩
          {line |
            (selectorFrontProbability selector hmeasurable hvalid hselector :
                Measure E4) target / 2 ≤
              (fibreIntervalProbability :
                Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
                (markedLineSetFibreSet line target)} ∧
      (∀ line ∈ retained, ∀ line' ∈ retained, line ≠ line' →
        2 * delta ≤ dist (direction line) (direction line')) ∧
      (selectorFrontProbability selector hmeasurable hvalid hselector :
          Measure E4) target / 2 ≤
        (retained.card : ENNReal) *
          (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3) := by
  let mu : Measure E4 :=
    selectorFrontProbability selector hmeasurable hvalid hselector
  let activeLines : Set MarkedLine :=
    selector ∩
      {line |
        mu target / 2 ≤
          (fibreIntervalProbability :
            Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineSetFibreSet line target)}
  have hvalidActive : ∀ line ∈ activeLines, IsValidLine line := by
    intro line hline
    exact hvalid line hline.1
  obtain ⟨retained, hretained, hseparated, hcoverLines⟩ :=
    exists_direction_separated_active_marked_cover
      activeLines hvalidActive (show 0 < 2 * delta by positivity)
  let activeDirections : Set {theta : E4 // ‖theta‖ = 1} :=
    {theta |
      mu target / 2 ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineSetFibreSet
            ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
              MarkedLine) target)}
  let center : retained → {theta : E4 // ‖theta‖ = 1} := fun line =>
    ⟨direction (line : MarkedLine),
      (hvalidActive line (hretained line.property)).1⟩
  have hcoverDirections : activeDirections ⊆
      ⋃ line ∈ (retained.attach : Set retained),
        Metric.ball (center line) (4 * delta) := by
    intro theta htheta
    let chosen : MarkedLine :=
      ((selectorLine selector hmeasurable hvalid hselector theta : selector) :
        MarkedLine)
    have hchosenActive : chosen ∈ activeLines := by
      refine ⟨(selectorLine selector hmeasurable hvalid hselector theta).property, ?_⟩
      exact htheta
    have hcovered := hcoverLines hchosenActive
    simp only [Set.mem_iUnion] at hcovered ⊢
    obtain ⟨line, hlineRetained, hclose⟩ := hcovered
    let lineSub : retained := ⟨line, hlineRetained⟩
    refine ⟨lineSub, ?_, ?_⟩
    · simp [lineSub]
    · change dist (theta : E4) (direction line) < 4 * delta
      change dist (direction chosen) (direction line) < 2 * (2 * delta) at hclose
      have hdirectionChosen : direction chosen = (theta : E4) := by
        exact direction_selectorLine selector hmeasurable hvalid hselector theta
      rw [hdirectionChosen] at hclose
      linarith
  have hcap : ∀ line ∈ retained.attach,
      (normSphereProbability :
        Measure {theta : E4 // ‖theta‖ = 1})
          (Metric.ball (center line) (4 * delta)) ≤
        metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3 := by
    intro line _hline
    exact normSphereProbability_ball_upper_bound
      (center line) (by positivity) hdeltaOne
  have hhalf : mu target / 2 ≤
      (normSphereProbability :
        Measure {theta : E4 // ‖theta‖ = 1}) activeDirections := by
    simpa [mu, activeDirections] using
      selector_active_directions_half_front_mass
        selector hmeasurable hvalid hselector target htarget
  have hcount : mu target / 2 ≤
      (retained.card : ENNReal) *
        (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3) := by
    calc
      mu target / 2 ≤
          (normSphereProbability :
            Measure {theta : E4 // ‖theta‖ = 1}) activeDirections := hhalf
      _ ≤ ((retained.attach).card : ENNReal) *
          (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3) :=
        measure_le_card_mul_of_finite_cover
          (normSphereProbability :
            Measure {theta : E4 // ‖theta‖ = 1})
          activeDirections retained.attach
          (fun line => Metric.ball (center line) (4 * delta))
          (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3)
          hcoverDirections hcap
      _ = (retained.card : ENNReal) *
          (metricSphereCapConstant * (ENNReal.ofReal (4 * delta)) ^ 3) := by simp
  refine ⟨retained, ?_, hseparated, ?_⟩
  · simpa [activeLines, mu] using hretained
  · simpa [mu] using hcount

/-- Complete continuous-to-finite active-direction readback for one physical
cover layer.  Intersecting the half-mass active set with the supported
selector lines loses no measure.  Compact direction pruning then returns
actual active marked lines which are `delta`-separated, and the cubic cap at
radius `2 * delta` converts the retained active mass into their cardinality.
No finite active-family hypothesis is assumed. -/
theorem markedCarrierPiece_exists_separated_active_family_with_count
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (piece : Set (E4 × E4))
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceCarrier : piece ⊆ lineCarrier selector)
    (hmass : (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) piece ≠ 0)
    (target : Set E4) (htarget : MeasurableSet target)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : 2 * delta ≤ 1) :
    ∃ retained : Finset MarkedLine,
      (↑retained : Set MarkedLine) ⊆
        selectorLinesOverCarrierPiece selector piece ∩
          {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
                hselector piece : Measure E4) target / 2 ≤
            (fibreIntervalProbability :
              Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
              (markedLineSetFibreSet line target)} ∧
      (∀ line ∈ retained, ∀ line' ∈ retained,
        line ≠ line' →
          delta ≤ dist (direction line) (direction line')) ∧
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target / 2 ≤
        (retained.card : ENNReal) *
          (carrierPieceDirectionCapConstant selector hmeasurable hvalid
            hselector piece * (ENNReal.ofReal (2 * delta)) ^ 3) := by
  let nu : Measure MarkedLine :=
    markedCarrierPieceLineProbability selector hmeasurable hvalid hselector piece
  let support : Set MarkedLine := selectorLinesOverCarrierPiece selector piece
  let broadActive : Set MarkedLine :=
    {line | (markedCarrierPieceFrontProbability selector hmeasurable hvalid
          hselector piece : Measure E4) target / 2 ≤
      (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineSetFibreSet line target)}
  let active : Set MarkedLine := support ∩ broadActive
  have hnuSupport : nu supportᶜ = 0 := by
    exact markedCarrierPieceLineProbability_apply_compl_eq_zero selector hmeasurable
      hvalid hselector piece hpieceMeasurable hpieceCarrier hmass
  have hhalfBroad :
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target / 2 ≤ nu broadActive := by
    exact markedCarrierPiece_active_lines_half_front_mass selector hmeasurable hvalid
      hselector piece target htarget
  have hbroadSubset : broadActive ⊆ active ∪ supportᶜ := by
    intro line hline
    by_cases hs : line ∈ support
    · exact Or.inl ⟨hs, hline⟩
    · exact Or.inr hs
  have hhalfActive :
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
        Measure E4) target / 2 ≤ nu active := by
    calc
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
          Measure E4) target / 2 ≤ nu broadActive := hhalfBroad
      _ ≤ nu (active ∪ supportᶜ) := measure_mono hbroadSubset
      _ ≤ nu active + nu supportᶜ := measure_union_le _ _
      _ = nu active := by rw [hnuSupport, add_zero]
  have hactiveValid : ∀ line ∈ active, IsValidLine line := by
    intro line hline
    exact hvalid line hline.1.1
  obtain ⟨retained, hretainedActive, hseparated, hcover⟩ :=
    exists_direction_separated_active_marked_cover active hactiveValid hdelta
  refine ⟨retained, ?_, hseparated, ?_⟩
  · simpa only [active, support, broadActive] using hretainedActive
  · calc
      (markedCarrierPieceFrontProbability selector hmeasurable hvalid hselector piece :
          Measure E4) target / 2 ≤ nu active := hhalfActive
      _ ≤ (retained.card : ENNReal) *
          (carrierPieceDirectionCapConstant selector hmeasurable hvalid
            hselector piece * (ENNReal.ofReal (2 * delta)) ^ 3) := by
        apply measure_le_card_mul_of_finite_cover nu active retained
          (fun line => lineDirectionBall (direction line) (2 * delta))
          (carrierPieceDirectionCapConstant selector hmeasurable hvalid
            hselector piece * (ENNReal.ofReal (2 * delta)) ^ 3)
          hcover
        intro line hline
        let theta : {theta : E4 // ‖theta‖ = 1} :=
          ⟨direction line, (hactiveValid line (hretainedActive hline)).1⟩
        simpa [nu, theta] using
          (markedCarrierPieceLineProbability_lineDirectionBall_upper_bound
            selector hmeasurable hvalid hselector piece hpieceMeasurable
            hpieceCarrier hmass theta (by linarith) hdeltaOne)

/-- Indexed form used by the finite marked partition.  Besides the retained
direction-separated indices, it returns an actual assignment of every old
cell to a retained direction within `delta`; this is the fibre map to which
the weighted counting lemma below is applied. -/
theorem exists_direction_separated_center_assignment
    {n : ℕ} (center : Fin n → MarkedLine)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ retained : Finset (Fin n),
      (∀ i ∈ retained, ∀ j ∈ retained,
        i ≠ j →
          delta ≤ dist (direction (center i)) (direction (center j))) ∧
      ∃ assign : Fin n → Fin n,
        (∀ i, assign i ∈ retained) ∧
        ∀ i, dist (direction (center i))
          (direction (center (assign i))) < delta := by
  obtain ⟨retained, _hretained, hseparated, hcover⟩ :=
    exists_maximal_image_separated_subfamily
      (Finset.univ : Finset (Fin n)) (fun i => direction (center i)) hdelta
  have hcover' :
      ∀ i : Fin n, ∃ j ∈ retained,
        dist (direction (center i)) (direction (center j)) < delta := by
    intro i
    exact hcover i (by simp)
  choose assign hassign hdist using hcover'
  exact ⟨retained, hseparated, assign, hassign, hdist⟩

/-- If a normalized finite weight is assigned to finitely many retained
centers and every assignment fibre has weight at most `cap`, then the number
of retained centers pays for the whole mass.  This is the exact finite
counting step used after the direction-cap estimate: it converts the weighted
marked partition into the lower cardinality bound needed by an unweighted WZ
direction family. -/
theorem one_le_card_mul_of_weighted_fiber_cap
    {alpha beta : Type*} [DecidableEq beta]
    (points : Finset alpha) (centers : Finset beta)
    (assign : alpha → beta) (weight : alpha → ENNReal) (cap : ENNReal)
    (hassign : ∀ a ∈ points, assign a ∈ centers)
    (htotal : (∑ a ∈ points, weight a) = 1)
    (hfiber : ∀ b ∈ centers,
      (∑ a ∈ points with assign a = b, weight a) ≤ cap) :
    1 ≤ (centers.card : ENNReal) * cap := by
  classical
  calc
    1 = ∑ a ∈ points, weight a := htotal.symm
    _ = ∑ b ∈ centers, ∑ a ∈ points with assign a = b, weight a := by
      exact (Finset.sum_fiberwise_of_maps_to hassign weight).symm
    _ ≤ ∑ _b ∈ centers, cap := by
      exact Finset.sum_le_sum fun b hb => hfiber b hb
    _ = (centers.card : ENNReal) * cap := by simp

/-- The cells assigned to one retained direction form a disjoint union inside
the direction ball of radius `2 * delta` around that retained center.  Thus a
single direction Frostman estimate controls the whole assignment fibre; no
loss proportional to the number of old cells is incurred. -/
theorem assignment_fiber_mass_le_direction_cap
    (nu : Measure MarkedLine) {n : ℕ}
    (center : Fin n → MarkedLine) (cell : Fin n → Set MarkedLine)
    (assign : Fin n → Fin n) (Cdir : ENNReal) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : 2 * delta ≤ 1)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    (hdirectionCell : ∀ i, ∀ line ∈ cell i,
      dist (direction line) (direction (center i)) < delta)
    (hassign : ∀ i, dist (direction (center i))
      (direction (center (assign i))) < delta)
    (hcap : ∀ theta : E4, ∀ r : ℝ, 0 < r → r ≤ 1 →
      nu (lineDirectionBall theta r) ≤ Cdir * (ENNReal.ofReal r) ^ 3)
    (j : Fin n) :
    (∑ i ∈ (Finset.univ.filter fun i => assign i = j), nu (cell i)) ≤
      Cdir * (ENNReal.ofReal (2 * delta)) ^ 3 := by
  let J : Finset (Fin n) := Finset.univ.filter fun i => assign i = j
  let U : Set MarkedLine := ⋃ i ∈ J, cell i
  have hJdisjoint : PairwiseDisjoint (↑J) cell := by
    intro i hi k hk hik
    exact hcellDisjoint hik
  have hmeasureU : nu U = ∑ i ∈ J, nu (cell i) := by
    exact measure_biUnion_finset hJdisjoint
      (fun i hi => hcellMeasurable i)
  have hUsubset : U ⊆ lineDirectionBall (direction (center j)) (2 * delta) := by
    intro line hline
    simp only [U, Set.mem_iUnion] at hline
    obtain ⟨i, hiJ, hlineCell⟩ := hline
    have hij : assign i = j := by
      simpa [J] using hiJ
    change dist (direction line) (direction (center j)) < 2 * delta
    calc
      dist (direction line) (direction (center j)) ≤
          dist (direction line) (direction (center i)) +
            dist (direction (center i)) (direction (center j)) :=
        dist_triangle _ _ _
      _ < delta + delta :=
        add_lt_add (hdirectionCell i line hlineCell)
          (by simpa [hij] using hassign i)
      _ = 2 * delta := by ring
  change (∑ i ∈ J, nu (cell i)) ≤ _
  rw [← hmeasureU]
  exact (measure_mono hUsubset).trans
    (hcap (direction (center j)) (2 * delta) (by linarith) hdeltaOne)

/-- A normalized weighted marked partition admits a direction-separated
retained subfamily whose cardinality pays for all of the mass.  This is the
finite weighted-to-unweighted conversion needed before invoking the WZ
estimate: the affine-marked centers themselves are retained, while only their
directions are separated. -/
theorem exists_direction_separated_centers_with_weighted_count
    (nu : Measure MarkedLine) {n : ℕ}
    (center : Fin n → MarkedLine) (cell : Fin n → Set MarkedLine)
    (Cdir : ENNReal) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : 2 * delta ≤ 1)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellDisjoint : Pairwise (fun i j => Disjoint (cell i) (cell j)))
    (hdirectionCell : ∀ i, ∀ line ∈ cell i,
      dist (direction line) (direction (center i)) < delta)
    (htotal : (∑ i, nu (cell i)) = 1)
    (hcap : ∀ theta : E4, ∀ r : ℝ, 0 < r → r ≤ 1 →
      nu (lineDirectionBall theta r) ≤ Cdir * (ENNReal.ofReal r) ^ 3) :
    ∃ retained : Finset (Fin n),
      (∀ i ∈ retained, ∀ j ∈ retained,
        i ≠ j → delta ≤
          dist (direction (center i)) (direction (center j))) ∧
      ∃ assign : Fin n → Fin n,
        (∀ i, assign i ∈ retained) ∧
        (∀ i, dist (direction (center i))
          (direction (center (assign i))) < delta) ∧
        1 ≤ (retained.card : ENNReal) *
          (Cdir * (ENNReal.ofReal (2 * delta)) ^ 3) := by
  obtain ⟨retained, hseparated, assign, hassignRetained, hassignClose⟩ :=
    exists_direction_separated_center_assignment center hdelta
  refine ⟨retained, hseparated, assign, hassignRetained, hassignClose, ?_⟩
  apply one_le_card_mul_of_weighted_fiber_cap
    (Finset.univ : Finset (Fin n)) retained assign
    (fun i => nu (cell i))
    (Cdir * (ENNReal.ofReal (2 * delta)) ^ 3)
  · intro i hi
    exact hassignRetained i
  · simpa using htotal
  · intro j hj
    exact assignment_fiber_mass_le_direction_cap
      nu center cell assign Cdir hdelta hdeltaOne hcellMeasurable
      hcellDisjoint hdirectionCell hassignClose hcap j

/-- Contact-front transfer with the affine mark kept visible.  If the point
of an original marked segment at time `t` is within `eta` of the point of a
retained marked segment at the same Reeb time, then every `rho`-ball around
the original point lies in the `(rho + eta)`-tube about the retained marked
segment.  This is the physical operation used when a cubical shading is
built from a cover-assigned portion of the original segment: the proof never
replaces the affine mark by direction closeness. -/
theorem ball_frontPoint_subset_transferred_markedUnitTube
    (line center : MarkedLine) {t eta rho : ℝ}
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hclose : dist (rawFrontParam (line, t))
      (rawFrontParam (center, t)) ≤ eta) :
    Metric.ball (rawFrontParam (line, t)) rho ⊆
      markedUnitTube center (rho + eta) := by
  intro x hx
  have hcenterFront :
      rawFrontParam (center, t) ∈ unitFront {center} :=
    rawFrontParam_mem_unitFront_singleton center ht
  refine (Metric.infDist_le_dist_of_mem hcenterFront).trans ?_
  exact le_of_lt <| by
    calc
      dist x (rawFrontParam (center, t)) ≤
          dist x (rawFrontParam (line, t)) +
            dist (rawFrontParam (line, t)) (rawFrontParam (center, t)) :=
        dist_triangle _ _ _
      _ < rho + eta := add_lt_add_of_lt_of_le hx hclose

/-- Finite-union form of the preceding transfer.  Each selected dyadic cell
is allowed its own original marked line and Reeb time, but all cells are
transferred only when their same-time front points are close to the retained
marked center.  This is the exact typed bridge from cover-assigned occurrence
cells to one WZ shading without identifying distinct affine marks. -/
theorem wzDyadicCells_subset_transferred_markedUnitTube
    (center : MarkedLine) {delta eta rho : ℝ}
    (cells : Finset (Fin 4 → ℤ))
    (sourceLine : (Fin 4 → ℤ) → MarkedLine)
    (sourceTime : (Fin 4 → ℤ) → ℝ)
    (htime : ∀ k ∈ cells,
      sourceTime k ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcell : ∀ k ∈ cells,
      wzDyadicCell delta k ⊆
        Metric.ball
          (rawFrontParam (sourceLine k, sourceTime k)) rho)
    (hfront : ∀ k ∈ cells,
      dist (rawFrontParam (sourceLine k, sourceTime k))
        (rawFrontParam (center, sourceTime k)) ≤ eta) :
    (⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k) ⊆
      markedUnitTube center (rho + eta) := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, hxcell⟩ := hx
  exact ball_frontPoint_subset_transferred_markedUnitTube
    (sourceLine k) center (htime k hk) (hfront k hk)
      (hcell k hk hxcell)

/-- A ball used to thicken one selected occurrence remains in the original
Hausdorff-cover ball after enlarging its radius by the thickening scale.  The
centre of the occurrence is an actual contact-front point; no direction-only
surrogate enters this readback. -/
theorem ball_subset_dilated_coverBall
    {X : Type*} [PseudoMetricSpace X] (source coverCenter : X)
    {rho R : ℝ}
    (hsource : source ∈ Metric.ball coverCenter R) :
    Metric.ball source rho ⊆ Metric.ball coverCenter (R + rho) := by
  intro x hx
  rw [Metric.mem_ball] at hsource hx ⊢
  calc
    dist x coverCenter ≤ dist x source + dist source coverCenter :=
      dist_triangle _ _ _
    _ < rho + R := add_lt_add hx hsource
    _ = R + rho := add_comm _ _

/-- Finite-union cover readback.  Every selected dyadic cell is charged to
the very Hausdorff-cover ball containing its source occurrence, and hence the
entire cubical shading is covered by the corresponding radius dilations. -/
theorem wzDyadicCells_subset_dilated_coverBalls
    {delta rho : ℝ}
    (cells : Finset (Fin 4 → ℤ))
    (sourceLine : (Fin 4 → ℤ) → MarkedLine)
    (sourceTime : (Fin 4 → ℤ) → ℝ)
    (coverCenter : (Fin 4 → ℤ) → E4)
    (coverRadius : (Fin 4 → ℤ) → ℝ)
    (hcell : ∀ k ∈ cells,
      wzDyadicCell delta k ⊆
        Metric.ball
          (rawFrontParam (sourceLine k, sourceTime k)) rho)
    (hassigned : ∀ k ∈ cells,
      rawFrontParam (sourceLine k, sourceTime k) ∈
        Metric.ball (coverCenter k) (coverRadius k)) :
    (⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k) ⊆
      ⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
        Metric.ball (coverCenter k) (coverRadius k + rho) := by
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk, hxcell⟩ := hx
  exact ⟨k, hk,
    ball_subset_dilated_coverBall
      (rawFrontParam (sourceLine k, sourceTime k)) (coverCenter k)
        (hassigned k hk) (hcell k hk hxcell)⟩

/-- The simultaneous physical readback required by the cover-adapted WZ
argument.  The same cubical shading lies in the tube of the retained marked
line and in controlled dilations of the original Hausdorff cover balls. -/
theorem wzDyadicCells_physical_readback
    (center : MarkedLine) {delta eta rho : ℝ}
    (cells : Finset (Fin 4 → ℤ))
    (sourceLine : (Fin 4 → ℤ) → MarkedLine)
    (sourceTime : (Fin 4 → ℤ) → ℝ)
    (coverCenter : (Fin 4 → ℤ) → E4)
    (coverRadius : (Fin 4 → ℤ) → ℝ)
    (htime : ∀ k ∈ cells,
      sourceTime k ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcell : ∀ k ∈ cells,
      wzDyadicCell delta k ⊆
        Metric.ball
          (rawFrontParam (sourceLine k, sourceTime k)) rho)
    (hfront : ∀ k ∈ cells,
      dist (rawFrontParam (sourceLine k, sourceTime k))
        (rawFrontParam (center, sourceTime k)) ≤ eta)
    (hassigned : ∀ k ∈ cells,
      rawFrontParam (sourceLine k, sourceTime k) ∈
        Metric.ball (coverCenter k) (coverRadius k)) :
    (⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k) ⊆
      markedUnitTube center (rho + eta) ∩
        (⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
          Metric.ball (coverCenter k) (coverRadius k + rho)) := by
  intro x hx
  exact ⟨
    wzDyadicCells_subset_transferred_markedUnitTube
      center cells sourceLine sourceTime htime hcell hfront hx,
    wzDyadicCells_subset_dilated_coverBalls
      cells sourceLine sourceTime coverCenter coverRadius
        hcell hassigned hx⟩

/-- Tube inclusion is monotone in the physical thickness. -/
theorem markedUnitTube_mono (line : MarkedLine) {a b : ℝ} (hab : a ≤ b) :
    markedUnitTube line a ⊆ markedUnitTube line b := by
  intro x hx
  exact hx.trans hab

/-- Scale-matched version of the contact-front transfer.  It records the
explicit numerical condition under which the transferred thickening fits in
the thickness used by the finite WZ input. -/
theorem wzDyadicCells_subset_transferred_markedUnitTube_at_scale
    (center : MarkedLine) {delta eta rho : ℝ}
    (cells : Finset (Fin 4 → ℤ))
    (sourceLine : (Fin 4 → ℤ) → MarkedLine)
    (sourceTime : (Fin 4 → ℤ) → ℝ)
    (htime : ∀ k ∈ cells,
      sourceTime k ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcell : ∀ k ∈ cells,
      wzDyadicCell delta k ⊆
        Metric.ball
          (rawFrontParam (sourceLine k, sourceTime k)) rho)
    (hfront : ∀ k ∈ cells,
      dist (rawFrontParam (sourceLine k, sourceTime k))
        (rawFrontParam (center, sourceTime k)) ≤ eta)
    (hscale : rho + eta ≤ delta) :
    (⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k) ⊆
      markedUnitTube center delta :=
  (wzDyadicCells_subset_transferred_markedUnitTube
    center cells sourceLine sourceTime htime hcell hfront).trans
      (markedUnitTube_mono center hscale)

/-- Distinct direction-separated indices carry distinct marked lines.  This
is the injectivity required by `FiniteScaleSource`; it follows from the
strictly positive separation scale and does not forget the affine mark. -/
theorem line_injective_of_direction_separated
    {n : ℕ} (line : Fin n → MarkedLine) {delta : ℝ}
    (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) :
    Function.Injective line := by
  intro i j hij
  by_contra hne
  have hpos := hseparated i j hne
  rw [hij, dist_self] at hpos
  exact (not_le_of_gt hdelta) hpos

/-- Canonical finite source carried by a finite family of actual marked
lines and prescribed shadings.  The carrier tree is the discrete one-level
tree; later carrier estimates depend only on its line parameters, while the
affine fibre mark is stored exactly. -/
noncomputable def unweightedMarkedShadingSource
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (shading : Fin n → Set E4) :
    FiniteScaleSource n where
  thickness := delta
  line := line
  line_injective := hline
  shading := shading
  weight := fun _ => 1
  fibreMark := fun i => mark (line i)
  tree := {
    parent := fun _ => none
    level := fun _ => 0
    parent_level := by simp
    carrierCell := fun i => {(direction (line i), offset (line i))}
    nested := by simp }
  line_in_carrier := by simp

/-- Source assembly specialized to a direction-separated marked family. -/
noncomputable def directionSeparatedMarkedShadingSource
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) :
    FiniteScaleSource n :=
  unweightedMarkedShadingSource delta line
    (line_injective_of_direction_separated line hdelta hseparated) shading

/-- The literal cubical shading attached to each retained marked line. -/
def wzCellShading {n : ℕ} (delta : ℝ)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (i : Fin n) : Set E4 :=
  ⋃ k ∈ (cells i : Set (Fin 4 → ℤ)), wzDyadicCell delta k

theorem isWZCubicalShading_wzCellShading
    {n : ℕ} (delta : ℝ)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (i : Fin n) :
    IsWZCubicalShading delta (wzCellShading delta cells i) := by
  exact ⟨cells i, rfl⟩

/-- A half-open WZ cell is measurable in the canonical Euclidean volume
structure on `E4`. -/
theorem measurableSet_wzDyadicCell
    (delta : ℝ) (k : Fin 4 → ℤ) : MeasurableSet (wzDyadicCell delta k) := by
  let box : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun j =>
    Set.Ico ((k j : ℝ) * delta) (((k j : ℝ) + 1) * delta))
  have hbox : MeasurableSet box := by
    dsimp [box]
    exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)
  have hcell : wzDyadicCell delta k =
      (@WithLp.ofLp 2 (Fin 4 → ℝ)) ⁻¹' box := by
    ext x
    simp [wzDyadicCell, box]
  rw [hcell]
  exact (PiLp.volume_preserving_ofLp (Fin 4)).measurable hbox

/-- The canonical integer address of a point in the side-`delta` WZ grid. -/
noncomputable def wzDyadicCellIndex (delta : ℝ) (x : E4) : Fin 4 → ℤ :=
  fun j => ⌊x j / delta⌋

/-- For positive scale, every point belongs to the half-open WZ cell carrying
its canonical floor index.  The half-open convention makes this true also on
cell boundaries, without any generic-position hypothesis. -/
theorem mem_wzDyadicCell_index
    {delta : ℝ} (hdelta : 0 < delta) (x : E4) :
    x ∈ wzDyadicCell delta (wzDyadicCellIndex delta x) := by
  intro j
  constructor
  · exact (le_div_iff₀ hdelta).mp (Int.floor_le (x j / delta))
  · exact (div_lt_iff₀ hdelta).mp (Int.lt_floor_add_one (x j / delta))

/-- The lower corner of a half-open WZ cell, regarded as a point of the
canonical four-dimensional Euclidean space. -/
def wzDyadicLowerCorner (delta : ℝ) (k : Fin 4 → ℤ) : E4 :=
  WithLp.toLp 2 (fun j => (k j : ℝ) * delta)

/-- A side-`delta` WZ cell is contained in the radius-`2 * delta` Euclidean
ball about its lower corner.  The factor two is the exact square root of the
ambient dimension and is kept explicit for the longitudinal ledger. -/
theorem wzDyadicCell_subset_ball_lowerCorner
    {delta : ℝ} (hdelta : 0 < delta) (k : Fin 4 → ℤ) :
    wzDyadicCell delta k ⊆
      Metric.ball (wzDyadicLowerCorner delta k) (2 * delta) := by
  intro x hx
  rw [Metric.mem_ball, EuclideanSpace.dist_eq,
    Real.sqrt_lt' (by positivity)]
  simp only [Fin.sum_univ_four]
  simp only [wzDyadicCell, Set.mem_ofPred_eq] at hx
  have hcoord : ∀ j : Fin 4,
      dist (x j) ((wzDyadicLowerCorner delta k) j) < delta := by
    intro j
    rw [Real.dist_eq, abs_of_nonneg]
    · simp only [wzDyadicLowerCorner, PiLp.toLp_apply]
      nlinarith [(hx j).2]
    · simp only [wzDyadicLowerCorner, PiLp.toLp_apply]
      exact sub_nonneg.mpr (hx j).1
  have h0 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (0 : Fin 4))
  have h1 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (1 : Fin 4))
  have h2 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (2 : Fin 4))
  have h3 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (3 : Fin 4))
  nlinarith

/-- Any side-`delta` WZ cell is contained in the radius-`2 * delta` ball
about each one of its own points.  This is the sharp dimension-four diameter
bound needed when the distinguished point is an actual marked-front
occurrence rather than the artificial lower corner of the grid cell. -/
theorem wzDyadicCell_subset_ball_of_mem
    {delta : ℝ} (hdelta : 0 < delta) (k : Fin 4 → ℤ)
    {x : E4} (hx : x ∈ wzDyadicCell delta k) :
    wzDyadicCell delta k ⊆ Metric.ball x (2 * delta) := by
  intro y hy
  rw [Metric.mem_ball, EuclideanSpace.dist_eq,
    Real.sqrt_lt' (by positivity)]
  simp only [Fin.sum_univ_four]
  simp only [wzDyadicCell, Set.mem_ofPred_eq] at hx hy
  have hcoord : ∀ j : Fin 4, dist (y j) (x j) < delta := by
    intro j
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [(hx j).1, (hx j).2, (hy j).1, (hy j).2]
  have h0 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (0 : Fin 4))
  have h1 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (1 : Fin 4))
  have h2 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (2 : Fin 4))
  have h3 := (sq_lt_sq₀ dist_nonneg hdelta.le).2 (hcoord (3 : Fin 4))
  nlinarith

/-- Fibre times at which one fixed marked line visits a specified cubical WZ
cell.  This is the physical cell mass used in the longitudinal allocation. -/
def markedLineDyadicCellFibreSet
    (line : MarkedLine) (delta : ℝ) (k : Fin 4 → ℤ) :
    Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :=
  {t | rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k}

theorem measurableSet_markedLineDyadicCellFibreSet
    (line : MarkedLine) (delta : ℝ) (k : Fin 4 → ℤ) :
    MeasurableSet (markedLineDyadicCellFibreSet line delta k) := by
  apply (measurableSet_wzDyadicCell delta k).preimage
  exact continuous_rawFrontParam.measurable.comp
    (measurable_const.prodMk measurable_subtype_coe)

/-- The whole normalized fibre of one marked line meets only finitely many
side-`delta` WZ cells.  This is an explicit bounded-coordinate argument: the
canonical floor index in each of the four coordinates lies in a finite integer
interval.  Hence finite cubical coverage is a theorem, not an extra input. -/
theorem exists_finite_markedLineDyadicCell_cover
    (line : MarkedLine) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ cells : Finset (Fin 4 → ℤ),
      ((Set.univ : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) ⊆
        ⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet line delta k) ∧
      ∀ k ∈ cells, ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k := by
  classical
  let B : Fin 4 → ℝ := fun j =>
    |offset line j| + (|mark line| + 1 / 2) * |direction line j|
  let indices : Set (Fin 4 → ℤ) :=
    {k | ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      wzDyadicCellIndex delta (rawFrontParam (line, (t : ℝ))) = k}
  have hindicesFinite : indices.Finite := by
    apply (Set.Finite.pi' (fun j : Fin 4 =>
      Set.finite_Icc ⌊-(B j) / delta⌋ ⌊B j / delta⌋)).subset
    intro k hk j
    rcases hk with ⟨t, rfl⟩
    have htAbs : |(t : ℝ)| ≤ 1 / 2 := by
      exact abs_le.mpr t.property
    have hmark : |mark line + (t : ℝ)| ≤ |mark line| + 1 / 2 := by
      calc
        |mark line + (t : ℝ)| ≤ |mark line| + |(t : ℝ)| := abs_add_le _ _
        _ ≤ |mark line| + 1 / 2 := add_le_add (le_refl _) htAbs
    have hcoord :
        |rawFrontParam (line, (t : ℝ)) j| ≤ B j := by
      change |offset line j + (mark line + (t : ℝ)) * direction line j| ≤ B j
      dsimp only [B]
      calc
        |offset line j + (mark line + (t : ℝ)) * direction line j| ≤
            |offset line j| + |(mark line + (t : ℝ)) * direction line j| :=
          abs_add_le _ _
        _ = |offset line j| + |mark line + (t : ℝ)| * |direction line j| := by
          rw [abs_mul]
        _ ≤ |offset line j| + (|mark line| + 1 / 2) * |direction line j| := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_right hmark (abs_nonneg _))
    constructor
    · apply Int.floor_mono
      exact (div_le_div_iff_of_pos_right hdelta).2 (neg_le_of_abs_le hcoord)
    · apply Int.floor_mono
      exact (div_le_div_iff_of_pos_right hdelta).2 (le_of_abs_le hcoord)
  refine ⟨hindicesFinite.toFinset, ?_, ?_⟩
  intro t _ht
  let k := wzDyadicCellIndex delta (rawFrontParam (line, (t : ℝ)))
  have hk : k ∈ hindicesFinite.toFinset := by
    exact (Set.Finite.mem_toFinset hindicesFinite).2 ⟨t, rfl⟩
  have htCell : t ∈ markedLineDyadicCellFibreSet line delta k := by
    exact mem_wzDyadicCell_index hdelta _
  simp only [Set.mem_iUnion]
  exact ⟨k, ⟨hk, htCell⟩⟩
  intro k hk
  have hk' : k ∈ indices := (Set.Finite.mem_toFinset hindicesFinite).1 hk
  rcases hk' with ⟨t, rfl⟩
  exact ⟨t, mem_wzDyadicCell_index hdelta _⟩

/-- Restrict the canonical finite cell family to the cells which actually
meet a prescribed active fibre-time set.  Unlike a full-segment cover, this
construction is source-hereditary and does not enlarge a Hausdorff cover
layer by adding cells from inactive times. -/
theorem exists_finite_active_markedLineDyadicCell_cover
    (line : MarkedLine) {delta : ℝ} (hdelta : 0 < delta)
    (activeTime : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) :
    ∃ cells : Finset (Fin 4 → ℤ),
      activeTime ⊆
        ⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet line delta k ∧
      ∀ k ∈ cells,
        ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          t ∈ activeTime ∧
          rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k := by
  classical
  obtain ⟨allCells, hallCover, _hallMeet⟩ :=
    exists_finite_markedLineDyadicCell_cover line hdelta
  let cells := allCells.filter fun k =>
    ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      t ∈ activeTime ∧
      rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k
  refine ⟨cells, ?_, ?_⟩
  · intro t ht
    have htAll := hallCover (Set.mem_univ t)
    simp only [Set.mem_iUnion] at htAll ⊢
    obtain ⟨k, hkAll, htCell⟩ := htAll
    have hk : k ∈ cells := by
      exact Finset.mem_filter.mpr ⟨hkAll, ⟨t, ht, htCell⟩⟩
    exact ⟨k, hk, htCell⟩
  · intro k hk
    exact (Finset.mem_filter.mp hk).2

/-- The union of all side-`delta` cells which actually meet one marked unit
segment lies in its `2 * delta`-tube.  This is the constant-scale geometric
bridge used in the cover-adapted WZ construction; no direction-only proxy or
unproved cell-containment hypothesis appears. -/
theorem wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (line : MarkedLine) {delta : ℝ} (hdelta : 0 < delta)
    (cells : Finset (Fin 4 → ℤ))
    (hmeet : ∀ k ∈ cells,
      ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k) :
    (⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k) ⊆
      markedUnitTube line (2 * delta) := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨k, hk, hxcell⟩ := hx
  obtain ⟨t, htcell⟩ := hmeet k hk
  have hball : x ∈ Metric.ball (rawFrontParam (line, (t : ℝ))) (2 * delta) :=
    wzDyadicCell_subset_ball_of_mem hdelta k htcell hxcell
  simpa using ball_frontPoint_subset_transferred_markedUnitTube
    line line (t := (t : ℝ)) (eta := 0) (rho := 2 * delta)
      t.property (by simp) hball

/-- A valid unit-speed marked line spends at most `4 * delta` of normalized
fibre time in one side-`delta` four-dimensional cell.  This is the concrete
geometric source of the per-cell longitudinal capacity; it follows from the
cell-to-ball containment and the exact one-dimensional ball-fibre estimate. -/
theorem fibreIntervalProbability_markedLineDyadicCellFibreSet_le
    {line : MarkedLine} (hvalid : IsValidLine line)
    {delta : ℝ} (hdelta : 0 < delta) (k : Fin 4 → ℤ) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        (markedLineDyadicCellFibreSet line delta k) ≤
      ENNReal.ofReal (4 * delta) := by
  calc
    (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (markedLineDyadicCellFibreSet line delta k) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineBallFibreSet line
              (wzDyadicLowerCorner delta k) (2 * delta)) := by
      apply measure_mono
      intro t ht
      exact wzDyadicCell_subset_ball_lowerCorner hdelta k ht
    _ ≤ ENNReal.ofReal (2 * (2 * delta)) :=
      fibreIntervalProbability_markedLineBallFibreSet_le
        hvalid (wzDyadicLowerCorner delta k) (by positivity)
    _ = ENNReal.ofReal (4 * delta) := by ring_nf

/-- The actual longitudinal mass of one cubical cell along a marked line. -/
noncomputable def markedLineDyadicCellMass
    (line : MarkedLine) (delta : ℝ) (k : Fin 4 → ℤ) : ENNReal :=
  (fibreIntervalProbability :
    Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
      (markedLineDyadicCellFibreSet line delta k)

theorem markedLineDyadicCellMass_le
    {line : MarkedLine} (hvalid : IsValidLine line)
    {delta : ℝ} (hdelta : 0 < delta) (k : Fin 4 → ℤ) :
    markedLineDyadicCellMass line delta k ≤ ENNReal.ofReal (4 * delta) :=
  fibreIntervalProbability_markedLineDyadicCellFibreSet_le hvalid hdelta k

/-- A finite cover of an active fibre-time set by cubical preimages converts
directly into the longitudinal mass sum used in the density ledger.  This is
outer-measure subadditivity, so no artificial disjointification is needed. -/
theorem fibreIntervalProbability_le_sum_markedLineDyadicCellMass
    (line : MarkedLine) (delta : ℝ) (cells : Finset (Fin 4 → ℤ))
    (activeTime : Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hcover : activeTime ⊆
      ⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
        markedLineDyadicCellFibreSet line delta k) :
    (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) activeTime ≤
      ∑ k ∈ cells, markedLineDyadicCellMass line delta k := by
  calc
    (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) activeTime ≤
      (fibreIntervalProbability :
        Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
          (⋃ k ∈ (cells : Set (Fin 4 → ℤ)),
            markedLineDyadicCellFibreSet line delta k) := measure_mono hcover
    _ ≤ ∑ k ∈ cells,
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
            (markedLineDyadicCellFibreSet line delta k) := by
      exact measure_biUnion_finset_le cells
        (markedLineDyadicCellFibreSet line delta)
    _ = ∑ k ∈ cells, markedLineDyadicCellMass line delta k := rfl

/-- Exact four-dimensional volume of one half-open WZ cell. -/
theorem volume_wzDyadicCell (delta : ℝ) (k : Fin 4 → ℤ) :
    volume (wzDyadicCell delta k) = (ENNReal.ofReal delta) ^ 4 := by
  let box : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun j =>
    Set.Ico ((k j : ℝ) * delta) (((k j : ℝ) + 1) * delta))
  have hbox : MeasurableSet box := by
    dsimp [box]
    exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)
  have hcell : wzDyadicCell delta k =
      (@WithLp.ofLp 2 (Fin 4 → ℝ)) ⁻¹' box := by
    ext x
    simp [wzDyadicCell, box]
  rw [hcell,
    (PiLp.volume_preserving_ofLp (Fin 4)).measure_preimage hbox.nullMeasurableSet]
  dsimp [box]
  rw [Real.volume_pi_Ico]
  simp [sub_eq_add_neg, add_mul, Finset.prod_const]

/-- Distinct integer labels give disjoint half-open WZ cells at every positive
scale. -/
theorem wzDyadicCell_disjoint
    {delta : ℝ} (hdelta : 0 < delta) {k l : Fin 4 → ℤ} (hkl : k ≠ l) :
    Disjoint (wzDyadicCell delta k) (wzDyadicCell delta l) := by
  apply Set.disjoint_left.2
  intro x hxk hxl
  have hj : ∃ j, k j ≠ l j := by
    by_contra h
    push Not at h
    exact hkl (funext h)
  obtain ⟨j, hj⟩ := hj
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · have hstepZ : k j + 1 ≤ l j := by omega
    have hstepR : (k j : ℝ) + 1 ≤ (l j : ℝ) := by exact_mod_cast hstepZ
    have hmul := mul_le_mul_of_nonneg_right hstepR hdelta.le
    exact (not_lt_of_ge (hxl j).1) ((hxk j).2.trans_le hmul)
  · have hstepZ : l j + 1 ≤ k j := by omega
    have hstepR : (l j : ℝ) + 1 ≤ (k j : ℝ) := by exact_mod_cast hstepZ
    have hmul := mul_le_mul_of_nonneg_right hstepR hdelta.le
    exact (not_lt_of_ge (hxk j).1) ((hxl j).2.trans_le hmul)

/-- The volume of a cubical shading is exactly its number of selected cells
times `delta^4`; no overlap loss is present because the cells are half-open. -/
theorem volume_wzCellShading
    {n : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (i : Fin n) :
    volume (wzCellShading delta cells i) =
      (cells i).card * (ENNReal.ofReal delta) ^ 4 := by
  have hset : wzCellShading delta cells i =
      ⋃ k ∈ cells i, wzDyadicCell delta k := by
    ext x
    simp [wzCellShading]
  rw [hset, measure_biUnion_finset]
  · simp [volume_wzDyadicCell]
  · intro k hk l hl hkl
    exact wzDyadicCell_disjoint hdelta hkl
  · intro k hk
    exact measurableSet_wzDyadicCell delta k

/-- Every finite cubical WZ shading is measurable. -/
theorem measurableSet_wzCellShading
    {n : ℕ} (delta : ℝ)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (i : Fin n) :
    MeasurableSet (wzCellShading delta cells i) := by
  have hset : wzCellShading delta cells i =
      ⋃ k ∈ cells i, wzDyadicCell delta k := by
    ext x
    simp [wzCellShading]
  rw [hset]
  exact Finset.measurableSet_biUnion (cells i)
    (fun k _hk => measurableSet_wzDyadicCell delta k)

/-- Canonical WZ source obtained from separated actual marked lines and their
finite dyadic-cell shadings. -/
noncomputable def directionSeparatedWZCellSource
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) :
    FiniteScaleSource n :=
  directionSeparatedMarkedShadingSource delta line
    (wzCellShading delta cells) hdelta hseparated

/-- Scale-honest WZ source: `tubeDelta` is the physical tube thickness while
`cellDelta` is the cubical mesh.  The old single-scale constructor is the
special case in which they coincide. -/
noncomputable def directionSeparatedWZCellSourceAtScales
    {n : ℕ} (tubeDelta cellDelta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (htubeDelta : 0 < tubeDelta)
    (hseparated : ∀ i j, i ≠ j →
      tubeDelta ≤ dist (direction (line i)) (direction (line j))) :
    FiniteScaleSource n :=
  directionSeparatedMarkedShadingSource tubeDelta line
    (wzCellShading cellDelta cells) htubeDelta hseparated

theorem directionSeparatedWZCellSourceAtScales_comparable_cubical
    {n : ℕ} (tubeDelta cellDelta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (htubeDelta : 0 < tubeDelta)
    (hcellDelta : 0 < cellDelta) (hcellTube : cellDelta ≤ tubeDelta)
    (htubeCell : tubeDelta ≤ 2 * cellDelta)
    (hcellDyadic : IsWZDyadicScale cellDelta)
    (hseparated : ∀ i j, i ≠ j →
      tubeDelta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    IsWZComparableCubicalShading
      (directionSeparatedWZCellSourceAtScales tubeDelta cellDelta line cells
        htubeDelta hseparated).thickness
      ((directionSeparatedWZCellSourceAtScales tubeDelta cellDelta line cells
        htubeDelta hseparated).shading i) := by
  exact ⟨cellDelta, hcellDelta, hcellTube, htubeCell, hcellDyadic,
    isWZCubicalShading_wzCellShading cellDelta cells i⟩

/-- At the geometrically correct fixed scale ratio, actual incidence of every
selected cell with its marked segment proves the tube-containment clause of
the finite WZ input automatically. -/
theorem directionSeparatedWZCellSourceAtScales_shading_subset_two_mul_tube
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      2 * delta ≤ dist (direction (line i)) (direction (line j)))
    (hmeet : ∀ i k, k ∈ cells i →
      ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        rawFrontParam (line i, (t : ℝ)) ∈ wzDyadicCell delta k)
    (i : Fin n) :
    (directionSeparatedWZCellSourceAtScales
        (2 * delta) delta line cells (by positivity) hseparated).shading i ⊆
      markedUnitTube
        ((directionSeparatedWZCellSourceAtScales
          (2 * delta) delta line cells (by positivity) hseparated).line i)
        (directionSeparatedWZCellSourceAtScales
          (2 * delta) delta line cells (by positivity) hseparated).thickness := by
  change wzCellShading delta cells i ⊆ markedUnitTube (line i) (2 * delta)
  exact wzDyadicCells_meeting_markedLine_subset_two_mul_tube
    (line i) hdelta (cells i) (hmeet i)

theorem directionSeparatedWZCellSource_cubical
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ)) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    IsWZCubicalShading
      (directionSeparatedWZCellSource
        delta line cells hdelta hseparated).thickness
      ((directionSeparatedWZCellSource
        delta line cells hdelta hseparated).shading i) := by
  exact isWZCubicalShading_wzCellShading delta cells i

@[simp] theorem directionSeparatedMarkedShadingSource_thickness
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) :
    (directionSeparatedMarkedShadingSource
      delta line shading hdelta hseparated).thickness = delta := rfl

@[simp] theorem directionSeparatedMarkedShadingSource_line
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    (directionSeparatedMarkedShadingSource
      delta line shading hdelta hseparated).line i = line i := rfl

@[simp] theorem directionSeparatedMarkedShadingSource_shading
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    (directionSeparatedMarkedShadingSource
      delta line shading hdelta hseparated).shading i = shading i := rfl

@[simp] theorem directionSeparatedMarkedShadingSource_weight
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    (directionSeparatedMarkedShadingSource
      delta line shading hdelta hseparated).weight i = 1 := rfl

@[simp] theorem directionSeparatedMarkedShadingSource_fibreMark
    {n : ℕ} (delta : ℝ) (line : Fin n → MarkedLine)
    (shading : Fin n → Set E4) (hdelta : 0 < delta)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j))) (i : Fin n) :
    (directionSeparatedMarkedShadingSource
      delta line shading hdelta hseparated).fibreMark i = mark (line i) := rfl

/-- The points assigned to a specified cell.  Cell equality is used only
classically, so no computable equality structure leaks into the geometric
interface. -/
noncomputable def pointsInCell
    {alpha beta : Type*} (points : Finset alpha) (cell : alpha → beta)
    (b : beta) : Finset alpha := by
  classical
  exact points.filter fun a => cell a = b

theorem pointsInCell_mono
    {alpha beta : Type*} {smaller larger : Finset alpha}
    (cell : alpha → beta) (b : beta) (hsub : smaller ⊆ larger) :
    pointsInCell smaller cell b ⊆ pointsInCell larger cell b := by
  classical
  intro a ha
  have ha' : a ∈ smaller ∧ cell a = b := by
    simpa [pointsInCell] using ha
  simpa [pointsInCell] using And.intro (hsub ha'.1) ha'.2

/-- Canonical enumeration of a retained finite family.  Its codomain is the
original ambient type, so every marked line and in particular its affine
fibre mark is transported literally rather than reconstructed. -/
noncomputable def retainedIndex
    {alpha : Type*} (retained : Finset alpha) :
    Fin retained.card → alpha :=
  fun i => ((retained.equivFin).symm i).1

theorem retainedIndex_mem
    {alpha : Type*} (retained : Finset alpha)
    (i : Fin retained.card) : retainedIndex retained i ∈ retained :=
  ((retained.equivFin).symm i).2

theorem retainedIndex_injective
    {alpha : Type*} (retained : Finset alpha) :
    Function.Injective (retainedIndex retained) := by
  intro i j hij
  apply (retained.equivFin).symm.injective
  apply Subtype.ext
  exact hij

/-- Extend a cell family indexed by the retained carrier to the ambient line
type without adding cells away from the retained family. -/
noncomputable def retainedCellFamily
    {alpha beta : Type*} (retained : Finset alpha)
    (cells : Fin retained.card → Finset beta) (a : alpha) : Finset beta := by
  classical
  exact if h : a ∈ retained then cells (retained.equivFin ⟨a, h⟩) else ∅

@[simp] theorem retainedCellFamily_retainedIndex
    {alpha beta : Type*} (retained : Finset alpha)
    (cells : Fin retained.card → Finset beta) (i : Fin retained.card) :
    retainedCellFamily retained cells (retainedIndex retained i) = cells i := by
  classical
  simp [retainedCellFamily, retainedIndex]

/-- Simultaneously choose only those cells which meet the prescribed active
time set on each retained marked line.  The witnesses retain their active-time
membership, which is the source-hereditary datum needed by cover readback. -/
theorem exists_finite_retained_active_fibre_covers
    (delta : ℝ) (hdelta : 0 < delta) (retained : Finset MarkedLine)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      (∀ i : Fin retained.card, activeTime i ⊆
        ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) ∧
      ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
        ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          t ∈ activeTime i ∧
          rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈
            wzDyadicCell delta k := by
  classical
  choose cells hcover hmeet using fun i : Fin retained.card =>
    exists_finite_active_markedLineDyadicCell_cover
      (retainedIndex retained i) hdelta (activeTime i)
  let shadingCells : MarkedLine → Finset (Fin 4 → ℤ) :=
    retainedCellFamily retained cells
  refine ⟨shadingCells, ?_, ?_⟩
  · intro i
    simpa [shadingCells] using hcover i
  · intro i k hk
    have hk' : k ∈ cells i := by
      simpa [shadingCells] using hk
    exact hmeet i k hk'

/-- Simultaneous source-hereditary form of finite fibre coverage.  For any
retained family and any later restriction of its active times, one can choose
finite cell families uniformly in the marked line, and the affine marks are
unchanged because the construction indexes the actual `rawFrontParam` fibres. -/
theorem exists_finite_active_fibre_covers
    (delta : ℝ) (hdelta : 0 < delta) (retained : Finset MarkedLine)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      (∀ i : Fin retained.card, activeTime i ⊆
        ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) ∧
      ∀ line k, k ∈ shadingCells line →
        ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          rawFrontParam (line, (t : ℝ)) ∈ wzDyadicCell delta k := by
  classical
  choose shadingCells hcover hwitness using fun line : MarkedLine =>
    exists_finite_markedLineDyadicCell_cover line hdelta
  refine ⟨shadingCells, ?_, hwitness⟩
  intro i
  exact (Set.subset_univ _).trans (hcover (retainedIndex retained i))

/-- Reindexing a retained family by `Fin retained.card` preserves every cell
fibre cardinality exactly.  This is the discrete bridge from the terminal
pruning certificate to the `FiniteScaleSource` interface. -/
theorem pointsInCell_reindex_card
    {alpha beta : Type*} (retained : Finset alpha)
    (cell : alpha → beta) (b : beta) :
    (pointsInCell (Finset.univ : Finset (Fin retained.card))
      (fun i => cell (retainedIndex retained i)) b).card =
    (pointsInCell retained cell b).card := by
  classical
  apply Finset.card_bij (fun i _hi => retainedIndex retained i)
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨retainedIndex_mem retained i, hi'.2⟩
  · intro i _hi j _hj hij
    exact retainedIndex_injective retained hij
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    let aSub : retained := ⟨a, ha'.1⟩
    let i : Fin retained.card := retained.equivFin aSub
    refine ⟨i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      simpa [retainedIndex, i, aSub] using ha'.2
    · simp [retainedIndex, i, aSub]

/-- The retained marked family, enumerated as a literal WZ finite source.
The source line is the original retained marked line, so the affine fibre
mark survives definitionally. -/
noncomputable def retainedWZCellSource
    (delta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (hdelta : 0 < delta)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b)) :
    FiniteScaleSource retained.card :=
  directionSeparatedWZCellSource delta (retainedIndex retained)
    (fun i => shadingCells (retainedIndex retained i)) hdelta (by
      intro i j hij
      exact hseparated (retainedIndex retained i) (retainedIndex_mem retained i)
        (retainedIndex retained j) (retainedIndex_mem retained j)
        (fun h => hij (retainedIndex_injective retained h)))

/-- Retained source with separate, comparable physical and cubical scales. -/
noncomputable def retainedWZCellSourceAtScales
    (tubeDelta cellDelta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (htubeDelta : 0 < tubeDelta)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      tubeDelta ≤ dist (direction a) (direction b)) :
    FiniteScaleSource retained.card :=
  directionSeparatedWZCellSourceAtScales tubeDelta cellDelta
    (retainedIndex retained)
    (fun i => shadingCells (retainedIndex retained i)) htubeDelta (by
      intro i j hij
      exact hseparated (retainedIndex retained i) (retainedIndex_mem retained i)
        (retainedIndex retained j) (retainedIndex_mem retained j)
        (fun h => hij (retainedIndex_injective retained h)))

/-- If every selected cell meets an active fibre occurrence and every active
occurrence lies in a physical target, then the entire cubical source lies in
the `2 * delta` ball inflation of that same target.  Thus cover readback uses
the selected active layer itself, not the full marked segments. -/
theorem retainedWZCellSourceAtScales_shadingUnion_subset_active_target_inflation
    (delta : ℝ) (hdelta : 0 < delta) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b))
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (target : Set E4)
    (hactiveTarget : ∀ i t, t ∈ activeTime i →
      rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈ target)
    (hmeet : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        t ∈ activeTime i ∧
        rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈
          wzDyadicCell delta k) :
    (⋃ i, (retainedWZCellSourceAtScales (2 * delta) delta retained
      shadingCells (by positivity) hseparated).shading i) ⊆
        ⋃ y ∈ target, Metric.ball y (2 * delta) := by
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hxi⟩ := hx
  change x ∈ wzCellShading delta
    (fun j => shadingCells (retainedIndex retained j)) i at hxi
  simp only [wzCellShading, Set.mem_iUnion] at hxi
  obtain ⟨k, hk, hxCell⟩ := hxi
  obtain ⟨t, htActive, htCell⟩ := hmeet i k hk
  let y : E4 := rawFrontParam (retainedIndex retained i, (t : ℝ))
  refine ⟨y, hactiveTarget i t htActive, ?_⟩
  exact wzDyadicCell_subset_ball_of_mem hdelta k htCell hxCell

/-- Concrete contact-front data place every retained cubical shading inside
its actual marked tube.  The source marked line and the common Reeb time are
kept for each selected cell, so this bridge does not replace affine marks by
direction closeness. -/
theorem retainedWZCellSource_shading_subset_of_front_transfer
    (delta rho transfer : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (hdelta : 0 < delta)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (sourceLine : Fin retained.card → (Fin 4 → ℤ) → MarkedLine)
    (sourceTime : Fin retained.card → (Fin 4 → ℤ) → ℝ)
    (htime : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      sourceTime i k ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcell : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      wzDyadicCell delta k ⊆
        Metric.ball (rawFrontParam (sourceLine i k, sourceTime i k)) rho)
    (hfront : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      dist (rawFrontParam (sourceLine i k, sourceTime i k))
        (rawFrontParam (retainedIndex retained i, sourceTime i k)) ≤ transfer)
    (hscale : rho + transfer ≤ delta) :
    ∀ i : Fin retained.card,
      (retainedWZCellSource
        delta retained shadingCells hdelta hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSource
            delta retained shadingCells hdelta hseparated).line i)
          (retainedWZCellSource
            delta retained shadingCells hdelta hseparated).thickness := by
  intro i
  change
    (⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
        wzDyadicCell delta k) ⊆
      markedUnitTube (retainedIndex retained i) delta
  exact wzDyadicCells_subset_transferred_markedUnitTube_at_scale
    (retainedIndex retained i) (shadingCells (retainedIndex retained i))
    (sourceLine i) (sourceTime i) (htime i) (hcell i) (hfront i) hscale

/-- Canonical finite active-fibre cells simultaneously supply their covering
property and the physical tube-containment clause at the correct fixed scale
ratio.  This removes `hshadingTube` from the geometric construction rather
than leaving it as an external premise. -/
theorem exists_retained_wz_two_scale_cells_of_active_fibres
    (delta : ℝ) (hdelta : 0 < delta) (retained : Finset MarkedLine)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b)) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      (∀ i : Fin retained.card, activeTime i ⊆
        ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) ∧
      ∀ i : Fin retained.card,
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
            (by positivity) hseparated).line i)
          (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
            (by positivity) hseparated).thickness := by
  obtain ⟨shadingCells, hcover, hmeet⟩ :=
    exists_finite_retained_active_fibre_covers delta hdelta retained activeTime
  refine ⟨shadingCells, hcover, ?_⟩
  intro i
  change
    (directionSeparatedWZCellSourceAtScales (2 * delta) delta
      (retainedIndex retained)
      (fun j => shadingCells (retainedIndex retained j)) (by positivity) _).shading i ⊆
      markedUnitTube (retainedIndex retained i) (2 * delta)
  let hsepIndex : ∀ a b : Fin retained.card, a ≠ b →
      2 * delta ≤ dist (direction (retainedIndex retained a))
        (direction (retainedIndex retained b)) := by
    intro a b hab
    exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
      (retainedIndex retained b) (retainedIndex_mem retained b)
      (fun h => hab (retainedIndex_injective retained h))
  exact directionSeparatedWZCellSourceAtScales_shading_subset_two_mul_tube
    delta (retainedIndex retained)
      (fun j => shadingCells (retainedIndex retained j)) hdelta hsepIndex
      (by
        intro j k hk
        obtain ⟨t, _htActive, htCell⟩ := hmeet j k hk
        exact ⟨t, htCell⟩) i

/-- The terminal population certificate transports verbatim to the canonical
`Fin retained.card` enumeration. -/
theorem terminal_population_reindex
    {alpha beta level : Type*} (retained : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ)
    (hterminal : ∀ ell b,
      (pointsInCell retained (cell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (cell ell) b).card) :
    ∀ ell b,
      (pointsInCell (Finset.univ : Finset (Fin retained.card))
        (fun i => cell ell (retainedIndex retained i)) b).Nonempty →
      threshold ell ≤
        (pointsInCell (Finset.univ : Finset (Fin retained.card))
          (fun i => cell ell (retainedIndex retained i)) b).card := by
  intro ell b hnonempty
  have holdNonempty : (pointsInCell retained (cell ell) b).Nonempty := by
    apply Finset.card_pos.mp
    rw [← pointsInCell_reindex_card retained (cell ell) b]
    exact Finset.card_pos.mpr hnonempty
  have h := hterminal ell b holdNonempty
  rwa [pointsInCell_reindex_card retained (cell ell) b]

/-- Scale--cell pairs occupied by a finite point family. -/
noncomputable def occupiedCells
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta) :
    Finset (level × beta) := by
  classical
  exact ((Finset.univ : Finset level).product (Finset.univ : Finset beta)).filter
    fun e => (pointsInCell points (cell e.1) e.2).Nonempty

/-- The threshold penalty of the cells occupied by a point family. -/
noncomputable def occupiedCellPenalty
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) : ℕ :=
  ∑ e ∈ occupiedCells points cell, threshold e.1

/-- The nonrecursive pruning potential: cardinality minus occupied-cell
threshold penalty. -/
noncomputable def carrierPruningPotential
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) : ℤ :=
  (points.card : ℤ) - (occupiedCellPenalty points cell threshold : ℤ)

theorem occupiedCells_mono
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    {smaller larger : Finset alpha} (cell : level → alpha → beta)
    (hsub : smaller ⊆ larger) :
    occupiedCells smaller cell ⊆ occupiedCells larger cell := by
  classical
  intro e he
  have he' := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨he'.1, ?_⟩
  obtain ⟨a, ha⟩ := he'.2
  exact ⟨a, pointsInCell_mono (cell e.1) e.2 hsub ha⟩

theorem occupiedCellPenalty_le_total
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) :
    occupiedCellPenalty points cell threshold ≤
      ∑ ell : level, Fintype.card beta * threshold ell := by
  classical
  calc
    occupiedCellPenalty points cell threshold =
        ∑ e ∈ occupiedCells points cell, threshold e.1 := rfl
    _ ≤ ∑ e ∈ ((Finset.univ : Finset level).product
          (Finset.univ : Finset beta)), threshold e.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact (Finset.mem_filter.mp he).1
      · intro e he hnot
        exact Nat.zero_le _
    _ = ∑ ell : level, Fintype.card beta * threshold ell := by
      change (∑ e : level × beta, threshold e.1) = _
      rw [Fintype.sum_prod_type]
      simp

theorem occupiedCells_erase_fiber_subset
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (ell : level) (b : beta)
    (hocc : (pointsInCell points (cell ell) b).Nonempty) :
    occupiedCells (points \ pointsInCell points (cell ell) b) cell ⊆
      (occupiedCells points cell).erase (ell, b) := by
  classical
  intro e he
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    subst e
    have he' := Finset.mem_filter.mp he
    obtain ⟨a, ha⟩ := he'.2
    have ha' :
        a ∈ points \ pointsInCell points (cell ell) b ∧ cell ell a = b := by
      simpa [pointsInCell] using ha
    have haRemoved : a ∈ pointsInCell points (cell ell) b := by
      simpa [pointsInCell] using
        And.intro (Finset.mem_sdiff.mp ha'.1).1 ha'.2
    exact (Finset.mem_sdiff.mp ha'.1).2 haRemoved
  · exact occupiedCells_mono cell Finset.sdiff_subset he

theorem occupiedCellPenalty_erase_fiber_add_le
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) (ell : level) (b : beta)
    (hocc : (pointsInCell points (cell ell) b).Nonempty) :
    occupiedCellPenalty
        (points \ pointsInCell points (cell ell) b) cell threshold +
        threshold ell ≤
      occupiedCellPenalty points cell threshold := by
  classical
  have hkey : (ell, b) ∈ occupiedCells points cell := by
    apply Finset.mem_filter.mpr
    exact ⟨by simp, hocc⟩
  have hsum :
      occupiedCellPenalty
          (points \ pointsInCell points (cell ell) b) cell threshold ≤
        ∑ e ∈ (occupiedCells points cell).erase (ell, b),
          threshold e.1 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact occupiedCells_erase_fiber_subset points cell ell b hocc
    · intro e he hnot
      exact Nat.zero_le _
  calc
    occupiedCellPenalty
          (points \ pointsInCell points (cell ell) b) cell threshold +
          threshold ell ≤
        (∑ e ∈ (occupiedCells points cell).erase (ell, b),
          threshold e.1) + threshold ell := Nat.add_le_add_right hsum _
    _ = occupiedCellPenalty points cell threshold := by
      simpa [occupiedCellPenalty] using
        (Finset.sum_erase_add (occupiedCells points cell)
          (fun e => threshold e.1) hkey)

/-- A finite multiscale carrier admits a terminal pruning obtained without
recursion: maximize cardinality minus the total threshold penalty of occupied
cells over all subfamilies.  At a maximizer, deleting any under-populated
occupied cell would strictly increase the potential, which is impossible. -/
theorem exists_terminal_carrier_pruning
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ retained.card +
        ∑ ell : level, Fintype.card beta * threshold ell ∧
      ∀ (ell : level) (b : beta),
        (pointsInCell retained (cell ell) b).Nonempty →
          threshold ell ≤ (pointsInCell retained (cell ell) b).card := by
  classical
  obtain ⟨retained, hretainedPower, hmax⟩ :=
    Finset.exists_max_image points.powerset
      (fun subset => carrierPruningPotential subset cell threshold)
      ⟨points, Finset.mem_powerset.mpr (by rfl)⟩
  have hretained : retained ⊆ points :=
    Finset.mem_powerset.mp hretainedPower
  refine ⟨retained, hretained, ?_, ?_⟩
  · have hfull := hmax points (Finset.mem_powerset.mpr (by rfl))
    have hpenalty :=
      occupiedCellPenalty_le_total points cell threshold
    change
      (points.card : ℤ) -
          (occupiedCellPenalty points cell threshold : ℤ) ≤
        (retained.card : ℤ) -
          (occupiedCellPenalty retained cell threshold : ℤ) at hfull
    omega
  · intro ell b hoccupied
    by_contra hpopulation
    have hlow :
        (pointsInCell retained (cell ell) b).card < threshold ell :=
      Nat.lt_of_not_ge hpopulation
    let fiber := pointsInCell retained (cell ell) b
    let smaller := retained \ fiber
    have hfiberOccupied : fiber.Nonempty := by
      simpa [fiber] using hoccupied
    have hsmallerSubset : smaller ⊆ points :=
      Finset.sdiff_subset.trans hretained
    have hsmallerPower : smaller ∈ points.powerset :=
      Finset.mem_powerset.mpr hsmallerSubset
    have hmaxSmaller := hmax smaller hsmallerPower
    have hpenaltyDrop :
        occupiedCellPenalty smaller cell threshold + threshold ell ≤
          occupiedCellPenalty retained cell threshold := by
      simpa [smaller, fiber] using
        occupiedCellPenalty_erase_fiber_add_le
          retained cell threshold ell b hoccupied
    have hfiberSubset : fiber ⊆ retained := by
      intro a ha
      have ha' : a ∈ retained ∧ cell ell a = b := by
        simpa [fiber, pointsInCell] using ha
      exact ha'.1
    have hcard : smaller.card + fiber.card = retained.card := by
      simpa [smaller] using
        (Finset.card_sdiff_add_card_eq_card hfiberSubset)
    have hstrict :
        carrierPruningPotential retained cell threshold <
          carrierPruningPotential smaller cell threshold := by
      change
        (retained.card : ℤ) -
            (occupiedCellPenalty retained cell threshold : ℤ) <
          (smaller.card : ℤ) -
            (occupiedCellPenalty smaller cell threshold : ℤ)
      dsimp [fiber] at hlow hcard
      omega
    exact (not_lt_of_ge hmaxSmaller) hstrict

/-- If twice the total occupied-cell budget fits inside the original family,
the terminal pruning retains at least half of the points. -/
theorem exists_terminal_carrier_pruning_half
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ)
    (hbudget :
      2 * (∑ ell : level, Fintype.card beta * threshold ell) ≤
        points.card) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ (ell : level) (b : beta),
        (pointsInCell retained (cell ell) b).Nonempty →
          threshold ell ≤ (pointsInCell retained (cell ell) b).card := by
  obtain ⟨retained, hretained, hsize, hterminal⟩ :=
    exists_terminal_carrier_pruning points cell threshold
  refine ⟨retained, hretained, ?_, hterminal⟩
  omega

/-!
For a cover-adapted application the available carrier cells depend on the
scale.  The following variant keeps those finite cell sets explicit, so the
deletion budget is the sharp sum of `card (cells ell) * threshold ell` rather
than a common ambient-cell cardinality at every level.
-/

noncomputable def occupiedCellsWithin
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) : Finset (level × beta) := by
  classical
  exact ((Finset.univ : Finset level).product (Finset.univ : Finset beta)).filter
    fun e => e.2 ∈ cells e.1 ∧
      (pointsInCell points (cell e.1) e.2).Nonempty

noncomputable def occupiedCellPenaltyWithin
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ) : ℕ :=
  ∑ e ∈ occupiedCellsWithin cells points cell, threshold e.1

noncomputable def carrierPruningPotentialWithin
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ) : ℤ :=
  (points.card : ℤ) -
    (occupiedCellPenaltyWithin cells points cell threshold : ℤ)

theorem occupiedCellsWithin_mono
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) {smaller larger : Finset alpha}
    (cell : level → alpha → beta) (hsub : smaller ⊆ larger) :
    occupiedCellsWithin cells smaller cell ⊆
      occupiedCellsWithin cells larger cell := by
  classical
  intro e he
  have he' := Finset.mem_filter.mp he
  apply Finset.mem_filter.mpr
  refine ⟨he'.1, he'.2.1, ?_⟩
  obtain ⟨a, ha⟩ := he'.2.2
  exact ⟨a, pointsInCell_mono (cell e.1) e.2 hsub ha⟩

theorem occupiedCellPenaltyWithin_le_total
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ) :
    occupiedCellPenaltyWithin cells points cell threshold ≤
      ∑ ell : level, (cells ell).card * threshold ell := by
  classical
  calc
    occupiedCellPenaltyWithin cells points cell threshold =
        ∑ e ∈ occupiedCellsWithin cells points cell,
          threshold e.1 := rfl
    _ ≤ ∑ e ∈
          (((Finset.univ : Finset level).product
            (Finset.univ : Finset beta)).filter fun e => e.2 ∈ cells e.1),
          threshold e.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have he' := Finset.mem_filter.mp he
        apply Finset.mem_filter.mpr
        exact ⟨he'.1, he'.2.1⟩
      · intro e he hnot
        exact Nat.zero_le _
    _ = ∑ ell : level, (cells ell).card * threshold ell := by
      rw [Finset.sum_filter]
      change
        (∑ e : level × beta,
          if e.2 ∈ cells e.1 then threshold e.1 else 0) = _
      rw [Fintype.sum_prod_type]
      simp

theorem occupiedCellsWithin_erase_fiber_subset
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (ell : level) (b : beta) :
    occupiedCellsWithin cells
        (points \ pointsInCell points (cell ell) b) cell ⊆
      (occupiedCellsWithin cells points cell).erase (ell, b) := by
  intro e he
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    subst e
    have he' :
        b ∈ cells ell ∧
          (pointsInCell
            (points \ pointsInCell points (cell ell) b)
            (cell ell) b).Nonempty := by
      simpa [occupiedCellsWithin] using he
    obtain ⟨a, ha⟩ := he'.2
    have ha' :
        a ∈ points \ pointsInCell points (cell ell) b ∧ cell ell a = b := by
      simpa [pointsInCell] using ha
    have haRemoved : a ∈ pointsInCell points (cell ell) b := by
      simpa [pointsInCell] using
        And.intro (Finset.mem_sdiff.mp ha'.1).1 ha'.2
    exact (Finset.mem_sdiff.mp ha'.1).2 haRemoved
  · exact occupiedCellsWithin_mono cells cell Finset.sdiff_subset he

theorem occupiedCellPenaltyWithin_erase_fiber_add_le
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ)
    (ell : level) (b : beta) (hb : b ∈ cells ell)
    (hocc : (pointsInCell points (cell ell) b).Nonempty) :
    occupiedCellPenaltyWithin cells
        (points \ pointsInCell points (cell ell) b) cell threshold +
        threshold ell ≤
      occupiedCellPenaltyWithin cells points cell threshold := by
  have hkey : (ell, b) ∈ occupiedCellsWithin cells points cell := by
    simpa [occupiedCellsWithin] using And.intro hb hocc
  have hsum :
      occupiedCellPenaltyWithin cells
          (points \ pointsInCell points (cell ell) b) cell threshold ≤
        ∑ e ∈ (occupiedCellsWithin cells points cell).erase (ell, b),
          threshold e.1 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact occupiedCellsWithin_erase_fiber_subset cells points cell ell b
    · intro e he hnot
      exact Nat.zero_le _
  calc
    occupiedCellPenaltyWithin cells
          (points \ pointsInCell points (cell ell) b) cell threshold +
          threshold ell ≤
        (∑ e ∈ (occupiedCellsWithin cells points cell).erase (ell, b),
          threshold e.1) + threshold ell := Nat.add_le_add_right hsum _
    _ = occupiedCellPenaltyWithin cells points cell threshold := by
      simpa [occupiedCellPenaltyWithin] using
        (Finset.sum_erase_add (occupiedCellsWithin cells points cell)
          (fun e => threshold e.1) hkey)

theorem exists_terminal_carrier_pruning_with_varying_cells
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ retained.card +
        ∑ ell : level, (cells ell).card * threshold ell ∧
      ∀ (ell : level) (b : beta),
        (pointsInCell retained (cell ell) b).Nonempty →
          threshold ell ≤ (pointsInCell retained (cell ell) b).card := by
  classical
  obtain ⟨retained, hretainedPower, hmax⟩ :=
    Finset.exists_max_image points.powerset
      (fun subset =>
        carrierPruningPotentialWithin cells subset cell threshold)
      ⟨points, Finset.mem_powerset.mpr (by rfl)⟩
  have hretained : retained ⊆ points :=
    Finset.mem_powerset.mp hretainedPower
  refine ⟨retained, hretained, ?_, ?_⟩
  · have hfull := hmax points (Finset.mem_powerset.mpr (by rfl))
    have hpenalty :=
      occupiedCellPenaltyWithin_le_total cells points cell threshold
    change
      (points.card : ℤ) -
          (occupiedCellPenaltyWithin cells points cell threshold : ℤ) ≤
        (retained.card : ℤ) -
          (occupiedCellPenaltyWithin cells retained cell threshold : ℤ) at hfull
    omega
  · intro ell b hoccupied
    by_contra hpopulation
    have hlow :
        (pointsInCell retained (cell ell) b).card < threshold ell :=
      Nat.lt_of_not_ge hpopulation
    obtain ⟨a, ha⟩ := hoccupied
    have ha' : a ∈ retained ∧ cell ell a = b := by
      simpa [pointsInCell] using ha
    have hb : b ∈ cells ell := by
      rw [← ha'.2]
      exact hcell ell a (hretained ha'.1)
    let fiber := pointsInCell retained (cell ell) b
    let smaller := retained \ fiber
    have hsmallerSubset : smaller ⊆ points :=
      Finset.sdiff_subset.trans hretained
    have hsmallerPower : smaller ∈ points.powerset :=
      Finset.mem_powerset.mpr hsmallerSubset
    have hmaxSmaller := hmax smaller hsmallerPower
    have hpenaltyDrop :
        occupiedCellPenaltyWithin cells smaller cell threshold + threshold ell ≤
          occupiedCellPenaltyWithin cells retained cell threshold := by
      simpa [smaller, fiber] using
        occupiedCellPenaltyWithin_erase_fiber_add_le
          cells retained cell threshold ell b hb ⟨a, ha⟩
    have hfiberSubset : fiber ⊆ retained := by
      intro x hx
      have hx' : x ∈ retained ∧ cell ell x = b := by
        simpa [fiber, pointsInCell] using hx
      exact hx'.1
    have hcard : smaller.card + fiber.card = retained.card := by
      simpa [smaller] using
        (Finset.card_sdiff_add_card_eq_card hfiberSubset)
    have hstrict :
        carrierPruningPotentialWithin cells retained cell threshold <
          carrierPruningPotentialWithin cells smaller cell threshold := by
      change
        (retained.card : ℤ) -
            (occupiedCellPenaltyWithin cells retained cell threshold : ℤ) <
          (smaller.card : ℤ) -
            (occupiedCellPenaltyWithin cells smaller cell threshold : ℤ)
      dsimp [fiber] at hlow hcard
      omega
    exact (not_lt_of_ge hmaxSmaller) hstrict

theorem exists_terminal_carrier_pruning_with_varying_cells_half
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hbudget :
      2 * (∑ ell : level, (cells ell).card * threshold ell) ≤
        points.card) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ (ell : level) (b : beta),
        (pointsInCell retained (cell ell) b).Nonempty →
          threshold ell ≤ (pointsInCell retained (cell ell) b).card := by
  obtain ⟨retained, hretained, hsize, hterminal⟩ :=
    exists_terminal_carrier_pruning_with_varying_cells
      cells points cell threshold hcell
  refine ⟨retained, hretained, ?_, hterminal⟩
  omega

/-!
The terminal cell statement becomes the lower half of almost AD regularity
only after it is read in the metric of line parameters.  The following
lemmas make that step explicit: a carrier cell containing a retained point
must lie in a controlled metric ball about that point.
-/

noncomputable def pointsInMetricClosedBall
    {alpha X : Type*} [PseudoMetricSpace X]
    (points : Finset alpha) (image : alpha → X) (a : alpha) (radius : ℝ) :
    Finset alpha := by
  classical
  exact points.filter fun b => dist (image b) (image a) ≤ radius

/-- For a finite-scale source, the abstract metric-ball count is literally
the carrier-ball count in the WZ interface.  No comparison constant or
forgetful map occurs here: the image is the full marked carrier parameter
`(direction, offset)`. -/
@[simp] theorem pointsInMetricClosedBall_univ_wzCarrierPoint_card
    {n : ℕ} (D : FiniteScaleSource n) (i : Fin n) (radius : ℝ) :
    (pointsInMetricClosedBall (Finset.univ : Finset (Fin n))
      (wzCarrierPoint D) i radius).card =
        wzCarrierBallCount D i radius := by
  rfl

theorem pointsInCell_subset_pointsInMetricClosedBall
    {alpha beta level X : Type*} [PseudoMetricSpace X]
    (points : Finset alpha) (cell : level → alpha → beta)
    (image : alpha → X) (radius : level → ℝ)
    (ell : level) (a : alpha) (ha : a ∈ points)
    (hcellDiameter : ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    pointsInCell points (cell ell) (cell ell a) ⊆
      pointsInMetricClosedBall points image a (radius ell) := by
  classical
  intro b hb
  have hb' : b ∈ points ∧ cell ell b = cell ell a := by
    simpa [pointsInCell] using hb
  exact Finset.mem_filter.mpr
    ⟨hb'.1, hcellDiameter b hb'.1 hb'.2⟩

/-- Terminal population in every occupied carrier cell gives a centered
metric-ball lower count at every retained parameter and every selected
scale. -/
theorem terminal_carrier_pruning_metric_lower_count
    {alpha beta level X : Type*} [PseudoMetricSpace X]
    (retained : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) (image : alpha → X)
    (radius : level → ℝ)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell retained (cell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (cell ell) b).card)
    (hcellDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∀ ell a, a ∈ retained →
      threshold ell ≤
        (pointsInMetricClosedBall retained image a (radius ell)).card := by
  intro ell a ha
  have hoccupied :
      (pointsInCell retained (cell ell) (cell ell a)).Nonempty := by
    refine ⟨a, ?_⟩
    simp [pointsInCell, ha]
  have hpopulation := hterminal ell (cell ell a) hoccupied
  exact hpopulation.trans (Finset.card_le_card
    (pointsInCell_subset_pointsInMetricClosedBall
      retained cell image radius ell a ha (hcellDiameter ell a ha)))

/-- Metric form of the cover-adapted pruning lemma.  Under the finite
deletion budget it retains at least half the parameters, preserves the
cellwise terminal statement, and supplies the centered lower count at every
chosen scale.  The upper count is a separate packing consequence of direction
separation, exactly as in the manuscript. -/
theorem exists_terminal_carrier_pruning_metric_half
    {alpha beta level X : Type*} [Fintype beta] [Fintype level]
    [PseudoMetricSpace X]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (threshold : level → ℕ)
    (image : alpha → X) (radius : level → ℝ)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell)
    (hbudget :
      2 * (∑ ell : level, (cells ell).card * threshold ell) ≤
        points.card) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      (∀ (ell : level) (b : beta),
        (pointsInCell retained (cell ell) b).Nonempty →
          threshold ell ≤ (pointsInCell retained (cell ell) b).card) ∧
      ∀ ell a, a ∈ retained →
        threshold ell ≤
          (pointsInMetricClosedBall retained image a (radius ell)).card := by
  obtain ⟨retained, hretained, hsize, hterminal⟩ :=
    exists_terminal_carrier_pruning_with_varying_cells_half
      cells points cell threshold hcell hbudget
  refine ⟨retained, hretained, hsize, hterminal, ?_⟩
  apply terminal_carrier_pruning_metric_lower_count
    retained cell threshold image radius hterminal
  intro ell a ha b hb heq
  exact hcellDiameter ell a (hretained ha) b (hretained hb) heq

/-- Scales at which the requested real-valued lower population is nontrivial.
At the complementary scales the center point itself already supplies the
bound.  Restricting pruning to this subtype prevents the spurious one-point
per-cell charge caused by rounding a threshold smaller than one. -/
abbrev ActiveCarrierPruningLevel {level : Type*}
    (target : level → ℝ) := {ell : level // 1 ≤ target ell}

/-- On an active scale the integer ceiling costs less than twice the real
threshold.  This is why the pruning ledger must omit scales with target below
one. -/
theorem active_carrier_threshold_ceil_lt_two_mul
    {level : Type*} (target : level → ℝ)
    (ell : ActiveCarrierPruningLevel target) :
    (⌈target ell.1⌉₊ : ℝ) < 2 * target ell.1 := by
  apply Nat.ceil_lt_two_mul
  linarith [ell.2]

/-- Summed ceiling loss on the active scales.  The factor two is uniform in
the number of scales and cells. -/
theorem active_carrier_ceiling_charge_le_two_mul
    {beta level : Type*} [Fintype level]
    (cells : level → Finset beta) (target : level → ℝ) :
    ((∑ ell : ActiveCarrierPruningLevel target,
        (cells ell.1).card * ⌈target ell.1⌉₊ : ℕ) : ℝ) ≤
      2 * ∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1 := by
  classical
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * (⌈target ell.1⌉₊ : ℝ)) ≤
      ∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * (2 * target ell.1) := by
        apply Finset.sum_le_sum
        intro ell _hell
        exact mul_le_mul_of_nonneg_left
          (active_carrier_threshold_ceil_lt_two_mul target ell).le
          (Nat.cast_nonneg _)
    _ = 2 * ∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _hell
      ring

/-- A real weighted-Carleson budget implies the exact natural-number budget
required by terminal pruning.  The coefficient four is precisely: twice for
retaining half the points and twice for ceiling the active real thresholds. -/
theorem active_carrier_nat_budget_of_real_budget
    {alpha beta level : Type*} [Fintype level]
    (cells : level → Finset beta) (points : Finset alpha)
    (target : level → ℝ)
    (hbudgetReal :
      4 * (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1) ≤
          (points.card : ℝ)) :
    2 * (∑ ell : ActiveCarrierPruningLevel target,
      (cells ell.1).card * ⌈target ell.1⌉₊) ≤ points.card := by
  classical
  have hceiling := active_carrier_ceiling_charge_le_two_mul cells target
  have hreal :
      (2 * (∑ ell : ActiveCarrierPruningLevel target,
        (cells ell.1).card * ⌈target ell.1⌉₊) : ℝ) ≤
          (points.card : ℝ) := by
    calc
      (2 * (∑ ell : ActiveCarrierPruningLevel target,
        (cells ell.1).card * ⌈target ell.1⌉₊) : ℝ) =
          2 * ((∑ ell : ActiveCarrierPruningLevel target,
            (cells ell.1).card * ⌈target ell.1⌉₊ : ℕ) : ℝ) := by
              norm_num
      _ ≤ 2 * (2 * ∑ ell : ActiveCarrierPruningLevel target,
          ((cells ell.1).card : ℝ) * target ell.1) :=
        mul_le_mul_of_nonneg_left hceiling (by norm_num)
      _ = 4 * (∑ ell : ActiveCarrierPruningLevel target,
          ((cells ell.1).card : ℝ) * target ell.1) := by ring
      _ ≤ (points.card : ℝ) := hbudgetReal
  exact_mod_cast hreal

/-- Finite dyadic Carleson summation for the active pruning ledger.  A charge
bounded by `K q^ell` at level `ell` sums with a constant independent of the
depth; the inactive-level filter can only decrease the sum. -/
theorem active_carrier_geometric_charge_bound
    {beta : Type*} (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (target : Fin (levelZero + 1) → ℝ) (K q : ℝ)
    (hK : 0 ≤ K) (hq : 1 < q)
    (hcharge : ∀ ell,
      ((cells ell).card : ℝ) * target ell ≤ K * q ^ ell.val) :
    (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1) ≤
      K * q ^ (levelZero + 1) / (q - 1) := by
  classical
  let active : Finset (Fin (levelZero + 1)) :=
    Finset.univ.filter fun ell => 1 ≤ target ell
  have hactiveEq :
      (∑ ell ∈ active,
          ((cells ell).card : ℝ) * target ell) =
        ∑ ell : ActiveCarrierPruningLevel target,
          ((cells ell.1).card : ℝ) * target ell.1 := by
    apply Finset.sum_subtype active
    intro ell
    simp [active]
  have hfiltered :
      (∑ ell : ActiveCarrierPruningLevel target,
          K * q ^ ell.1.val) ≤
        ∑ ell : Fin (levelZero + 1), K * q ^ ell.val := by
    rw [← Finset.sum_subtype active (by
      intro ell
      simp [active]) (fun ell => K * q ^ ell.val)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (by
        simpa [active] using
          (Finset.filter_subset (fun ell : Fin (levelZero + 1) =>
            1 ≤ target ell) Finset.univ))
    intro ell _hell _hnot
    positivity
  have hpointwise :
      (∑ ell : ActiveCarrierPruningLevel target,
          ((cells ell.1).card : ℝ) * target ell.1) ≤
        ∑ ell : ActiveCarrierPruningLevel target,
          K * q ^ ell.1.val := by
    apply Finset.sum_le_sum
    intro ell _hell
    exact hcharge ell.1
  have hfull :
      (∑ ell : Fin (levelZero + 1), K * q ^ ell.val) =
        K * ∑ i ∈ Finset.range (levelZero + 1), q ^ i := by
    calc
      (∑ ell : Fin (levelZero + 1), K * q ^ ell.val) =
          K * ∑ ell : Fin (levelZero + 1), q ^ ell.val := by
            rw [Finset.mul_sum]
      _ = K * ∑ i ∈ Finset.range (levelZero + 1), q ^ i := by
        rw [Fin.sum_univ_eq_sum_range]
  have hgeom :
      (∑ i ∈ Finset.range (levelZero + 1), q ^ i) ≤
        q ^ (levelZero + 1) / (q - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).2
    rw [geom_sum_mul]
    linarith
  calc
    (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1) ≤
      ∑ ell : ActiveCarrierPruningLevel target,
        K * q ^ ell.1.val := hpointwise
    _ ≤ ∑ ell : Fin (levelZero + 1), K * q ^ ell.val := hfiltered
    _ = K * ∑ i ∈ Finset.range (levelZero + 1), q ^ i := hfull
    _ ≤ K * (q ^ (levelZero + 1) / (q - 1)) :=
      mul_le_mul_of_nonneg_left hgeom hK
    _ = K * q ^ (levelZero + 1) / (q - 1) := by ring

/-- The manuscript's cell-count and population-threshold estimates multiply
without loss: if their dyadic factors are `qCell^ell` and `qTarget^ell`, the
Carleson charge has ratio `(qCell * qTarget)^ell`. -/
theorem carrier_cell_target_product_charge
    {beta : Type*} {levelZero : ℕ}
    (cells : Fin (levelZero + 1) → Finset beta)
    (target : Fin (levelZero + 1) → ℝ)
    (cellConstant targetConstant qCell qTarget : ℝ)
    (hcellConstant : 0 ≤ cellConstant)
    (htargetConstant : 0 ≤ targetConstant)
    (hqCell : 0 ≤ qCell) (hqTarget : 0 ≤ qTarget)
    (htargetNonneg : ∀ ell, 0 ≤ target ell)
    (hcell : ∀ ell,
      ((cells ell).card : ℝ) ≤ cellConstant * qCell ^ ell.val)
    (htarget : ∀ ell,
      target ell ≤ targetConstant * qTarget ^ ell.val) :
    ∀ ell,
      ((cells ell).card : ℝ) * target ell ≤
        (cellConstant * targetConstant) *
          (qCell * qTarget) ^ ell.val := by
  intro ell
  calc
    ((cells ell).card : ℝ) * target ell ≤
        (cellConstant * qCell ^ ell.val) *
          (targetConstant * qTarget ^ ell.val) := by
      exact mul_le_mul (hcell ell) (htarget ell)
        (htargetNonneg ell)
        (mul_nonneg hcellConstant (pow_nonneg hqCell _))
    _ = (cellConstant * targetConstant) *
          (qCell * qTarget) ^ ell.val := by
      rw [mul_pow]
      ring

/-- Integer threshold actually used by active-scale pruning.  Scales whose
real target is at least one are rounded upward; at every inactive scale the
single centered retained point supplies the canonical threshold one. -/
noncomputable def activeCarrierPruningThreshold
    {level : Type*} (target : level → ℝ) (ell : level) : ℕ :=
  if 1 ≤ target ell then ⌈target ell⌉₊ else 1

/-- The rounded pruning threshold dominates the original nonnegative-real
target after passage to `ENNReal`.  This is the exact type bridge needed by
the WZ almost-AD lower bound: active scales use `Nat.ceil`, while at inactive
scales the canonical threshold one still dominates the target. -/
theorem ofReal_le_activeCarrierPruningThreshold
    {level : Type*} (target : level → ℝ) (ell : level) :
    ENNReal.ofReal (target ell) ≤
      (activeCarrierPruningThreshold target ell : ENNReal) := by
  by_cases hactive : 1 ≤ target ell
  · simp only [activeCarrierPruningThreshold, hactive, if_true]
    calc
      ENNReal.ofReal (target ell) ≤
          ENNReal.ofReal (⌈target ell⌉₊ : ℝ) :=
        ENNReal.ofReal_le_ofReal (Nat.le_ceil (target ell))
      _ = (⌈target ell⌉₊ : ENNReal) := by simp
  · have htarget : target ell ≤ 1 := le_of_not_ge hactive
    simp only [activeCarrierPruningThreshold, hactive, if_false]
    simpa using ENNReal.ofReal_le_ofReal htarget

/-- Real-threshold version of finite multiscale carrier pruning.  Only active
scales (`target ≥ 1`) enter the deletion ledger.  Their thresholds are rounded
up, while inactive scales are discharged by the centered point.  This is the
precise discrete formulation of the pruning step in the almost-AD argument. -/
theorem exists_active_terminal_carrier_pruning_metric_half
    {alpha beta level X : Type*} [Fintype beta] [Fintype level]
    [PseudoMetricSpace X]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (target : level → ℝ)
    (image : alpha → X) (radius : level → ℝ)
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell)
    (hbudget :
      2 * (∑ ell : ActiveCarrierPruningLevel target,
        (cells ell.1).card * ⌈target ell.1⌉₊) ≤ points.card) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  classical
  let activeCell : ActiveCarrierPruningLevel target → alpha → beta :=
    fun ell => cell ell.1
  let activeCells : ActiveCarrierPruningLevel target → Finset beta :=
    fun ell => cells ell.1
  let activeThreshold : ActiveCarrierPruningLevel target → ℕ :=
    fun ell => ⌈target ell.1⌉₊
  let activeRadius : ActiveCarrierPruningLevel target → ℝ :=
    fun ell => radius ell.1
  obtain ⟨retained, hretained, hsize, _hterminal, hmetric⟩ :=
    exists_terminal_carrier_pruning_metric_half
      activeCells points activeCell activeThreshold image activeRadius
      (by
        intro ell a ha
        exact hcell ell.1 a ha)
      (by
        intro ell a ha b hb hab
        exact hcellDiameter ell.1 a ha b hb hab)
      (by simpa [activeCells, activeThreshold] using hbudget)
  refine ⟨retained, hretained, hsize, ?_⟩
  intro ell a ha
  by_cases hactive : 1 ≤ target ell
  · let ellActive : ActiveCarrierPruningLevel target := ⟨ell, hactive⟩
    have hcountNat :
        ⌈target ell⌉₊ ≤
          (pointsInMetricClosedBall retained image a (radius ell)).card := by
      simpa [ellActive, activeThreshold, activeRadius] using
        hmetric ellActive a ha
    have hcountReal :
        (⌈target ell⌉₊ : ℝ) ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
      exact_mod_cast hcountNat
    exact (Nat.le_ceil (target ell)).trans hcountReal
  · have htarget : target ell ≤ 1 := le_of_lt (lt_of_not_ge hactive)
    have haBall :
        a ∈ pointsInMetricClosedBall retained image a (radius ell) := by
      apply Finset.mem_filter.mpr
      exact ⟨ha, by simpa using hradius ell⟩
    have honeNat :
        1 ≤ (pointsInMetricClosedBall retained image a (radius ell)).card :=
      Finset.one_le_card.mpr ⟨a, haBall⟩
    have honeReal :
        (1 : ℝ) ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
      exact_mod_cast honeNat
    exact htarget.trans honeReal

/-- Certificate-preserving form of active-scale pruning.  In addition to the
centered metric lower counts, it retains the terminal population statement
for every occupied carrier cell.  This extra conjunct is essential for
reindexing the retained marked family as a `FiniteScaleSource` and feeding it
to the full-radius WZ readback; a metric-ball lower bound alone cannot recover
the population of its distinguished carrier cell. -/
theorem exists_active_terminal_carrier_pruning_metric_half_with_cells
    {alpha beta level X : Type*} [Fintype beta] [Fintype level]
    [PseudoMetricSpace X]
    (cells : level → Finset beta) (points : Finset alpha)
    (cell : level → alpha → beta) (target : level → ℝ)
    (image : alpha → X) (radius : level → ℝ)
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell)
    (hbudget :
      2 * (∑ ell : ActiveCarrierPruningLevel target,
        (cells ell.1).card * ⌈target ell.1⌉₊) ≤ points.card) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      (∀ ell b,
        (pointsInCell retained (cell ell) b).Nonempty →
          activeCarrierPruningThreshold target ell ≤
            (pointsInCell retained (cell ell) b).card) ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  classical
  let activeCell : ActiveCarrierPruningLevel target → alpha → beta :=
    fun ell => cell ell.1
  let activeCells : ActiveCarrierPruningLevel target → Finset beta :=
    fun ell => cells ell.1
  let activeThreshold : ActiveCarrierPruningLevel target → ℕ :=
    fun ell => ⌈target ell.1⌉₊
  let activeRadius : ActiveCarrierPruningLevel target → ℝ :=
    fun ell => radius ell.1
  obtain ⟨retained, hretained, hsize, hterminal, hmetric⟩ :=
    exists_terminal_carrier_pruning_metric_half
      activeCells points activeCell activeThreshold image activeRadius
      (by
        intro ell a ha
        exact hcell ell.1 a ha)
      (by
        intro ell a ha b hb hab
        exact hcellDiameter ell.1 a ha b hb hab)
      (by simpa [activeCells, activeThreshold] using hbudget)
  refine ⟨retained, hretained, hsize, ?_, ?_⟩
  · intro ell b hnonempty
    by_cases hactive : 1 ≤ target ell
    · let ellActive : ActiveCarrierPruningLevel target := ⟨ell, hactive⟩
      simpa [activeCarrierPruningThreshold, hactive, ellActive,
        activeCell, activeThreshold] using
        hterminal ellActive b hnonempty
    · simp only [activeCarrierPruningThreshold, hactive, if_false]
      exact Finset.one_le_card.mpr hnonempty
  · intro ell a ha
    by_cases hactive : 1 ≤ target ell
    · let ellActive : ActiveCarrierPruningLevel target := ⟨ell, hactive⟩
      have hcountNat :
          ⌈target ell⌉₊ ≤
            (pointsInMetricClosedBall retained image a (radius ell)).card := by
        simpa [ellActive, activeThreshold, activeRadius] using
          hmetric ellActive a ha
      have hcountReal :
          (⌈target ell⌉₊ : ℝ) ≤
            ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
        exact_mod_cast hcountNat
      exact (Nat.le_ceil (target ell)).trans hcountReal
    · have htarget : target ell ≤ 1 := le_of_lt (lt_of_not_ge hactive)
      have haBall :
          a ∈ pointsInMetricClosedBall retained image a (radius ell) := by
        apply Finset.mem_filter.mpr
        exact ⟨ha, by simpa using hradius ell⟩
      have honeNat :
          1 ≤ (pointsInMetricClosedBall retained image a (radius ell)).card :=
        Finset.one_le_card.mpr ⟨a, haBall⟩
      have honeReal :
          (1 : ℝ) ≤
            ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
        exact_mod_cast honeNat
      exact htarget.trans honeReal

/-- Closed finite compensation ledger.  A dyadic geometric bound on the
scale-by-scale carrier charge, together with the single terminal depth
inequality, automatically supplies the integer deletion budget and hence a
half-sized terminal family with the requested real lower count at every
scale.  No recursive loss and no per-scale rounding debt remains. -/
theorem exists_dyadic_geometric_carleson_pruning_metric_half
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (points : Finset alpha)
    (cell : Fin (levelZero + 1) → alpha → beta)
    (target : Fin (levelZero + 1) → ℝ)
    (image : alpha → X) (radius : Fin (levelZero + 1) → ℝ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 1 < q)
    (hcharge : ∀ ell,
      ((cells ell).card : ℝ) * target ell ≤ K * q ^ ell.val)
    (hterminalBudget :
      4 * (K * q ^ (levelZero + 1) / (q - 1)) ≤
        (points.card : ℝ))
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  have hsum := active_carrier_geometric_charge_bound
    levelZero cells target K q hK hq hcharge
  have hrealBudget :
      4 * (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1) ≤
          (points.card : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans hterminalBudget
  have hnatBudget := active_carrier_nat_budget_of_real_budget
    cells points target hrealBudget
  exact exists_active_terminal_carrier_pruning_metric_half
    cells points cell target image radius hradius hcell hcellDiameter hnatBudget

/-- Power-separated form of the closed compensation ledger.  This is the
direct interface for a packing cover bound times a scale-dependent population
threshold: the two dyadic ratios are multiplied once, then summed by the
geometric Carleson lemma above. -/
theorem exists_dyadic_power_carleson_pruning_metric_half
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (points : Finset alpha)
    (cell : Fin (levelZero + 1) → alpha → beta)
    (target : Fin (levelZero + 1) → ℝ)
    (image : alpha → X) (radius : Fin (levelZero + 1) → ℝ)
    (cellConstant targetConstant qCell qTarget : ℝ)
    (hcellConstant : 0 ≤ cellConstant)
    (htargetConstant : 0 ≤ targetConstant)
    (hqCell : 0 ≤ qCell) (hqTarget : 0 ≤ qTarget)
    (hq : 1 < qCell * qTarget)
    (htargetNonneg : ∀ ell, 0 ≤ target ell)
    (hcellBound : ∀ ell,
      ((cells ell).card : ℝ) ≤ cellConstant * qCell ^ ell.val)
    (htargetBound : ∀ ell,
      target ell ≤ targetConstant * qTarget ^ ell.val)
    (hterminalBudget :
      4 * ((cellConstant * targetConstant) *
          (qCell * qTarget) ^ (levelZero + 1) /
            (qCell * qTarget - 1)) ≤
        (points.card : ℝ))
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  have hcharge := carrier_cell_target_product_charge
    cells target cellConstant targetConstant qCell qTarget
    hcellConstant htargetConstant hqCell hqTarget htargetNonneg
    hcellBound htargetBound
  exact exists_dyadic_geometric_carleson_pruning_metric_half
    levelZero cells points cell target image radius
    (cellConstant * targetConstant) (qCell * qTarget)
    (mul_nonneg hcellConstant htargetConstant) hq hcharge
    hterminalBudget hradius hcell hcellDiameter

/-- In the four-dimensional Kakeya application the transverse carrier cover
has exponent `3 + packingSlack`, whereas the cubic population threshold gains
the reciprocal factor `2^(-3)` at each dyadic step.  Their product is exactly
the residual Carleson ratio `2^packingSlack`; the ambient three-dimensional
power cancels rather than contributing to the terminal loss. -/
theorem packing_three_dyadic_ratio_identity (packingSlack : ℝ) :
    (2 : ℝ) ^ (3 + packingSlack) * (1 / 8 : ℝ) =
      (2 : ℝ) ^ packingSlack := by
  rw [Real.rpow_add (by norm_num) 3 packingSlack]
  norm_num [Real.rpow_natCast]
  ring

/-- Positivity of the packing slack is precisely what makes the residual
dyadic compensation series geometric with ratio strictly larger than one. -/
theorem packing_three_dyadic_ratio_gt_one
    {packingSlack : ℝ} (hpackingSlack : 0 < packingSlack) :
    1 < (2 : ℝ) ^ (3 + packingSlack) * (1 / 8 : ℝ) := by
  rw [packing_three_dyadic_ratio_identity packingSlack]
  exact Real.one_lt_rpow (by norm_num) hpackingSlack

/-- Manuscript-specific finite compensation ledger.  A transverse cover with
dyadic growth `2^((3+packingSlack) ell)` and a cubic target with dyadic decay
`2^(-3 ell)` leave only the residual ratio `2^(packingSlack ell)`.  Thus the
single displayed terminal budget closes all active scales simultaneously and
returns a half-sized family satisfying every centered lower population bound.

This is the exact finite combinatorial instantiation behind the manuscript's
`rho^(-3-packingSlack)` cover multiplied by
`delta^kappa (rho/delta)^3` target calculation. -/
theorem exists_packing_three_dyadic_carleson_pruning_metric_half
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (points : Finset alpha)
    (cell : Fin (levelZero + 1) → alpha → beta)
    (target : Fin (levelZero + 1) → ℝ)
    (image : alpha → X) (radius : Fin (levelZero + 1) → ℝ)
    (packingSlack cellConstant targetConstant : ℝ)
    (hpackingSlack : 0 < packingSlack)
    (hcellConstant : 0 ≤ cellConstant)
    (htargetConstant : 0 ≤ targetConstant)
    (htargetNonneg : ∀ ell, 0 ≤ target ell)
    (hcellBound : ∀ ell,
      ((cells ell).card : ℝ) ≤
        cellConstant * ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val)
    (htargetBound : ∀ ell,
      target ell ≤ targetConstant * (1 / 8 : ℝ) ^ ell.val)
    (hterminalBudget :
      4 * ((cellConstant * targetConstant) *
          ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) /
            ((2 : ℝ) ^ packingSlack - 1)) ≤
        (points.card : ℝ))
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  apply exists_dyadic_power_carleson_pruning_metric_half
    levelZero cells points cell target image radius
    cellConstant targetConstant
    ((2 : ℝ) ^ (3 + packingSlack)) (1 / 8 : ℝ)
    hcellConstant htargetConstant
  · positivity
  · norm_num
  · exact packing_three_dyadic_ratio_gt_one hpackingSlack
  · exact htargetNonneg
  · exact hcellBound
  · exact htargetBound
  · simpa only [packing_three_dyadic_ratio_identity] using hterminalBudget
  · exact hradius
  · exact hcell
  · exact hcellDiameter

/-- Converting the terminal dyadic depth to the physical thickness.  If
`delta = 2^(-L)`, then the last geometric factor is exactly one additional
`2^packingSlack` times `delta^(-packingSlack)`. -/
theorem dyadic_packing_slack_depth_identity
    (packingSlack : ℝ) (levelZero : ℕ) :
    ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) =
      (2 : ℝ) ^ packingSlack *
        (((2 : ℝ) ^ (-(levelZero : ℝ))) ^ (-packingSlack)) := by
  have hcore :
      ((2 : ℝ) ^ packingSlack) ^ levelZero =
        ((2 : ℝ) ^ (-(levelZero : ℝ))) ^ (-packingSlack) := by
    calc
      ((2 : ℝ) ^ packingSlack) ^ levelZero =
          ((2 : ℝ) ^ packingSlack) ^ (levelZero : ℝ) := by
            symm
            exact Real.rpow_natCast ((2 : ℝ) ^ packingSlack) levelZero
      _ = (2 : ℝ) ^ (packingSlack * (levelZero : ℝ)) := by
            symm
            exact Real.rpow_mul (by norm_num) packingSlack levelZero
      _ = (2 : ℝ) ^ ((-(levelZero : ℝ)) * (-packingSlack)) := by
            ring_nf
      _ = ((2 : ℝ) ^ (-(levelZero : ℝ))) ^ (-packingSlack) := by
            exact Real.rpow_mul (by norm_num)
              (-(levelZero : ℝ)) (-packingSlack)
  rw [pow_succ, hcore]
  ring

/-- Bridge between the dyadic notation used by `IsWZDyadicScale` and the
real-power notation used in the exponent ledger. -/
theorem dyadic_inverse_nat_pow_eq_rpow_neg (levelZero : ℕ) :
    (2 : ℝ)⁻¹ ^ levelZero =
      (2 : ℝ) ^ (-(levelZero : ℝ)) := by
  calc
    (2 : ℝ)⁻¹ ^ levelZero =
        ((2 : ℝ)⁻¹) ^ (levelZero : ℝ) := by
          symm
          exact Real.rpow_natCast ((2 : ℝ)⁻¹) levelZero
    _ = (((2 : ℝ) ^ (-1 : ℝ)) ^ (levelZero : ℝ)) := by
          rw [Real.rpow_neg_one]
    _ = (2 : ℝ) ^ ((-1 : ℝ) * (levelZero : ℝ)) := by
          symm
          exact Real.rpow_mul (by norm_num) (-1) levelZero
    _ = (2 : ℝ) ^ (-(levelZero : ℝ)) := by
          ring_nf

/-- The numerical terminal budget in physical-scale form.  The deletion
ledger contributes `delta^(-packingSlack)`, the target contributes
`delta^(kappa-3)`, and their product splits as
`delta^(kappa-packingSlack-pointSlack) delta^(-3+pointSlack)`.
Consequently the first factor is absorbed by the source-cardinality constant,
while the second is exactly the assumed point-count scale. -/
theorem packing_three_terminal_budget_of_exponent_absorption
    {alpha : Type*} (levelZero : ℕ)
    {delta packingSlack pointSlack kappa cellConstant thresholdConstant
      pointConstant : ℝ}
    (points : Finset alpha)
    (hdelta : 0 < delta)
    (hdyadic : delta = (2 : ℝ) ^ (-(levelZero : ℝ)))
    (habsorb :
      (4 * (cellConstant * thresholdConstant) *
          (2 : ℝ) ^ packingSlack /
            ((2 : ℝ) ^ packingSlack - 1)) *
        delta ^ (kappa - packingSlack - pointSlack) ≤ pointConstant)
    (hpoints :
      pointConstant * delta ^ (-3 + pointSlack) ≤
        (points.card : ℝ)) :
    4 * ((cellConstant *
          (thresholdConstant * delta ^ (kappa - 3))) *
        ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) /
          ((2 : ℝ) ^ packingSlack - 1)) ≤
      (points.card : ℝ) := by
  have hdepth :
      ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) =
        (2 : ℝ) ^ packingSlack * delta ^ (-packingSlack) := by
    rw [hdyadic]
    exact dyadic_packing_slack_depth_identity packingSlack levelZero
  have hexponents :
      delta ^ (kappa - 3) * delta ^ (-packingSlack) =
        delta ^ (kappa - packingSlack - pointSlack) *
          delta ^ (-3 + pointSlack) := by
    rw [← Real.rpow_add hdelta, ← Real.rpow_add hdelta]
    congr 1
    ring
  have hidentity :
      4 * ((cellConstant *
            (thresholdConstant * delta ^ (kappa - 3))) *
          ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) /
            ((2 : ℝ) ^ packingSlack - 1)) =
        ((4 * (cellConstant * thresholdConstant) *
            (2 : ℝ) ^ packingSlack /
              ((2 : ℝ) ^ packingSlack - 1)) *
          delta ^ (kappa - packingSlack - pointSlack)) *
            delta ^ (-3 + pointSlack) := by
    rw [hdepth]
    calc
      4 * (cellConstant * (thresholdConstant * delta ^ (kappa - 3)) *
          (2 ^ packingSlack * delta ^ (-packingSlack)) /
            (2 ^ packingSlack - 1)) =
          (4 * (cellConstant * thresholdConstant) * 2 ^ packingSlack /
            (2 ^ packingSlack - 1)) *
              (delta ^ (kappa - 3) * delta ^ (-packingSlack)) := by
                ring
      _ = (4 * (cellConstant * thresholdConstant) * 2 ^ packingSlack /
            (2 ^ packingSlack - 1)) *
              (delta ^ (kappa - packingSlack - pointSlack) *
                delta ^ (-3 + pointSlack)) := by
                rw [hexponents]
      _ = ((4 * (cellConstant * thresholdConstant) * 2 ^ packingSlack /
              (2 ^ packingSlack - 1)) *
            delta ^ (kappa - packingSlack - pointSlack)) *
              delta ^ (-3 + pointSlack) := by
                ring
  rw [hidentity]
  exact
    (mul_le_mul_of_nonneg_right habsorb (by positivity)).trans hpoints

/-- A positive exponent gap absorbs every fixed nonnegative coefficient below
one uniform positive scale.  Applied with
`gap = kappa - packingSlack - pointSlack`, this proves that the terminal
budget hypothesis above is automatic from the manuscript's strict inequality
`kappa > packingSlack + pointSlack`. -/
theorem exists_positive_rpow_absorption_threshold
    {gap coefficient pointConstant : ℝ}
    (hgap : 0 < gap) (hcoefficient : 0 ≤ coefficient)
    (hpointConstant : 0 < pointConstant) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        coefficient * delta ^ gap ≤ pointConstant := by
  have hfull :
      Tendsto (fun delta : ℝ => coefficient * delta ^ gap)
        (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hgap.ne'] using
      tendsto_const_nhds.mul
        ((Real.continuous_rpow_const hgap.le).tendsto 0)
  have hlimit :
      Tendsto (fun delta : ℝ => coefficient * delta ^ gap)
        (𝓝[>] 0) (𝓝 0) :=
    hfull.mono_left inf_le_left
  have hsmall :
      ∀ᶠ delta : ℝ in 𝓝[>] 0,
        coefficient * delta ^ gap < pointConstant :=
    (tendsto_order.1 hlimit).2 _ hpointConstant
  have hrange : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨deltaZero, hsmallZero, hdeltaZero, hdeltaZeroOne⟩ :=
    (hsmall.and hrange).exists
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaZero
  have hpowMono : delta ^ gap ≤ deltaZero ^ gap :=
    Real.rpow_le_rpow hdelta.le hdeltaZero hgap.le
  exact
    (mul_le_mul_of_nonneg_left hpowMono hcoefficient).trans hsmallZero.le

/-- The manuscript's exponent inequality in its exact compensation form.
For nonnegative cover and target constants and positive source constant,
`packingSlack + pointSlack < kappa` produces one uniform scale below which
the full geometric-series coefficient is absorbed. -/
theorem exists_packing_three_compensation_threshold
    {packingSlack pointSlack kappa cellConstant thresholdConstant
      pointConstant : ℝ}
    (hpackingSlack : 0 < packingSlack)
    (hexponentGap : packingSlack + pointSlack < kappa)
    (hcellConstant : 0 ≤ cellConstant)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointConstant : 0 < pointConstant) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        (4 * (cellConstant * thresholdConstant) *
            (2 : ℝ) ^ packingSlack /
              ((2 : ℝ) ^ packingSlack - 1)) *
          delta ^ (kappa - packingSlack - pointSlack) ≤ pointConstant := by
  have hratio : 0 < (2 : ℝ) ^ packingSlack - 1 := by
    have hone : 1 < (2 : ℝ) ^ packingSlack :=
      Real.one_lt_rpow (by norm_num) hpackingSlack
    linarith
  apply exists_positive_rpow_absorption_threshold
    (gap := kappa - packingSlack - pointSlack)
    (coefficient :=
      4 * (cellConstant * thresholdConstant) *
        (2 : ℝ) ^ packingSlack /
          ((2 : ℝ) ^ packingSlack - 1))
    (pointConstant := pointConstant)
  · linarith
  · positivity
  · exact hpointConstant

/-- Exact parameter specialization used by the cover-adapted manuscript.
The carrier cover pays `theta / 4`, the Hausdorff-layer cardinality is
weakened to the common loss `2 * theta`, and the terminal population uses
`3 * theta`.  Their strict gap is therefore automatic for every positive
`theta`; in particular the compensation-zone Carleson charge is absorbed
uniformly at all sufficiently small scales. -/
theorem exists_cover_adapted_packing_three_compensation_threshold
    {theta cellConstant thresholdConstant pointConstant : ℝ}
    (htheta : 0 < theta)
    (hcellConstant : 0 ≤ cellConstant)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointConstant : 0 < pointConstant) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        (4 * (cellConstant * thresholdConstant) *
          (2 : ℝ) ^ (theta / 4) /
              ((2 : ℝ) ^ (theta / 4) - 1)) *
          delta ^ (3 * theta - theta / 4 - 2 * theta) ≤ pointConstant := by
  apply exists_packing_three_compensation_threshold
    (packingSlack := theta / 4)
    (pointSlack := 2 * theta)
    (kappa := 3 * theta)
    (cellConstant := cellConstant)
    (thresholdConstant := thresholdConstant)
    (pointConstant := pointConstant)
  · positivity
  · linarith
  · exact hcellConstant
  · exact hthresholdConstant
  · exact hpointConstant

/-- Fixed-scale manuscript form of the compensation closure.  The target
normalization is now `thresholdConstant * delta^(kappa-3)`, and the source
lower bound is `pointConstant * delta^(-3+pointSlack)`.  The sole remaining
small-scale premise is the explicit absorption inequality supplied uniformly
by `exists_positive_rpow_absorption_threshold` whenever
`kappa > packingSlack + pointSlack`. -/
theorem exists_packing_three_dyadic_carleson_pruning_metric_half_of_absorption
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (points : Finset alpha)
    (cell : Fin (levelZero + 1) → alpha → beta)
    (target : Fin (levelZero + 1) → ℝ)
    (image : alpha → X) (radius : Fin (levelZero + 1) → ℝ)
    (delta packingSlack pointSlack kappa cellConstant thresholdConstant
      pointConstant : ℝ)
    (hdelta : 0 < delta)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hpackingSlack : 0 < packingSlack)
    (hcellConstant : 0 ≤ cellConstant)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointLower :
      pointConstant * delta ^ (-3 + pointSlack) ≤
        (points.card : ℝ))
    (habsorb :
      (4 * (cellConstant * thresholdConstant) *
          (2 : ℝ) ^ packingSlack /
            ((2 : ℝ) ^ packingSlack - 1)) *
        delta ^ (kappa - packingSlack - pointSlack) ≤ pointConstant)
    (htargetNonneg : ∀ ell, 0 ≤ target ell)
    (hcellBound : ∀ ell,
      ((cells ell).card : ℝ) ≤
        cellConstant * ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val)
    (htargetBound : ∀ ell,
      target ell ≤
        (thresholdConstant * delta ^ (kappa - 3)) *
          (1 / 8 : ℝ) ^ ell.val)
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  apply exists_packing_three_dyadic_carleson_pruning_metric_half
    levelZero cells points cell target image radius
    packingSlack cellConstant
    (thresholdConstant * delta ^ (kappa - 3))
    hpackingSlack hcellConstant
  · exact mul_nonneg hthresholdConstant (by positivity)
  · exact htargetNonneg
  · exact hcellBound
  · exact htargetBound
  · have hdyadicRpow :
        delta = (2 : ℝ) ^ (-(levelZero : ℝ)) :=
      hdyadic.trans (dyadic_inverse_nat_pow_eq_rpow_neg levelZero)
    exact packing_three_terminal_budget_of_exponent_absorption
      levelZero points hdelta hdyadicRpow habsorb hpointLower
  · exact hradius
  · exact hcell
  · exact hcellDiameter

/-- Certificate-preserving manuscript specialization.  This is the version
used by the WZ source readback: the same exponent-gap compensation argument
now returns both half-retention and the integer terminal population of every
occupied retained cell. -/
theorem exists_packing_three_dyadic_carleson_pruning_with_cells_of_absorption
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (levelZero : ℕ)
    (cells : Fin (levelZero + 1) → Finset beta)
    (points : Finset alpha)
    (cell : Fin (levelZero + 1) → alpha → beta)
    (target : Fin (levelZero + 1) → ℝ)
    (image : alpha → X) (radius : Fin (levelZero + 1) → ℝ)
    (delta packingSlack pointSlack kappa cellConstant thresholdConstant
      pointConstant : ℝ)
    (hdelta : 0 < delta)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hpackingSlack : 0 < packingSlack)
    (hcellConstant : 0 ≤ cellConstant)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointLower :
      pointConstant * delta ^ (-3 + pointSlack) ≤
        (points.card : ℝ))
    (habsorb :
      (4 * (cellConstant * thresholdConstant) *
          (2 : ℝ) ^ packingSlack /
            ((2 : ℝ) ^ packingSlack - 1)) *
        delta ^ (kappa - packingSlack - pointSlack) ≤ pointConstant)
    (htargetNonneg : ∀ ell, 0 ≤ target ell)
    (hcellBound : ∀ ell,
      ((cells ell).card : ℝ) ≤
        cellConstant * ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val)
    (htargetBound : ∀ ell,
      target ell ≤
        (thresholdConstant * delta ^ (kappa - 3)) *
          (1 / 8 : ℝ) ^ ell.val)
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hcell : ∀ ell a, a ∈ points → cell ell a ∈ cells ell)
    (hcellDiameter : ∀ ell a, a ∈ points → ∀ b ∈ points,
      cell ell b = cell ell a →
        dist (image b) (image a) ≤ radius ell) :
    ∃ retained : Finset alpha,
      retained ⊆ points ∧
      points.card ≤ 2 * retained.card ∧
      (∀ ell b,
        (pointsInCell retained (cell ell) b).Nonempty →
          activeCarrierPruningThreshold target ell ≤
            (pointsInCell retained (cell ell) b).card) ∧
      ∀ ell a, a ∈ retained →
        target ell ≤
          ((pointsInMetricClosedBall retained image a (radius ell)).card : ℝ) := by
  let targetConstant : ℝ :=
    thresholdConstant * delta ^ (kappa - 3)
  have htargetConstant : 0 ≤ targetConstant := by
    dsimp [targetConstant]
    exact mul_nonneg hthresholdConstant (by positivity)
  have hchargeRaw := carrier_cell_target_product_charge
    cells target cellConstant targetConstant
    ((2 : ℝ) ^ (3 + packingSlack)) (1 / 8 : ℝ)
    hcellConstant htargetConstant (by positivity) (by norm_num)
    htargetNonneg hcellBound (by simpa [targetConstant] using htargetBound)
  have hcharge : ∀ ell,
      ((cells ell).card : ℝ) * target ell ≤
        (cellConstant * targetConstant) *
          ((2 : ℝ) ^ packingSlack) ^ ell.val := by
    simpa only [packing_three_dyadic_ratio_identity] using hchargeRaw
  have hratio : 1 < (2 : ℝ) ^ packingSlack :=
    Real.one_lt_rpow (by norm_num) hpackingSlack
  have hsum := active_carrier_geometric_charge_bound
    levelZero cells target (cellConstant * targetConstant)
    ((2 : ℝ) ^ packingSlack)
    (mul_nonneg hcellConstant htargetConstant) hratio hcharge
  have hdyadicRpow :
      delta = (2 : ℝ) ^ (-(levelZero : ℝ)) :=
    hdyadic.trans (dyadic_inverse_nat_pow_eq_rpow_neg levelZero)
  have hterminalBudget :
      4 * ((cellConstant * targetConstant) *
          ((2 : ℝ) ^ packingSlack) ^ (levelZero + 1) /
            ((2 : ℝ) ^ packingSlack - 1)) ≤
        (points.card : ℝ) := by
    simpa [targetConstant] using
      (packing_three_terminal_budget_of_exponent_absorption
        levelZero points hdelta hdyadicRpow habsorb hpointLower)
  have hrealBudget :
      4 * (∑ ell : ActiveCarrierPruningLevel target,
        ((cells ell.1).card : ℝ) * target ell.1) ≤
          (points.card : ℝ) :=
    (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans hterminalBudget
  have hnatBudget := active_carrier_nat_budget_of_real_budget
    cells points target hrealBudget
  exact exists_active_terminal_carrier_pruning_metric_half_with_cells
    cells points cell target image radius
    hradius hcell hcellDiameter hnatBudget

/-- A finite set partitioned into at most `card beta` cells, each of
population at most `threshold`, has total population at most
`card beta * threshold`. -/
theorem finite_partition_card_bound
    {alpha beta : Type*} [Fintype beta]
    (points : Finset alpha) (cell : alpha → beta) (threshold : ℕ)
    (hfiber : ∀ b : beta,
      (pointsInCell points cell b).card ≤ threshold) :
    points.card ≤ Fintype.card beta * threshold := by
  classical
  have hmap : Set.MapsTo cell (points : Set alpha)
      ((Finset.univ : Finset beta) : Set beta) := by
    intro a ha
    simp
  calc
    points.card = ∑ b ∈ (Finset.univ : Finset beta),
          (pointsInCell points cell b).card := by
      simpa [pointsInCell] using
        (Finset.card_eq_sum_card_fiberwise hmap)
    _ ≤
        ∑ _b ∈ (Finset.univ : Finset beta), threshold := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b
    _ = Fintype.card beta * threshold := by simp

/-- A separated finite family has at most one point in every cell whose
image-diameter is strictly smaller than the separation scale.  Applied to a
finite partition of a carrier ball, this is the abstract packing step behind
the upper half of the almost-AD estimate. -/
theorem metricClosedBall_card_le_of_separated_cells
    {alpha beta X : Type*} [Fintype beta] [PseudoMetricSpace X]
    (points : Finset alpha) (image : alpha → X)
    (center : alpha) (radius delta : ℝ) (cell : alpha → beta)
    (hseparated : ∀ a ∈ points, ∀ b ∈ points,
      a ≠ b → delta ≤ dist (image a) (image b))
    (hcellDiameter :
      ∀ a ∈ pointsInMetricClosedBall points image center radius,
      ∀ b ∈ pointsInMetricClosedBall points image center radius,
        cell a = cell b → dist (image a) (image b) < delta) :
    (pointsInMetricClosedBall points image center radius).card ≤
      Fintype.card beta := by
  classical
  let ball := pointsInMetricClosedBall points image center radius
  have hballSubset : ball ⊆ points := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hfiber : ∀ c : beta,
      (pointsInCell ball cell c).card ≤ 1 := by
    intro c
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : a ∈ ball ∧ cell a = c := by
      simpa [pointsInCell] using ha
    have hb' : b ∈ ball ∧ cell b = c := by
      simpa [pointsInCell] using hb
    by_contra hne
    have hfar := hseparated a (hballSubset ha'.1)
      b (hballSubset hb'.1) hne
    have hnear := hcellDiameter a ha'.1 b hb'.1
      (ha'.2.trans hb'.2.symm)
    exact (not_lt_of_ge hfar) hnear
  have hpartition := finite_partition_card_bound ball cell 1 hfiber
  simpa [ball] using hpartition

/-- Projected form of the packing lemma.  Membership in the counted ball is
tested in `ballImage`, while separation and the small-diameter partition are
tested in `separationImage`.  For marked tubes these are respectively the
full carrier parameter `(direction, offset)` and its three-dimensional
direction projection. -/
theorem metricClosedBall_card_le_of_projected_separated_cells
    {alpha beta X Y : Type*} [Fintype beta]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (points : Finset alpha) (ballImage : alpha → X)
    (separationImage : alpha → Y)
    (center : alpha) (radius delta : ℝ) (cell : alpha → beta)
    (hseparated : ∀ a ∈ points, ∀ b ∈ points,
      a ≠ b → delta ≤ dist (separationImage a) (separationImage b))
    (hcellDiameter :
      ∀ a ∈ pointsInMetricClosedBall points ballImage center radius,
      ∀ b ∈ pointsInMetricClosedBall points ballImage center radius,
        cell a = cell b →
          dist (separationImage a) (separationImage b) < delta) :
    (pointsInMetricClosedBall points ballImage center radius).card ≤
      Fintype.card beta := by
  classical
  let ball := pointsInMetricClosedBall points ballImage center radius
  have hballSubset : ball ⊆ points := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hfiber : ∀ c : beta,
      (pointsInCell ball cell c).card ≤ 1 := by
    intro c
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : a ∈ ball ∧ cell a = c := by
      simpa [pointsInCell] using ha
    have hb' : b ∈ ball ∧ cell b = c := by
      simpa [pointsInCell] using hb
    by_contra hne
    have hfar := hseparated a (hballSubset ha'.1)
      b (hballSubset hb'.1) hne
    have hnear := hcellDiameter a ha'.1 b hb'.1
      (ha'.2.trans hb'.2.symm)
    exact (not_lt_of_ge hfar) hnear
  have hpartition := finite_partition_card_bound ball cell 1 hfiber
  simpa [ball] using hpartition

/-- Local finite-partition bound.  Unlike `finite_partition_card_bound`, this
counts only the cells which actually meet the set under consideration.  This
is the form needed for a ball of radius `r`: a global direction grid has
roughly `delta⁻³` cells, whereas only roughly `(r / delta)³` of them can meet
one spherical cap. -/
theorem finite_partition_card_bound_on_cells
    {alpha beta : Type*} (points : Finset alpha) (cells : Finset beta)
    (cell : alpha → beta) (threshold : ℕ)
    (hmap : ∀ a ∈ points, cell a ∈ cells)
    (hfiber : ∀ b ∈ cells,
      (pointsInCell points cell b).card ≤ threshold) :
    points.card ≤ cells.card * threshold := by
  classical
  have hmaps : Set.MapsTo cell (points : Set alpha) (cells : Set beta) := by
    intro a ha
    exact hmap a ha
  calc
    points.card = ∑ b ∈ cells, (pointsInCell points cell b).card := by
      simpa [pointsInCell] using
        (Finset.card_eq_sum_card_fiberwise hmaps)
    _ ≤ ∑ _b ∈ cells, threshold := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b hb
    _ = cells.card * threshold := by simp

/-- Exact chordal distance formula for the inverse stereographic map.  The
denominator is the product of the two conformal factors; in particular it is
at least `16`, which is the source of the global nonexpansion below. -/
theorem stereoInvFunAux_norm_sub_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u w : E) (hv : ‖v‖ = 1)
    (hu : u ∈ (ℝ ∙ v)ᗮ) (hw : w ∈ (ℝ ∙ v)ᗮ) :
    ‖stereoInvFunAux v u - stereoInvFunAux v w‖ ^ 2 =
      16 * ‖u - w‖ ^ 2 /
        ((‖u‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4)) := by
  have huv : ⟪v, u⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu
  have hwv : ⟪v, w⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hnormu : ‖stereoInvFunAux v u‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using stereoInvFunAux_mem hv hu
  have hnormw : ‖stereoInvFunAux v w‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using stereoInvFunAux_mem hv hw
  rw [norm_sub_sq_real, hnormu, hnormw]
  simp only [one_pow, stereoInvFunAux_apply]
  simp [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    huv, hwv, real_inner_comm, hv, norm_sub_sq_real]
  field_simp
  ring

/-- The inverse stereographic map is globally `1`-Lipschitz for chordal
distance.  Consequently stereographic coordinates never decrease distances
between points of the punctured unit sphere. -/
theorem stereoInvFunAux_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u w : E) (hv : ‖v‖ = 1)
    (hu : u ∈ (ℝ ∙ v)ᗮ) (hw : w ∈ (ℝ ∙ v)ᗮ) :
    ‖stereoInvFunAux v u - stereoInvFunAux v w‖ ≤ ‖u - w‖ := by
  have hid := stereoInvFunAux_norm_sub_sq v u w hv hu hw
  have hdenpos : 0 < (‖u‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4) := by positivity
  have hden : (16 : ℝ) ≤ (‖u‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4) := by
    nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖w‖,
      mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖w‖)]
  have hfrac :
      16 * ‖u - w‖ ^ 2 /
          ((‖u‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4)) ≤ ‖u - w‖ ^ 2 := by
    rw [div_le_iff₀ hdenpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right hden (sq_nonneg ‖u - w‖))
  have hsq : ‖stereoInvFunAux v u - stereoInvFunAux v w‖ ^ 2 ≤
      ‖u - w‖ ^ 2 := hid.trans_le hfrac
  nlinarith [norm_nonneg (stereoInvFunAux v u - stereoInvFunAux v w),
    norm_nonneg (u - w)]

/-- Stereographic coordinates based at a unit pole do not contract chordal
distance on the punctured unit sphere. -/
theorem norm_sub_le_norm_stereoToFun_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v x y : E) (hv : ‖v‖ = 1)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxv : x ≠ v) (hyv : y ≠ v) :
    ‖x - y‖ ≤ ‖stereoToFun v x - stereoToFun v y‖ := by
  let xs : sphere (0 : E) 1 :=
    ⟨x, by simpa [mem_sphere_zero_iff_norm]⟩
  let ys : sphere (0 : E) 1 :=
    ⟨y, by simpa [mem_sphere_zero_iff_norm]⟩
  have hleftx := stereo_left_inv hv (x := xs) (by simpa [xs] using hxv)
  have hlefty := stereo_left_inv hv (x := ys) (by simpa [ys] using hyv)
  have hxinv : stereoInvFunAux v (stereoToFun v x : E) = x := by
    have h := congrArg Subtype.val hleftx
    simpa [xs, stereoInvFun] using h
  have hyinv : stereoInvFunAux v (stereoToFun v y : E) = y := by
    have h := congrArg Subtype.val hlefty
    simpa [ys, stereoInvFun] using h
  have h := stereoInvFunAux_norm_sub_le v
    (stereoToFun v x : E) (stereoToFun v y : E) hv
    (stereoToFun v x).property (stereoToFun v y).property
  rw [hxinv, hyinv] at h
  simpa using h

/-- On the chordal unit cap of radius one about `v`, stereographic
coordinates based at the antipode `-v` have norm at most twice the cap
radius.  This retains the scale factor needed for the cubic packing bound. -/
theorem norm_stereoToFun_neg_le_two_mul_norm_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v x : E) (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    (hcap : ‖x - v‖ ≤ 1) :
    ‖stereoToFun (-v) x‖ ≤ 2 * ‖x - v‖ := by
  have hdxsq : ‖x - v‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (x - v)]
  have hinner : 0 ≤ ⟪v, x⟫_ℝ := by
    have hid := norm_sub_sq_real x v
    rw [hx, hv] at hid
    rw [real_inner_comm] at hid
    nlinarith
  have hden : 1 ≤ (1 : ℝ) - innerSL ℝ (-v) x := by
    simp only [innerSL_apply_apply ℝ, inner_neg_left]
    linarith
  have hdenpos : 0 < (1 : ℝ) - innerSL ℝ (-v) x :=
    lt_of_lt_of_le zero_lt_one hden
  have hcoef : ‖(2 : ℝ) / ((1 : ℝ) - innerSL ℝ (-v) x)‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hdenpos)]
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  have hpole :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
      (𝕜 := ℝ) (-v)
  have hprojv : (ℝ ∙ (-v))ᗮ.orthogonalProjectionOnto v = 0 := by
    have h := congrArg Neg.neg hpole
    simpa using h
  have hproj : ‖(ℝ ∙ (-v))ᗮ.orthogonalProjectionOnto x‖ ≤ ‖x - v‖ := by
    calc
      ‖(ℝ ∙ (-v))ᗮ.orthogonalProjectionOnto x‖ =
          ‖(ℝ ∙ (-v))ᗮ.orthogonalProjectionOnto (x - v)‖ := by
            rw [map_sub, hprojv, sub_zero]
      _ ≤ ‖x - v‖ :=
        (ℝ ∙ (-v))ᗮ.norm_orthogonalProjectionOnto_apply_le (x - v)
  rw [stereoToFun_apply, norm_smul]
  exact (mul_le_mul hcoef hproj (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- Scale-covariant Euclidean packing inequality.  Balls of radius
`delta / 2` around a `delta`-separated family are disjoint and lie in the
ball of radius `R + delta / 2`.  We retain the inequality in `ENNReal`, the
coefficient type used by the finite WZ interface. -/
theorem finset_scaled_packing_volume_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (s : Finset E) (R delta : ℝ) (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hball : ∀ c ∈ s, ‖c‖ ≤ R)
    (hseparated : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → delta ≤ ‖c - d‖) :
    (s.card : ENNReal) *
        ENNReal.ofReal ((delta / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + delta / 2) ^ finrank ℝ E) := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let small : ℝ := delta / 2
  let large : ℝ := R + delta / 2
  have hsmall : 0 < small := by
    dsimp [small]
    linarith
  have hlarge : 0 < large := by
    dsimp [large]
    linarith
  set A := ⋃ c ∈ s, Metric.ball (c : E) small with hA
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun c => Metric.ball (c : E) small) := by
    rintro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    convert hseparated c hc d hd hcd using 1
    dsimp [small]
    ring
  have hsubset : A ⊆ Metric.ball (0 : E) large := by
    refine iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    calc
      small + dist x 0 ≤ small + R := by
        rw [dist_zero_right]
        linarith [hball x hx]
      _ = large := by
        dsimp [small, large]
        ring
  have hmeasure :
      (s.card : ENNReal) *
          ENNReal.ofReal (small ^ finrank ℝ E) * μ (Metric.ball 0 1) ≤
        ENNReal.ofReal (large ^ finrank ℝ E) * μ (Metric.ball 0 1) :=
    calc
      (s.card : ENNReal) *
          ENNReal.ofReal (small ^ finrank ℝ E) * μ (Metric.ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset hdisjoint fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hsmall]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball (0 : E) large) := measure_mono hsubset
      _ = ENNReal.ofReal (large ^ finrank ℝ E) * μ (Metric.ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hlarge]
  have hcancel :
      (s.card : ENNReal) * ENNReal.ofReal (small ^ finrank ℝ E) ≤
        ENNReal.ofReal (large ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos (μ := μ) (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  simpa [small, large] using hcancel

/-- Transfer the scale-covariant packing inequality through a local chart.
The chart is required only on the finite carrier ball: its image must lie in
an `R`-ball and distinct source points must remain `delta`-separated.  In the
application `E` is a three-dimensional tangent chart for the unit sphere. -/
theorem metricClosedBall_chart_packing_volume_bound
    {alpha X E : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (points : Finset alpha) (ballImage : alpha → X)
    (center : alpha) (radius delta R : ℝ) (chart : alpha → E)
    (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hchartBall : ∀ a ∈
      pointsInMetricClosedBall points ballImage center radius,
        ‖chart a‖ ≤ R)
    (hchartSeparated :
      ∀ a ∈ pointsInMetricClosedBall points ballImage center radius,
      ∀ b ∈ pointsInMetricClosedBall points ballImage center radius,
        a ≠ b → delta ≤ ‖chart a - chart b‖) :
    ((pointsInMetricClosedBall points ballImage center radius).card : ENNReal) *
        ENNReal.ofReal ((delta / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + delta / 2) ^ finrank ℝ E) := by
  classical
  let ball := pointsInMetricClosedBall points ballImage center radius
  let charted := ball.image chart
  have hinjective : Set.InjOn chart (ball : Set alpha) := by
    intro a ha b hb hab
    by_contra hne
    have hsep := hchartSeparated a ha b hb hne
    rw [hab, sub_self, norm_zero] at hsep
    exact (not_le_of_gt hdelta) hsep
  have hcard : charted.card = ball.card := by
    exact Finset.card_image_iff.mpr hinjective
  have hbound := finset_scaled_packing_volume_bound
    charted R delta hR hdelta
    (by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      exact hchartBall a ha)
    (by
      intro c hc d hd hcd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      apply hchartSeparated a ha b hb
      intro hab
      apply hcd
      simpa [hab])
  simpa [ball, charted, hcard] using hbound

/-- A point in the chordal unit cap about a unit vector cannot be its
antipode.  This supplies the puncture condition for the stereographic chart. -/
theorem ne_neg_of_norm_sub_le_one
    (v x : E4) (hv : ‖v‖ = 1) (hcap : ‖x - v‖ ≤ 1) : x ≠ -v := by
  intro h
  rw [h] at hcap
  have htwo : ‖(-v) - v‖ = 2 := by
    rw [show (-v) - v = (-2 : ℝ) • v by module, norm_smul, hv]
    norm_num
  rw [htwo] at hcap
  norm_num at hcap

/-- Explicit three-dimensional packing bound for a finite family of unit
directions in a marked carrier ball.  Carrier membership is allowed to live
in an arbitrary metric space; only its projected-direction radius is used by
the antipodal stereographic chart.  Thus the affine fibre mark is retained in
the ball predicate while the sharp cubic exponent comes solely from `S³`. -/
theorem metricClosedBall_unitSphere_packing_volume_bound
    {alpha X : Type*} [PseudoMetricSpace X]
    (points : Finset alpha) (ballImage : alpha → X)
    (sphereImage : alpha → E4) (center : alpha)
    (radius delta : ℝ) (hradius : 0 ≤ radius) (hradiusOne : radius ≤ 1)
    (hdelta : 0 < delta)
    (hnorm : ∀ a, ‖sphereImage a‖ = 1)
    (hprojectedBall : ∀ a ∈
      pointsInMetricClosedBall points ballImage center radius,
        dist (sphereImage a) (sphereImage center) ≤ radius)
    (hseparated :
      ∀ a ∈ pointsInMetricClosedBall points ballImage center radius,
      ∀ b ∈ pointsInMetricClosedBall points ballImage center radius,
        a ≠ b → delta ≤ dist (sphereImage a) (sphereImage b)) :
    ((pointsInMetricClosedBall points ballImage center radius).card : ENNReal) *
        ENNReal.ofReal ((delta / 2) ^ 3) ≤
      ENNReal.ofReal ((2 * radius + delta / 2) ^ 3) := by
  classical
  let c := sphereImage center
  let chart : alpha → (ℝ ∙ (-c))ᗮ :=
    fun a => stereoToFun (-c) (sphereImage a)
  have hbound := metricClosedBall_chart_packing_volume_bound
    points ballImage center radius delta (2 * radius) chart
    (by positivity) hdelta
    (by
      intro a ha
      have hproj := hprojectedBall a ha
      rw [dist_eq_norm] at hproj
      have hcap : ‖sphereImage a - sphereImage center‖ ≤ 1 :=
        hproj.trans hradiusOne
      have hb := norm_stereoToFun_neg_le_two_mul_norm_sub
        (sphereImage center) (sphereImage a) (hnorm center) (hnorm a) hcap
      calc
        ‖chart a‖ =
            ‖stereoToFun (-sphereImage center) (sphereImage a)‖ := rfl
        _ ≤ 2 * ‖sphereImage a - sphereImage center‖ := hb
        _ ≤ 2 * radius :=
          mul_le_mul_of_nonneg_left hproj (by norm_num))
    (by
      intro a ha b hb hab
      have hproja := hprojectedBall a ha
      have hprojb := hprojectedBall b hb
      rw [dist_eq_norm] at hproja hprojb
      have hacap : ‖sphereImage a - sphereImage center‖ ≤ 1 :=
        hproja.trans hradiusOne
      have hbcap : ‖sphereImage b - sphereImage center‖ ≤ 1 :=
        hprojb.trans hradiusOne
      have hane := ne_neg_of_norm_sub_le_one
        (sphereImage center) (sphereImage a) (hnorm center) hacap
      have hbne := ne_neg_of_norm_sub_le_one
        (sphereImage center) (sphereImage b) (hnorm center) hbcap
      have hexpand := norm_sub_le_norm_stereoToFun_sub
        (-sphereImage center) (sphereImage a) (sphereImage b)
        (by simpa using hnorm center) (hnorm a) (hnorm b) hane hbne
      have hsep := hseparated a ha b hb hab
      rw [dist_eq_norm] at hsep
      exact hsep.trans hexpand)
  have hcne : -c ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [c, hnorm center])
  letI : Fact (finrank ℝ E4 = 3 + 1) := ⟨by simp [E4]⟩
  have hdim : finrank ℝ (ℝ ∙ (-c))ᗮ = 3 :=
    Submodule.finrank_orthogonal_span_singleton hcne
  simpa [hdim] using hbound

/-- Cancel the positive small-ball volume in the cubic packing estimate.
The hypothesis `delta ≤ radius` is the scale range used by the finite WZ
interface; it turns the enlarged radius `2 * radius + delta / 2` into the
explicit harmless constant `5 / 2`. -/
theorem ennreal_count_le_five_mul_ratio_cubed
    (N : ENNReal) {radius delta : ℝ}
    (hradius : 0 ≤ radius) (hdelta : 0 < delta)
    (hdeltaRadius : delta ≤ radius)
    (hpacking : N * ENNReal.ofReal ((delta / 2) ^ 3) ≤
      ENNReal.ofReal ((2 * radius + delta / 2) ^ 3)) :
    N ≤ ENNReal.ofReal ((5 * radius / delta) ^ 3) := by
  have hbase : 0 ≤ 2 * radius + delta / 2 := by positivity
  have hbaseLe : 2 * radius + delta / 2 ≤ 5 * radius / 2 := by
    linarith
  have hreal :
      (2 * radius + delta / 2) ^ 3 ≤ (5 * radius / 2) ^ 3 := by
    gcongr
  have hfactor :
      ((5 * radius / delta) ^ 3) * ((delta / 2) ^ 3) =
        (5 * radius / 2) ^ 3 := by
    field_simp
  have hlarge :
      ENNReal.ofReal ((2 * radius + delta / 2) ^ 3) ≤
        ENNReal.ofReal ((5 * radius / delta) ^ 3) *
          ENNReal.ofReal ((delta / 2) ^ 3) := by
    rw [← ENNReal.ofReal_mul
      (by positivity : 0 ≤ (5 * radius / delta) ^ 3), hfactor]
    exact ENNReal.ofReal_le_ofReal hreal
  have hmul :
      N * ENNReal.ofReal ((delta / 2) ^ 3) ≤
        ENNReal.ofReal ((5 * radius / delta) ^ 3) *
          ENNReal.ofReal ((delta / 2) ^ 3) :=
    hpacking.trans hlarge
  have hsmall0 : ENNReal.ofReal ((delta / 2) ^ 3) ≠ 0 := by
    positivity
  have hsmallTop : ENNReal.ofReal ((delta / 2) ^ 3) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_left hsmall0 hsmallTop).1 hmul

/-- Finite-source specialization of the `S³` packing estimate.  The count
is exactly the WZ full-carrier ball count; projection to direction costs no
radius factor because the product carrier metric dominates its first
coordinate. -/
theorem finite_source_carrier_unitSphere_packing_volume_bound
    {n : ℕ} (D : FiniteScaleSource n)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (center : Fin n) (radius delta : ℝ)
    (hradius : 0 ≤ radius) (hradiusOne : radius ≤ 1) (hdelta : 0 < delta)
    (hseparated : ∀ a b, a ≠ b →
      delta ≤ dist (direction (D.line a)) (direction (D.line b))) :
    (wzCarrierBallCount D center radius : ENNReal) *
        ENNReal.ofReal ((delta / 2) ^ 3) ≤
      ENNReal.ofReal ((2 * radius + delta / 2) ^ 3) := by
  have hbound := metricClosedBall_unitSphere_packing_volume_bound
    (Finset.univ : Finset (Fin n)) (wzCarrierPoint D)
    (fun i => direction (D.line i)) center radius delta
    hradius hradiusOne hdelta (fun i => (hvalid i).1)
    (by
      intro a ha
      have hfull :
          dist (wzCarrierPoint D a) (wzCarrierPoint D center) ≤ radius :=
        (Finset.mem_filter.mp ha).2
      calc
        dist (direction (D.line a)) (direction (D.line center)) ≤
            dist (wzCarrierPoint D a) (wzCarrierPoint D center) := by
              rw [wzCarrierPoint, Prod.dist_eq]
              exact le_max_left _ _
        _ ≤ radius := hfull)
    (by
      intro a _ha b _hb hab
      exact hseparated a b hab)
  simpa using hbound

/-- Direct cubic WZ carrier-count consequence of spherical packing.  The
affine fibre remains part of `wzCarrierBallCount`; only the separated unit
directions are used to control its cardinality. -/
theorem finite_source_carrier_count_le_five_mul_ratio_cubed
    {n : ℕ} (D : FiniteScaleSource n)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (center : Fin n) (radius delta : ℝ)
    (hradius : 0 ≤ radius) (hradiusOne : radius ≤ 1)
    (hdelta : 0 < delta) (hdeltaRadius : delta ≤ radius)
    (hseparated : ∀ a b, a ≠ b →
      delta ≤ dist (direction (D.line a)) (direction (D.line b))) :
    (wzCarrierBallCount D center radius : ENNReal) ≤
      ENNReal.ofReal ((5 * radius / delta) ^ 3) := by
  apply ennreal_count_le_five_mul_ratio_cubed
    (wzCarrierBallCount D center radius : ENNReal)
    hradius hdelta hdeltaRadius
  exact finite_source_carrier_unitSphere_packing_volume_bound
    D hvalid center radius delta hradius hradiusOne hdelta hseparated

/-- Absorb the fixed spherical-packing constant into the negative subpower
allowed by the finite WZ interface.  This lemma isolates the only numerical
small-scale requirement: `delta ^ (-eta)` must dominate `5^3 = 125`. -/
theorem ennreal_count_le_subpower_mul_ratio_cubed
    (N : ENNReal) {radius delta eta : ℝ}
    (hradius : 0 ≤ radius) (hdelta : 0 < delta)
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (hcount : N ≤ ENNReal.ofReal ((5 * radius / delta) ^ 3)) :
    N ≤ (ENNReal.ofReal delta).rpow (-eta) *
      (ENNReal.ofReal (radius / delta)) ^ 3 := by
  have hfactor :
      ENNReal.ofReal ((5 * radius / delta) ^ 3) =
        125 * (ENNReal.ofReal (radius / delta)) ^ 3 := by
    rw [ENNReal.ofReal_pow (by positivity)]
    rw [show 5 * radius / delta = 5 * (radius / delta) by ring]
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
    ring
  calc
    N ≤ ENNReal.ofReal ((5 * radius / delta) ^ 3) := hcount
    _ = 125 * (ENNReal.ofReal (radius / delta)) ^ 3 := hfactor
    _ ≤ (ENNReal.ofReal delta).rpow (-eta) *
        (ENNReal.ofReal (radius / delta)) ^ 3 := by
      calc
        125 * (ENNReal.ofReal (radius / delta)) ^ 3 =
            (ENNReal.ofReal (radius / delta)) ^ 3 * 125 := mul_comm _ _
        _ ≤ (ENNReal.ofReal (radius / delta)) ^ 3 *
            (ENNReal.ofReal delta).rpow (-eta) :=
          mul_le_mul_right habsorb _
        _ = (ENNReal.ofReal delta).rpow (-eta) *
            (ENNReal.ofReal (radius / delta)) ^ 3 := mul_comm _ _

/-- Every positive loss exponent absorbs the fixed spherical-packing
constant below one uniform positive scale.  Thus the numerical hypothesis in
`ennreal_count_le_subpower_mul_ratio_cubed` is automatic after shrinking the
WZ threshold once, rather than being an additional source assumption. -/
theorem exists_subpower_absorption_threshold {eta : ℝ} (heta : 0 < eta) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaZero →
        (125 : ENNReal) ≤ (ENNReal.ofReal delta).rpow (-eta) := by
  have hofReal :
      Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0)
  have hpowZero :
      Tendsto (fun x : ENNReal => x.rpow eta) (𝓝 0) (𝓝 0) := by
    simpa using
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
        (c := (1 : ENNReal)) (by norm_num) heta)
  have hlimit :
      Tendsto (fun r : ℝ => (ENNReal.ofReal r).rpow eta)
        (𝓝[>] 0) (𝓝 0) :=
    (hpowZero.comp hofReal).mono_left inf_le_left
  have hinvPositive : (0 : ENNReal) < (125 : ENNReal)⁻¹ := by
    norm_num
  have hsmall :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        (ENNReal.ofReal r).rpow eta < (125 : ENNReal)⁻¹ :=
    (tendsto_order.1 hlimit).2 _ hinvPositive
  have hrange : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨deltaZero, hsmallZero, hdeltaZero, hdeltaZeroOne⟩ :=
    (hsmall.and hrange).exists
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaZero
  have hpowMono :
      (ENNReal.ofReal delta).rpow eta ≤
        (ENNReal.ofReal deltaZero).rpow eta :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdeltaZero) heta.le
  have hpowInv :
      (ENNReal.ofReal delta).rpow eta ≤ (125 : ENNReal)⁻¹ :=
    hpowMono.trans hsmallZero.le
  have hmul :
      (125 : ENNReal) * (ENNReal.ofReal delta).rpow eta ≤ 1 := by
    calc
      (125 : ENNReal) * (ENNReal.ofReal delta).rpow eta ≤
          125 * (125 : ENNReal)⁻¹ := mul_le_mul_right hpowInv 125
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hinv :
      (125 : ENNReal) ≤ ((ENNReal.ofReal delta).rpow eta)⁻¹ :=
    ENNReal.le_inv_iff_mul_le.mpr hmul
  exact hinv.trans_eq (ENNReal.rpow_neg _ eta).symm

/-- The projected `S³` packing theorem in exactly the upper-count form
required by `IsWangZakharovFiniteInput`, once the fixed constant has been
absorbed at the selected thickness. -/
theorem finite_source_carrier_count_le_subpower_ratio_cubed
    {n : ℕ} (D : FiniteScaleSource n)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (center : Fin n) (radius eta : ℝ)
    (hradius : 0 ≤ radius) (hradiusOne : radius ≤ 1)
    (hdelta : 0 < D.thickness)
    (hdeltaRadius : D.thickness ≤ radius)
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta))
    (hseparated : ∀ a b, a ≠ b →
      D.thickness ≤
        dist (direction (D.line a)) (direction (D.line b))) :
    (wzCarrierBallCount D center radius : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta) *
        (ENNReal.ofReal (radius / D.thickness)) ^ 3 := by
  apply ennreal_count_le_subpower_mul_ratio_cubed
    (wzCarrierBallCount D center radius : ENNReal)
    hradius hdelta habsorb
  exact finite_source_carrier_count_le_five_mul_ratio_cubed
    D hvalid center radius D.thickness hradius hradiusOne
    hdelta hdeltaRadius hseparated

/-- Uniform small-scale form of the carrier upper count.  For a fixed
positive `eta`, the returned `deltaZero` works simultaneously for every
finite source, every centre, and every radius in the WZ range. -/
theorem exists_uniform_finite_source_carrier_upper_threshold
    {eta : ℝ} (heta : 0 < eta) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
      ∀ {n : ℕ} (D : FiniteScaleSource n),
        D.thickness ≤ deltaZero →
        (∀ i, IsValidLine (D.line i)) →
        (∀ a b, a ≠ b →
          D.thickness ≤
            dist (direction (D.line a)) (direction (D.line b))) →
        ∀ (center : Fin n) (radius : ℝ),
          0 ≤ radius → radius ≤ 1 →
          0 < D.thickness → D.thickness ≤ radius →
          (wzCarrierBallCount D center radius : ENNReal) ≤
            (ENNReal.ofReal D.thickness).rpow (-eta) *
              (ENNReal.ofReal (radius / D.thickness)) ^ 3 := by
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, habsorb⟩ :=
    exists_subpower_absorption_threshold heta
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro n D hthickness hvalid hseparated center radius
    hradius hradiusOne hdelta hdeltaRadius
  exact finite_source_carrier_count_le_subpower_ratio_cubed
    D hvalid center radius eta hradius hradiusOne hdelta hdeltaRadius
    (habsorb D.thickness hdelta hthickness) hseparated

/-- Exact almost-AD readback from terminal carrier pruning and spherical
packing.  The lower bound uses the actual terminal population of the
cover-adapted carrier cell; the upper bound uses the full marked carrier ball
and only projects to the unit direction sphere for packing. -/
theorem finite_source_terminal_pruning_gives_wz_almostAD
    {n : ℕ} {beta level : Type*}
    (D : FiniteScaleSource n) (lowerCell : level → Fin n → beta)
    (threshold : level → ℕ) (radius : level → ℝ) (eta : ℝ)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell (Finset.univ : Finset (Fin n))
        (lowerCell ell) b).Nonempty →
          threshold ell ≤
            (pointsInCell (Finset.univ : Finset (Fin n))
              (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, ∀ b,
      lowerCell ell b = lowerCell ell a →
        dist (wzCarrierPoint D b) (wzCarrierPoint D a) ≤ radius ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (radius ell / D.thickness)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hseparated : ∀ a b, a ≠ b →
      D.thickness ≤
        dist (direction (D.line a)) (direction (D.line b)))
    (hradius : ∀ ell, 0 ≤ radius ell)
    (hradiusOne : ∀ ell, radius ell ≤ 1)
    (hdelta : 0 < D.thickness)
    (hdeltaRadius : ∀ ell, D.thickness ≤ radius ell)
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta)) :
    ∀ ell i,
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (radius ell / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i (radius ell) : ENNReal) ∧
      (wzCarrierBallCount D i (radius ell) : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (radius ell / D.thickness)) ^ 3 := by
  intro ell i
  have hlowerNat :
      threshold ell ≤ wzCarrierBallCount D i (radius ell) := by
    have h := terminal_carrier_pruning_metric_lower_count
      (Finset.univ : Finset (Fin n)) lowerCell threshold
      (wzCarrierPoint D) radius hterminal
      (by
        intro ell' a _ha b _hb hab
        exact hlowerDiameter ell' a b hab)
      ell i (by simp)
    simpa using h
  have hlowerCast :
      (threshold ell : ENNReal) ≤
        (wzCarrierBallCount D i (radius ell) : ENNReal) := by
    exact_mod_cast hlowerNat
  constructor
  · exact (hlowerThreshold ell).trans hlowerCast
  · exact finite_source_carrier_count_le_subpower_ratio_cubed
      D hvalid i (radius ell) eta (hradius ell) (hradiusOne ell)
      hdelta (hdeltaRadius ell) habsorb hseparated

/-- Carrier-ball counts are monotone in the radius. -/
theorem wzCarrierBallCount_mono_radius
    {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    {r R : ℝ} (hrR : r ≤ R) :
    wzCarrierBallCount D i r ≤ wzCarrierBallCount D i R := by
  classical
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ j, hj.2.trans hrR⟩

/-- The finite dyadic radius family associated with a thickness level. -/
noncomputable def wzDyadicRadius (levelZero : ℕ) (ell : Fin (levelZero + 1)) : ℝ :=
  (2 : ℝ)⁻¹ ^ ell.val

/-- The packing-three pruning target is exactly the WZ almost-AD lower
threshold at the dyadic carrier radii.  Here `delta` is the physical tube
thickness, and the WZ exponent is `3 * theta`; the numerical factor eight is
the cube of the radius inflation appearing in the finite WZ interface. -/
theorem cover_adapted_active_threshold_gives_wz_lower
    (levelZero : ℕ) (ell : Fin (levelZero + 1))
    (delta theta : ℝ) (hdelta : 0 < delta) :
    (ENNReal.ofReal delta).rpow (3 * theta) *
        (ENNReal.ofReal
          ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
      (activeCarrierPruningThreshold
        (fun j : Fin (levelZero + 1) =>
          (8 * delta ^ (3 * theta - 3)) *
            (1 / 8 : ℝ) ^ j.val) ell : ENNReal) := by
  have hradiusCube :
      (wzDyadicRadius levelZero ell) ^ (3 : ℕ) =
        (1 / 8 : ℝ) ^ ell.val := by
    calc
      (wzDyadicRadius levelZero ell) ^ (3 : ℕ) =
          (((2 : ℝ)⁻¹) ^ ell.val) ^ (3 : ℕ) := by
            rfl
      _ = ((2 : ℝ)⁻¹) ^ (ell.val * 3) := by
            exact (pow_mul ((2 : ℝ)⁻¹) ell.val 3).symm
      _ = ((2 : ℝ)⁻¹) ^ (3 * ell.val) := by
            rw [Nat.mul_comm]
      _ = ((((2 : ℝ)⁻¹) ^ (3 : ℕ)) ^ ell.val) := by
            exact pow_mul ((2 : ℝ)⁻¹) 3 ell.val
      _ = (1 / 8 : ℝ) ^ ell.val := by norm_num
  have hreal :
      delta ^ (3 * theta) *
          (((2 * wzDyadicRadius levelZero ell) / delta) ^ (3 : ℕ)) =
        (8 * delta ^ (3 * theta - 3)) *
          (1 / 8 : ℝ) ^ ell.val := by
    rw [div_pow, mul_pow, hradiusCube, Real.rpow_sub hdelta]
    norm_num
    field_simp
    <;> ring
  have hdeltaRpow :
      (ENNReal.ofReal delta).rpow (3 * theta) =
        ENNReal.ofReal (delta ^ (3 * theta)) := by
    change ENNReal.ofReal delta ^ (3 * theta) =
      ENNReal.ofReal (delta ^ (3 * theta))
    exact ENNReal.ofReal_rpow_of_pos hdelta
  have hradiusPos : 0 < wzDyadicRadius levelZero ell := by
    simp only [wzDyadicRadius]
    positivity
  have hratioNonneg :
      0 ≤ (2 * wzDyadicRadius levelZero ell) / delta := by
    positivity
  have hdeltaPowerNonneg : 0 ≤ delta ^ (3 * theta) :=
    Real.rpow_nonneg hdelta.le _
  calc
    (ENNReal.ofReal delta).rpow (3 * theta) *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 =
        ENNReal.ofReal
          (delta ^ (3 * theta) *
            (((2 * wzDyadicRadius levelZero ell) / delta) ^ (3 : ℕ))) := by
      rw [hdeltaRpow]
      rw [← ENNReal.ofReal_pow hratioNonneg]
      rw [← ENNReal.ofReal_mul hdeltaPowerNonneg]
    _ = ENNReal.ofReal
          ((8 * delta ^ (3 * theta - 3)) *
            (1 / 8 : ℝ) ^ ell.val) := by rw [hreal]
    _ ≤ (activeCarrierPruningThreshold
          (fun j : Fin (levelZero + 1) =>
            (8 * delta ^ (3 * theta - 3)) *
              (1 / 8 : ℝ) ^ j.val) ell : ENNReal) :=
      ofReal_le_activeCarrierPruningThreshold _ ell

/-- If `delta = 2⁻ˡ`, the `L + 1` radii `1, 2⁻¹, ..., 2⁻ˡ` form a
factor-two inner net of the whole interval `[delta, 1]`. -/
theorem wzDyadicRadius_covers_interval
    (levelZero : ℕ) {delta r : ℝ}
    (hdelta : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hdeltaRadius : delta ≤ r) (hradiusOne : r ≤ 1) :
    ∃ ell : Fin (levelZero + 1),
      wzDyadicRadius levelZero ell ≤ r ∧
        r ≤ 2 * wzDyadicRadius levelZero ell := by
  classical
  let p : ℕ → Prop := fun k => (2 : ℝ)⁻¹ ^ k ≤ r
  have hpLevel : p levelZero := by
    dsimp [p]
    simpa [hdelta] using hdeltaRadius
  have hexists : ∃ k, p k := ⟨levelZero, hpLevel⟩
  let k := Nat.find hexists
  have hk : p k := Nat.find_spec hexists
  have hkLevel : k ≤ levelZero := Nat.find_min' hexists hpLevel
  refine ⟨⟨k, Nat.lt_succ_of_le hkLevel⟩, hk, ?_⟩
  simp only [wzDyadicRadius]
  by_cases hkZero : k = 0
  · rw [hkZero]
    norm_num
    exact hradiusOne.trans (by norm_num)
  · obtain ⟨m, hkm⟩ := Nat.exists_eq_succ_of_ne_zero hkZero
    have hmlt : m < k := by omega
    have hnot : ¬ p m := Nat.find_min hexists hmlt
    have hrlt : r < (2 : ℝ)⁻¹ ^ m := by
      exact lt_of_not_ge hnot
    have heq : (2 : ℝ)⁻¹ ^ m =
        2 * ((2 : ℝ)⁻¹ ^ (m + 1)) := by
      rw [pow_succ]
      ring
    rw [hkm]
    exact hrlt.le.trans_eq heq

/-- Unpack the dyadic-thickness predicate into the finite factor-two radius
mesh used by the full-radius readback. -/
theorem isWZDyadicScale_has_finite_radius_mesh
    {delta : ℝ} (hdyadic : IsWZDyadicScale delta) :
    ∃ levelZero : ℕ,
      delta = (2 : ℝ)⁻¹ ^ levelZero ∧
      ∀ r : ℝ, delta ≤ r → r ≤ 1 →
        ∃ ell : Fin (levelZero + 1),
          wzDyadicRadius levelZero ell ≤ r ∧
            r ≤ 2 * wzDyadicRadius levelZero ell := by
  obtain ⟨levelZero, hlevelZero⟩ := hdyadic
  refine ⟨levelZero, hlevelZero, ?_⟩
  intro r hdeltaRadius hradiusOne
  exact wzDyadicRadius_covers_interval levelZero hlevelZero
    hdeltaRadius hradiusOne

/-- Full-radius WZ almost-AD readback.  A finite family of terminal radii
cofinal up to a factor two controls every radius in `[thickness, 1]`:
monotonicity enlarges the carrier ball, while the threshold is evaluated at
twice the selected radius and hence already contains the sole factor `2^3`.
The upper bound remains the direct spherical-packing estimate at the queried
radius. -/
theorem finite_source_terminal_pruning_gives_full_wz_almostAD
    {n : ℕ} {beta level : Type*}
    (D : FiniteScaleSource n) (lowerCell : level → Fin n → beta)
    (threshold : level → ℕ) (radius : level → ℝ) (eta : ℝ)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell (Finset.univ : Finset (Fin n))
        (lowerCell ell) b).Nonempty →
          threshold ell ≤
            (pointsInCell (Finset.univ : Finset (Fin n))
              (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, ∀ b,
      lowerCell ell b = lowerCell ell a →
        dist (wzCarrierPoint D b) (wzCarrierPoint D a) ≤ radius ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal ((2 * radius ell) / D.thickness)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hscaleCover : ∀ r : ℝ,
      D.thickness ≤ r → r ≤ 1 →
        ∃ ell : level, radius ell ≤ r ∧ r ≤ 2 * radius ell)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hseparated : ∀ a b, a ≠ b →
      D.thickness ≤
        dist (direction (D.line a)) (direction (D.line b)))
    (hdelta : 0 < D.thickness)
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta)) :
    ∀ i r, D.thickness ≤ r → r ≤ 1 →
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i r : ENNReal) ∧
      (wzCarrierBallCount D i r : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 := by
  intro i r hdeltaRadius hradiusOne
  obtain ⟨ell, hradiusLe, hradiusDouble⟩ :=
    hscaleCover r hdeltaRadius hradiusOne
  have hlowerNat :
      threshold ell ≤ wzCarrierBallCount D i (radius ell) := by
    have h := terminal_carrier_pruning_metric_lower_count
      (Finset.univ : Finset (Fin n)) lowerCell threshold
      (wzCarrierPoint D) radius hterminal
      (by
        intro ell' a _ha b _hb hab
        exact hlowerDiameter ell' a b hab)
      ell i (by simp)
    simpa using h
  have hlowerCast :
      (threshold ell : ENNReal) ≤
        (wzCarrierBallCount D i (radius ell) : ENNReal) := by
    exact_mod_cast hlowerNat
  have hratio :
      r / D.thickness ≤ (2 * radius ell) / D.thickness :=
    (div_le_div_iff_of_pos_right hdelta).2 hradiusDouble
  have hratioENN :
      ENNReal.ofReal (r / D.thickness) ≤
        ENNReal.ofReal ((2 * radius ell) / D.thickness) :=
    ENNReal.ofReal_le_ofReal hratio
  have htargetMono :
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal ((2 * radius ell) / D.thickness)) ^ 3 :=
    mul_le_mul_right (pow_le_pow_left' hratioENN 3) _
  constructor
  · calc
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal ((2 * radius ell) / D.thickness)) ^ 3 :=
        htargetMono
      _ ≤ (threshold ell : ENNReal) := hlowerThreshold ell
      _ ≤ (wzCarrierBallCount D i (radius ell) : ENNReal) := hlowerCast
      _ ≤ (wzCarrierBallCount D i r : ENNReal) := by
        exact_mod_cast wzCarrierBallCount_mono_radius D i hradiusLe
  · exact finite_source_carrier_count_le_subpower_ratio_cubed
      D hvalid i r eta (le_trans hdelta.le hdeltaRadius) hradiusOne
      hdelta hdeltaRadius habsorb hseparated

/-- Dyadic specialization of the full-radius readback.  Once the thickness is
`2⁻ᴸ`, the radii indexed by `Fin (L + 1)` automatically supply the factor-two
inner mesh, so no separate scale-cover hypothesis remains in the interface. -/
theorem finite_source_dyadic_terminal_pruning_gives_full_wz_almostAD
    {n : ℕ} {beta : Type*} {levelZero : ℕ}
    (D : FiniteScaleSource n)
    (lowerCell : Fin (levelZero + 1) → Fin n → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta : ℝ)
    (hthickness : D.thickness = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ (ell : Fin (levelZero + 1)) (b : beta),
      (pointsInCell (Finset.univ : Finset (Fin n))
        (lowerCell ell) b).Nonempty →
          threshold ell ≤
            (pointsInCell (Finset.univ : Finset (Fin n))
              (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, ∀ b,
      lowerCell ell b = lowerCell ell a →
        dist (wzCarrierPoint D b) (wzCarrierPoint D a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / D.thickness)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hseparated : ∀ a b, a ≠ b →
      D.thickness ≤
        dist (direction (D.line a)) (direction (D.line b)))
    (hdelta : 0 < D.thickness)
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta)) :
    ∀ i r, D.thickness ≤ r → r ≤ 1 →
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i r : ENNReal) ∧
      (wzCarrierBallCount D i r : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 := by
  apply finite_source_terminal_pruning_gives_full_wz_almostAD
    D lowerCell threshold (wzDyadicRadius levelZero) eta
    hterminal hlowerDiameter hlowerThreshold
  · intro r hdeltaRadius hradiusOne
    exact wzDyadicRadius_covers_interval levelZero hthickness
      hdeltaRadius hradiusOne
  · exact hvalid
  · exact hseparated
  · exact hdelta
  · exact habsorb

/-- Source-level readback for a pruned marked family.  This theorem is the
missing interface between the terminal carrier-cell certificate and the
finite WZ hypothesis: it canonically reindexes the retained marked lines,
preserves the affine marks, transports every terminal fibre cardinality, and
delivers the two-sided almost-AD carrier count at every physical radius. -/
theorem retained_wz_source_dyadic_terminal_pruning_gives_full_wz_almostAD
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hdelta : 0 < delta)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal delta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta)) :
    let D := retainedWZCellSource delta retained shadingCells hdelta hseparated
    ∀ i r, D.thickness ≤ r → r ≤ 1 →
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i r : ENNReal) ∧
      (wzCarrierBallCount D i r : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 := by
  let D := retainedWZCellSource delta retained shadingCells hdelta hseparated
  apply finite_source_dyadic_terminal_pruning_gives_full_wz_almostAD
    D (fun ell i => lowerCell ell (retainedIndex retained i)) threshold eta
  · exact hdyadic
  · exact terminal_population_reindex retained lowerCell threshold hterminal
  · intro ell a b hab
    exact hlowerDiameter ell (retainedIndex retained a)
      (retainedIndex_mem retained a) (retainedIndex retained b)
      (retainedIndex_mem retained b) hab
  · exact hlowerThreshold
  · intro i
    exact hvalid (retainedIndex retained i) (retainedIndex_mem retained i)
  · intro a b hab
    exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
      (retainedIndex retained b) (retainedIndex_mem retained b)
      (fun h => hab (retainedIndex_injective retained h))
  · exact hdelta
  · exact habsorb

/-- The almost-AD pruning ledger depends on the physical tube scale and the
marked carrier only, not on the mesh used to write the shading.  Hence it
applies verbatim to the scale-honest source with cell scale `cellDelta`. -/
theorem retained_wz_sourceAtScales_dyadic_terminal_pruning_gives_full_wz_almostAD
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta tubeDelta cellDelta : ℝ)
    (htubeDelta : 0 < tubeDelta)
    (htubeDyadic : tubeDelta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal tubeDelta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / tubeDelta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      tubeDelta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal tubeDelta).rpow (-eta)) :
    let D := retainedWZCellSourceAtScales tubeDelta cellDelta retained
      shadingCells htubeDelta hseparated
    ∀ i r, D.thickness ≤ r → r ≤ 1 →
      (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i r : ENNReal) ∧
      (wzCarrierBallCount D i r : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (r / D.thickness)) ^ 3 := by
  let D := retainedWZCellSourceAtScales tubeDelta cellDelta retained
    shadingCells htubeDelta hseparated
  apply finite_source_dyadic_terminal_pruning_gives_full_wz_almostAD
    D (fun ell i => lowerCell ell (retainedIndex retained i)) threshold eta
  · exact htubeDyadic
  · exact terminal_population_reindex retained lowerCell threshold hterminal
  · intro ell a b hab
    exact hlowerDiameter ell (retainedIndex retained a)
      (retainedIndex_mem retained a) (retainedIndex retained b)
      (retainedIndex_mem retained b) hab
  · exact hlowerThreshold
  · intro i
    exact hvalid (retainedIndex retained i) (retainedIndex_mem retained i)
  · intro a b hab
    exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
      (retainedIndex retained b) (retainedIndex_mem retained b)
      (fun h => hab (retainedIndex_injective retained h))
  · exact htubeDelta
  · exact habsorb

/-- Pointwise tube-density lower bounds sum to the aggregate density clause in
the finite WZ interface. -/
theorem wz_shading_density_of_pointwise
    {n : ℕ} (D : FiniteScaleSource n) (eta : ℝ)
    (hpointwise : ∀ i,
      (ENNReal.ofReal D.thickness).rpow eta *
          volume (markedUnitTube (D.line i) D.thickness) ≤
        volume (D.shading i)) :
    (ENNReal.ofReal D.thickness).rpow eta * wzTotalTubeVolume D ≤
      wzTotalShadingVolume D := by
  unfold wzTotalTubeVolume wzTotalShadingVolume
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi => hpointwise i

/-- A finite longitudinal allocation with per-cell mass at most `deltaMass`
forces the total assigned mass to be paid by the number of occupied cells. -/
theorem longitudinal_mass_le_card_mul_delta
    {alpha : Type*} (cells : Finset alpha)
    (cellMass : alpha → ENNReal) (deltaMass totalMass : ENNReal)
    (hcap : ∀ k ∈ cells, cellMass k ≤ deltaMass)
    (hcover : totalMass ≤ ∑ k ∈ cells, cellMass k) :
    totalMass ≤ (cells.card : ENNReal) * deltaMass := by
  calc
    totalMass ≤ ∑ k ∈ cells, cellMass k := hcover
    _ ≤ ∑ _k ∈ cells, deltaMass := by
      exact Finset.sum_le_sum fun k hk => hcap k hk
    _ = (cells.card : ENNReal) * deltaMass := by simp

/-- The assigned longitudinal mass and the one-cell longitudinal capacity
imply the exact cubical cell-count lower bound used by the WZ density clause. -/
theorem wz_cell_count_density_of_longitudinal_allocation
    {alpha : Type*} (delta eta : ℝ) (cells : Finset alpha)
    (cellMass : alpha → ENNReal) (totalMass : ENNReal)
    (hactive :
      (ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤ totalMass)
    (hcover : totalMass ≤ ∑ k ∈ cells, cellMass k)
    (hcap : ∀ k ∈ cells,
      cellMass k ≤ ENNReal.ofReal delta) :
    (ENNReal.ofReal delta).rpow eta *
        (32 * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
      (cells.card : ENNReal) * (ENNReal.ofReal delta) ^ 4 := by
  have hlong : totalMass ≤
      (cells.card : ENNReal) * ENNReal.ofReal delta :=
    longitudinal_mass_le_card_mul_delta
      cells cellMass (ENNReal.ofReal delta) totalMass hcap hcover
  have hcount :
      (ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (cells.card : ENNReal) * ENNReal.ofReal delta :=
    hactive.trans hlong
  have hmul := mul_le_mul_left hcount ((ENNReal.ofReal delta) ^ 3)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Version with the literal four-dimensional cubical capacity
`cellMass ≤ 4 * delta`.  The same factor four is required in the active-mass
lower bound and is then cancelled exactly in `ENNReal`; no asymptotic loss is
hidden in the cell count. -/
theorem wz_cell_count_density_of_longitudinal_allocation_four_capacity
    {alpha : Type*} (delta eta : ℝ) (cells : Finset alpha)
    (cellMass : alpha → ENNReal) (totalMass : ENNReal)
    (hactive :
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤ totalMass)
    (hcover : totalMass ≤ ∑ k ∈ cells, cellMass k)
    (hcap : ∀ k ∈ cells,
      cellMass k ≤ ENNReal.ofReal (4 * delta)) :
    (ENNReal.ofReal delta).rpow eta *
        (32 * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
      (cells.card : ENNReal) * (ENNReal.ofReal delta) ^ 4 := by
  have hlong : totalMass ≤
      (cells.card : ENNReal) * ENNReal.ofReal (4 * delta) :=
    longitudinal_mass_le_card_mul_delta
      cells cellMass (ENNReal.ofReal (4 * delta)) totalMass hcap hcover
  have hfour : ENNReal.ofReal (4 * delta) =
      (4 : ENNReal) * ENNReal.ofReal delta := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hcountFour :
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤
        (cells.card : ENNReal) *
          ((4 : ENNReal) * ENNReal.ofReal delta) := by
    simpa only [hfour] using hactive.trans hlong
  have hcount :
      (ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (cells.card : ENNReal) * ENNReal.ofReal delta := by
    apply (ENNReal.mul_le_mul_iff_left
      (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcountFour
  have hmul := mul_le_mul_left hcount ((ENNReal.ofReal delta) ^ 3)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Coefficient-free form of the preceding cancellation.  It is used when
the tube thickness is a fixed multiple of the cubical scale, so the desired
density coefficient is naturally written at the tube scale while the
one-cell longitudinal capacity remains `4 * cellDelta`. -/
theorem wz_cell_count_of_longitudinal_allocation_four_capacity
    {alpha : Type*} (cellDelta : ℝ) (coefficient : ENNReal)
    (cells : Finset alpha) (cellMass : alpha → ENNReal)
    (totalMass : ENNReal)
    (hactive : (4 : ENNReal) * coefficient ≤ totalMass)
    (hcover : totalMass ≤ ∑ k ∈ cells, cellMass k)
    (hcap : ∀ k ∈ cells,
      cellMass k ≤ ENNReal.ofReal (4 * cellDelta)) :
    coefficient * (ENNReal.ofReal cellDelta) ^ 3 ≤
      (cells.card : ENNReal) * (ENNReal.ofReal cellDelta) ^ 4 := by
  have hlong : totalMass ≤
      (cells.card : ENNReal) * ENNReal.ofReal (4 * cellDelta) :=
    longitudinal_mass_le_card_mul_delta
      cells cellMass (ENNReal.ofReal (4 * cellDelta)) totalMass hcap hcover
  have hfour : ENNReal.ofReal (4 * cellDelta) =
      (4 : ENNReal) * ENNReal.ofReal cellDelta := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hcountFour :
      (4 : ENNReal) * coefficient ≤
        (cells.card : ENNReal) *
          ((4 : ENNReal) * ENNReal.ofReal cellDelta) := by
    simpa only [hfour] using hactive.trans hlong
  have hcount : coefficient ≤
      (cells.card : ENNReal) * ENNReal.ofReal cellDelta := by
    apply (ENNReal.mul_le_mul_iff_left
      (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcountFour
  have hmul := mul_le_mul_left hcount ((ENNReal.ofReal cellDelta) ^ 3)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- With physical thickness `2 * delta`, an active fibre of the displayed
mass forces exactly the cell-volume lower bound needed for WZ density at the
physical scale.  The factor eight is `(2 * delta)^3 / delta^3`; it is a fixed
four-dimensional scale-comparison constant, not an asymptotic loss. -/
theorem wz_two_scale_cell_count_density_of_longitudinal_allocation
    {alpha : Type*} (delta eta : ℝ) (cells : Finset alpha)
    (cellMass : alpha → ENNReal) (totalMass : ENNReal)
    (hdelta : 0 < delta)
    (hactive :
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤ totalMass)
    (hcover : totalMass ≤ ∑ k ∈ cells, cellMass k)
    (hcap : ∀ k ∈ cells,
      cellMass k ≤ ENNReal.ofReal (4 * delta)) :
    (ENNReal.ofReal (2 * delta)).rpow eta *
        (32 * (ENNReal.ofReal (2 * delta)) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
      (cells.card : ENNReal) * (ENNReal.ofReal delta) ^ 4 := by
  have hbase := wz_cell_count_of_longitudinal_allocation_four_capacity
    delta
    (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
      (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))))
    cells cellMass totalMass hactive hcover hcap
  have htwo : ENNReal.ofReal (2 * delta) =
      (2 : ENNReal) * ENNReal.ofReal delta := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [htwo]
  rw [htwo] at hbase
  convert hbase using 1 <;> ring

/-- Family form of the longitudinal allocation argument.  It discharges the
cell-count hypothesis for every retained marked line without introducing an
aggregate shading-density axiom. -/
theorem retained_wz_cell_count_of_longitudinal_allocation
    (delta eta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (longitudinalMass : Fin retained.card → ENNReal)
    (cellMass : Fin retained.card → (Fin 4 → ℤ) → ENNReal)
    (hactive : ∀ i,
      (ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤ longitudinalMass i)
    (hcover : ∀ i, longitudinalMass i ≤
      ∑ k ∈ shadingCells (retainedIndex retained i), cellMass i k)
    (hcap : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      cellMass i k ≤ ENNReal.ofReal delta) :
    ∀ i : Fin retained.card,
      (ENNReal.ofReal delta).rpow eta *
          (32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (shadingCells (retainedIndex retained i)).card *
          (ENNReal.ofReal delta) ^ 4 := by
  intro i
  exact wz_cell_count_density_of_longitudinal_allocation
    delta eta (shadingCells (retainedIndex retained i))
    (cellMass i) (longitudinalMass i)
    (hactive i) (hcover i) (hcap i)

/-- Physical family form: the cell masses are no longer arbitrary data but
the fibre probabilities of the actual `rawFrontParam` preimages.  The
unit-speed cubical capacity theorem supplies every per-cell bound. -/
theorem retained_wz_cell_count_of_physical_longitudinal_allocation
    (delta eta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (longitudinalMass : Fin retained.card → ENNReal)
    (hdelta : 0 < delta)
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hactive : ∀ i,
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤ longitudinalMass i)
    (hcover : ∀ i, longitudinalMass i ≤
      ∑ k ∈ shadingCells (retainedIndex retained i),
        markedLineDyadicCellMass (retainedIndex retained i) delta k) :
    ∀ i : Fin retained.card,
      (ENNReal.ofReal delta).rpow eta *
          (32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (shadingCells (retainedIndex retained i)).card *
          (ENNReal.ofReal delta) ^ 4 := by
  intro i
  apply wz_cell_count_density_of_longitudinal_allocation_four_capacity
    delta eta (shadingCells (retainedIndex retained i))
    (markedLineDyadicCellMass (retainedIndex retained i) delta)
    (longitudinalMass i) (hactive i) (hcover i)
  intro k _hk
  exact markedLineDyadicCellMass_le
    (hvalid (retainedIndex retained i) (retainedIndex_mem retained i)) hdelta k

/-- Fully geometric density-count interface.  Its longitudinal mass is the
actual fibre probability of an active time set, and the only coverage input
says that every active time lands in one of the selected cubical preimages. -/
theorem retained_wz_cell_count_of_active_fibre_cover
    (delta eta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hdelta : 0 < delta)
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hactive : ∀ i,
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (hcellCover : ∀ i, activeTime i ⊆
      ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
        markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) :
    ∀ i : Fin retained.card,
      (ENNReal.ofReal delta).rpow eta *
          (32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (shadingCells (retainedIndex retained i)).card *
          (ENNReal.ofReal delta) ^ 4 := by
  apply retained_wz_cell_count_of_physical_longitudinal_allocation
    delta eta retained shadingCells
    (fun i => (fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    hdelta hvalid hactive
  intro i
  exact fibreIntervalProbability_le_sum_markedLineDyadicCellMass
    (retainedIndex retained i) delta
    (shadingCells (retainedIndex retained i)) (activeTime i) (hcellCover i)

/-- Active-fibre cell count at the scale-honest ratio: cells have side
`delta`, while the physical WZ tubes have thickness `2 * delta`. -/
theorem retained_wz_two_scale_cell_count_of_active_fibre_cover
    (delta eta : ℝ) (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hdelta : 0 < delta)
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (hcellCover : ∀ i, activeTime i ⊆
      ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
        markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) :
    ∀ i : Fin retained.card,
      (ENNReal.ofReal (2 * delta)).rpow eta *
          (32 * (ENNReal.ofReal (2 * delta)) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (shadingCells (retainedIndex retained i)).card *
          (ENNReal.ofReal delta) ^ 4 := by
  intro i
  apply wz_two_scale_cell_count_density_of_longitudinal_allocation
    delta eta (shadingCells (retainedIndex retained i))
    (markedLineDyadicCellMass (retainedIndex retained i) delta)
    ((fibreIntervalProbability :
      Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    hdelta (hactive i)
  · exact fibreIntervalProbability_le_sum_markedLineDyadicCellMass
      (retainedIndex retained i) delta
      (shadingCells (retainedIndex retained i)) (activeTime i) (hcellCover i)
  · intro k _hk
    exact markedLineDyadicCellMass_le
      (hvalid (retainedIndex retained i) (retainedIndex_mem retained i)) hdelta k

/-- The active-fibre lower bound itself produces finite cubical families with
the required cell-count density.  In particular, no finite-cover hypothesis is
needed at the longitudinal allocation stage: the cells are the canonical floor
indices of the actual marked fibres and are chosen simultaneously for the
whole retained family. -/
theorem exists_retained_wz_cell_count_of_active_fibres
    (delta eta : ℝ) (retained : Finset MarkedLine)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hdelta : 0 < delta)
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hactive : ∀ i,
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i)) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      ∀ i : Fin retained.card,
        (ENNReal.ofReal delta).rpow eta *
            (32 * (ENNReal.ofReal delta) ^ 3 *
              ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
          (shadingCells (retainedIndex retained i)).card *
            (ENNReal.ofReal delta) ^ 4 := by
  obtain ⟨shadingCells, hcellCover, _hcellMeet⟩ :=
    exists_finite_active_fibre_covers delta hdelta retained activeTime
  refine ⟨shadingCells, ?_⟩
  exact retained_wz_cell_count_of_active_fibre_cover
    delta eta retained shadingCells activeTime hdelta hvalid hactive hcellCover

/-- Exact cubical volume converts a finite lower bound on the number of
selected cells into the pointwise shading-density inequality.  The only
geometric loss is the explicit uniform upper volume constant for a marked
unit tube. -/
theorem wz_pointwise_density_of_cell_count
    {n : ℕ} (delta eta : ℝ) (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ))
    (hdelta : 0 < delta) (hsmall : delta ≤ 1)
    (hseparated : ∀ i j, i ≠ j →
      delta ≤ dist (direction (line i)) (direction (line j)))
    (hvalid : ∀ i, IsValidLine (line i))
    (hcellCount : ∀ i,
      (ENNReal.ofReal delta).rpow eta *
          (32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (cells i).card * (ENNReal.ofReal delta) ^ 4) :
    ∀ i,
      (ENNReal.ofReal
        (directionSeparatedWZCellSource
          delta line cells hdelta hseparated).thickness).rpow eta *
          volume (markedUnitTube
            ((directionSeparatedWZCellSource
              delta line cells hdelta hseparated).line i)
            (directionSeparatedWZCellSource
              delta line cells hdelta hseparated).thickness) ≤
        volume ((directionSeparatedWZCellSource
          delta line cells hdelta hseparated).shading i) := by
  intro i
  have htube := volume_markedUnitTube_upper_bound
    (hvalid i) hdelta hsmall
  calc
    (ENNReal.ofReal
        (directionSeparatedWZCellSource
          delta line cells hdelta hseparated).thickness).rpow eta *
          volume (markedUnitTube
            ((directionSeparatedWZCellSource
              delta line cells hdelta hseparated).line i)
            (directionSeparatedWZCellSource
              delta line cells hdelta hseparated).thickness) =
      (ENNReal.ofReal delta).rpow eta *
        volume (markedUnitTube (line i) delta) := by rfl
    _ ≤ (ENNReal.ofReal delta).rpow eta *
        (32 * (ENNReal.ofReal delta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
      simpa [mul_comm] using
        (mul_le_mul_left htube ((ENNReal.ofReal delta).rpow eta))
    _ ≤ (cells i).card * (ENNReal.ofReal delta) ^ 4 := hcellCount i
    _ = volume (wzCellShading delta cells i) :=
      (volume_wzCellShading hdelta cells i).symm
    _ = volume ((directionSeparatedWZCellSource
        delta line cells hdelta hseparated).shading i) := by rfl

/-- Pointwise density for separate physical and cubical scales.  Tube volume
is estimated at `tubeDelta`, while exact shading volume is counted using
side-`cellDelta` cells. -/
theorem wz_pointwise_density_atScales_of_cell_count
    {n : ℕ} (tubeDelta cellDelta eta : ℝ)
    (line : Fin n → MarkedLine)
    (cells : Fin n → Finset (Fin 4 → ℤ))
    (htubeDelta : 0 < tubeDelta) (hcellDelta : 0 < cellDelta)
    (htubeSmall : tubeDelta ≤ 1)
    (hseparated : ∀ i j, i ≠ j →
      tubeDelta ≤ dist (direction (line i)) (direction (line j)))
    (hvalid : ∀ i, IsValidLine (line i))
    (hcellCount : ∀ i,
      (ENNReal.ofReal tubeDelta).rpow eta *
          (32 * (ENNReal.ofReal tubeDelta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (cells i).card * (ENNReal.ofReal cellDelta) ^ 4) :
    ∀ i,
      (ENNReal.ofReal
        (directionSeparatedWZCellSourceAtScales tubeDelta cellDelta line cells
          htubeDelta hseparated).thickness).rpow eta *
          volume (markedUnitTube
            ((directionSeparatedWZCellSourceAtScales
              tubeDelta cellDelta line cells htubeDelta hseparated).line i)
            (directionSeparatedWZCellSourceAtScales
              tubeDelta cellDelta line cells htubeDelta hseparated).thickness) ≤
        volume ((directionSeparatedWZCellSourceAtScales
          tubeDelta cellDelta line cells htubeDelta hseparated).shading i) := by
  intro i
  have htube := volume_markedUnitTube_upper_bound
    (hvalid i) htubeDelta htubeSmall
  calc
    (ENNReal.ofReal
        (directionSeparatedWZCellSourceAtScales
          tubeDelta cellDelta line cells htubeDelta hseparated).thickness).rpow eta *
          volume (markedUnitTube
            ((directionSeparatedWZCellSourceAtScales
              tubeDelta cellDelta line cells htubeDelta hseparated).line i)
            (directionSeparatedWZCellSourceAtScales
              tubeDelta cellDelta line cells htubeDelta hseparated).thickness) =
      (ENNReal.ofReal tubeDelta).rpow eta *
        volume (markedUnitTube (line i) tubeDelta) := by rfl
    _ ≤ (ENNReal.ofReal tubeDelta).rpow eta *
        (32 * (ENNReal.ofReal tubeDelta) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
      simpa [mul_comm] using
        (mul_le_mul_left htube ((ENNReal.ofReal tubeDelta).rpow eta))
    _ ≤ (cells i).card * (ENNReal.ofReal cellDelta) ^ 4 := hcellCount i
    _ = volume (wzCellShading cellDelta cells i) :=
      (volume_wzCellShading hcellDelta cells i).symm
    _ = volume ((directionSeparatedWZCellSourceAtScales
        tubeDelta cellDelta line cells htubeDelta hseparated).shading i) := by rfl

/-- A raw geometric contained-tube coefficient gives the normalized
convex-Wolff clause once the coefficient is absorbed by the family size. -/
theorem wz_convex_wolff_of_geometric_count
    {n : ℕ} (D : FiniteScaleSource n) (eta : ℝ) (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount D U : ENNReal) ≤ K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal D.thickness).rpow (-eta) * n) :
    ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount D U : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) * volume U * n := by
  intro U hU
  calc
    (wzContainedTubeCount D U : ENNReal) ≤ K * volume U := hgeometric U hU
    _ ≤ ((ENNReal.ofReal D.thickness).rpow (-eta) * n) * volume U := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_right hnormalize (volume U))
    _ = (ENNReal.ofReal D.thickness).rpow (-eta) * volume U * n := by
      ac_rfl

/-- Assembly of the literal finite WZ input from the retained marked family.
The compensation/pruning ledger supplies the full-radius almost-AD clause;
the constructor supplies dyadic cubical shadings, unit weights, line
injectivity, and exact affine marks.  The two genuinely physical hypotheses
which remain visible are the convex-Wolff count and the shading-density
inequality. -/
theorem retained_wz_source_is_finite_input_of_dyadic_terminal_pruning
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal delta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (hshadingTube : ∀ i : Fin retained.card,
      (retainedWZCellSource delta retained shadingCells hdelta hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSource delta retained shadingCells hdelta hseparated).line i)
          (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness)
    (hconvexWolff : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSource delta retained shadingCells hdelta hseparated)
          U : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta) * volume U * retained.card)
    (hdensity :
      (ENNReal.ofReal delta).rpow eta *
          wzTotalTubeVolume
            (retainedWZCellSource delta retained shadingCells hdelta hseparated) ≤
        wzTotalShadingVolume
          (retainedWZCellSource delta retained shadingCells hdelta hseparated)) :
    IsWangZakharovFiniteInput
      (retainedWZCellSource delta retained shadingCells hdelta hseparated) eta := by
  have hAD := retained_wz_source_dyadic_terminal_pruning_gives_full_wz_almostAD
    retained shadingCells lowerCell threshold eta delta hdelta hdyadic
    hterminal hlowerDiameter hlowerThreshold hvalid hseparated habsorb
  refine ⟨Finset.card_pos.mpr hretained, hdelta, hdeltaOne, ⟨levelZero, hdyadic⟩,
    ?_, ?_, ?_, ?_, hshadingTube, ?_, ?_, hconvexWolff, hdensity⟩
  · intro i
    exact hvalid (retainedIndex retained i) (retainedIndex_mem retained i)
  · intro _i
    rfl
  · intro i
    change MeasurableSet (wzCellShading delta
      (fun j => shadingCells (retainedIndex retained j)) i)
    exact measurableSet_wzCellShading delta
      (fun j => shadingCells (retainedIndex retained j)) i
  · intro i
    refine ⟨delta, hdelta, le_rfl, ?_, ⟨levelZero, hdyadic⟩, ?_⟩
    · change delta ≤ 2 * delta
      linarith
    exact directionSeparatedWZCellSource_cubical delta (retainedIndex retained)
      (fun j => shadingCells (retainedIndex retained j)) hdelta
      (by
        intro a b hab
        exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
          (retainedIndex retained b) (retainedIndex_mem retained b)
          (fun h => hab (retainedIndex_injective retained h))) i
  · intro a b hab
    exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
      (retainedIndex retained b) (retainedIndex_mem retained b)
      (fun h => hab (retainedIndex_injective retained h))
  · exact hAD

/-- Scale-honest assembly of the finite WZ input.  Cubes have side `delta`,
physical tubes have thickness `2 * delta`, and every selected cube carries an
actual occurrence witness.  Consequently the tube-containment clause is a
theorem, not an exposed hypothesis. -/
theorem retained_wz_two_scale_source_is_finite_input_of_dyadic_terminal_pruning
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (htubeOne : 2 * delta ≤ 1)
    (htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hcellDyadic : IsWZDyadicScale delta)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal (2 * delta)).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / (2 * delta))) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta))
    (hmeet : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈
          wzDyadicCell delta k)
    (hconvexWolff : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated) U : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) * volume U * retained.card)
    (hdensity :
      (ENNReal.ofReal (2 * delta)).rpow eta *
          wzTotalTubeVolume
            (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
              (by positivity) hseparated) ≤
        wzTotalShadingVolume
          (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
            (by positivity) hseparated)) :
    IsWangZakharovFiniteInput
      (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
        (by positivity) hseparated) eta := by
  have hAD :=
    retained_wz_sourceAtScales_dyadic_terminal_pruning_gives_full_wz_almostAD
      retained shadingCells lowerCell threshold eta (2 * delta) delta
      (by positivity) htubeDyadic hterminal hlowerDiameter hlowerThreshold
      hvalid hseparated habsorb
  refine ⟨Finset.card_pos.mpr hretained, ?_, htubeOne,
    ⟨levelZero, htubeDyadic⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hconvexWolff,
      hdensity⟩
  · change 0 < 2 * delta
    positivity
  · intro i
    exact hvalid (retainedIndex retained i) (retainedIndex_mem retained i)
  · intro _i
    rfl
  · intro i
    change MeasurableSet (wzCellShading delta
      (fun j => shadingCells (retainedIndex retained j)) i)
    exact measurableSet_wzCellShading delta
      (fun j => shadingCells (retainedIndex retained j)) i
  · intro i
    let hsepIndex : ∀ a b : Fin retained.card, a ≠ b →
        2 * delta ≤ dist (direction (retainedIndex retained a))
          (direction (retainedIndex retained b)) := by
      intro a b hab
      exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
        (retainedIndex retained b) (retainedIndex_mem retained b)
        (fun h => hab (retainedIndex_injective retained h))
    exact directionSeparatedWZCellSourceAtScales_comparable_cubical
      (2 * delta) delta (retainedIndex retained)
      (fun j => shadingCells (retainedIndex retained j)) (by positivity)
      hdelta (by linarith) le_rfl hcellDyadic hsepIndex i
  · intro i
    change wzCellShading delta
      (fun j => shadingCells (retainedIndex retained j)) i ⊆
        markedUnitTube (retainedIndex retained i) (2 * delta)
    apply wzDyadicCells_meeting_markedLine_subset_two_mul_tube
      (retainedIndex retained i) hdelta
    exact hmeet i
  · intro a b hab
    exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
      (retainedIndex retained b) (retainedIndex_mem retained b)
      (fun h => hab (retainedIndex_injective retained h))
  · exact hAD

/-- Local geometric form of the retained-source assembly.  The caller supplies
only a raw contained-tube coefficient and a finite lower bound for the number
of cubical shading cells on each retained marked line.  Exact cell volume, the
uniform tube-volume bound, and the two finite-family aggregation lemmas then
produce the convex-Wolff and shading-density clauses of the WZ input. -/
theorem retained_wz_source_is_finite_input_of_local_geometry
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal delta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (hshadingTube : ∀ i : Fin retained.card,
      (retainedWZCellSource delta retained shadingCells hdelta hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSource delta retained shadingCells hdelta hseparated).line i)
          (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness)
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSource delta retained shadingCells hdelta hseparated)
          U : ENNReal) ≤ K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal
        (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness).rpow
          (-eta) * retained.card)
    (hcellCount : ∀ i : Fin retained.card,
      (ENNReal.ofReal delta).rpow eta *
          (32 * (ENNReal.ofReal delta) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
        (shadingCells (retainedIndex retained i)).card *
          (ENNReal.ofReal delta) ^ 4) :
    IsWangZakharovFiniteInput
      (retainedWZCellSource delta retained shadingCells hdelta hseparated) eta := by
  apply retained_wz_source_is_finite_input_of_dyadic_terminal_pruning
    retained shadingCells lowerCell threshold eta delta hretained hdelta hdeltaOne
    hdyadic hterminal hlowerDiameter hlowerThreshold hvalid hseparated habsorb
    hshadingTube
  · exact wz_convex_wolff_of_geometric_count
      (retainedWZCellSource delta retained shadingCells hdelta hseparated)
      eta K hgeometric hnormalize
  · exact wz_shading_density_of_pointwise
      (retainedWZCellSource delta retained shadingCells hdelta hseparated)
      eta (wz_pointwise_density_of_cell_count delta eta
        (retainedIndex retained)
        (fun i => shadingCells (retainedIndex retained i))
        hdelta hdeltaOne
        (by
          intro i j hij
          exact hseparated (retainedIndex retained i) (retainedIndex_mem retained i)
            (retainedIndex retained j) (retainedIndex_mem retained j)
            (fun h => hij (retainedIndex_injective retained h)))
        (fun i => hvalid (retainedIndex retained i) (retainedIndex_mem retained i))
        hcellCount)

/-- Longitudinal-allocation form of the retained-source assembly.  The raw
time allocation now supplies the cell-count input internally; hence the only
remaining physical count exposed by this theorem is convex-Wolff. -/
theorem retained_wz_source_is_finite_input_of_longitudinal_allocation
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal delta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (hshadingTube : ∀ i : Fin retained.card,
      (retainedWZCellSource delta retained shadingCells hdelta hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSource delta retained shadingCells hdelta hseparated).line i)
          (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness)
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSource delta retained shadingCells hdelta hseparated)
          U : ENNReal) ≤ K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal
        (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness).rpow
          (-eta) * retained.card)
    (longitudinalMass : Fin retained.card → ENNReal)
    (cellMass : Fin retained.card → (Fin 4 → ℤ) → ENNReal)
    (hactive : ∀ i,
      (ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤ longitudinalMass i)
    (hcover : ∀ i, longitudinalMass i ≤
      ∑ k ∈ shadingCells (retainedIndex retained i), cellMass i k)
    (hcap : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      cellMass i k ≤ ENNReal.ofReal delta) :
    IsWangZakharovFiniteInput
      (retainedWZCellSource delta retained shadingCells hdelta hseparated) eta := by
  apply retained_wz_source_is_finite_input_of_local_geometry
    retained shadingCells lowerCell threshold eta delta hretained hdelta hdeltaOne
    hdyadic hterminal hlowerDiameter hlowerThreshold hvalid hseparated habsorb
    hshadingTube K hgeometric hnormalize
  exact retained_wz_cell_count_of_longitudinal_allocation
    delta eta retained shadingCells longitudinalMass cellMass hactive hcover hcap

/-- Retained WZ assembly with a literal active fibre-time cover.  The theorem
internally performs the complete chain
`active times → cubical preimage masses → cell count → shading density`.
Thus no pointwise density, abstract cell capacity, or aggregate shading
hypothesis remains at this interface. -/
theorem retained_wz_source_is_finite_input_of_active_fibre_cover
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal delta).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / delta)) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal delta).rpow (-eta))
    (hshadingTube : ∀ i : Fin retained.card,
      (retainedWZCellSource delta retained shadingCells hdelta hseparated).shading i ⊆
        markedUnitTube
          ((retainedWZCellSource delta retained shadingCells hdelta hseparated).line i)
          (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness)
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSource delta retained shadingCells hdelta hseparated)
          U : ENNReal) ≤ K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal
        (retainedWZCellSource delta retained shadingCells hdelta hseparated).thickness).rpow
          (-eta) * retained.card)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hactive : ∀ i,
      (4 : ENNReal) * ((ENNReal.ofReal delta).rpow eta *
          (32 * ENNReal.ofReal (Real.pi ^ 2 / 2))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (hcellCover : ∀ i, activeTime i ⊆
      ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
        markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) :
    IsWangZakharovFiniteInput
      (retainedWZCellSource delta retained shadingCells hdelta hseparated) eta := by
  apply retained_wz_source_is_finite_input_of_local_geometry
    retained shadingCells lowerCell threshold eta delta hretained hdelta hdeltaOne
    hdyadic hterminal hlowerDiameter hlowerThreshold hvalid hseparated habsorb
    hshadingTube K hgeometric hnormalize
  exact retained_wz_cell_count_of_active_fibre_cover
    delta eta retained shadingCells activeTime hdelta hvalid hactive hcellCover

/-- Scale-honest active-fibre assembly.  Unlike the preceding legacy
single-scale statement, this theorem has no `hshadingTube` argument: actual
cell-occurrence witnesses prove that clause internally. -/
theorem retained_wz_two_scale_source_is_finite_input_of_active_fibre_cover
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (shadingCells : MarkedLine → Finset (Fin 4 → ℤ))
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (htubeOne : 2 * delta ≤ 1)
    (htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hcellDyadic : IsWZDyadicScale delta)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal (2 * delta)).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / (2 * delta))) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta))
    (hmeet : ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
      ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈
          wzDyadicCell delta k)
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated) U : ENNReal) ≤ K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) * retained.card)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (hcellCover : ∀ i, activeTime i ⊆
      ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
        markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) :
    IsWangZakharovFiniteInput
      (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
        (by positivity) hseparated) eta := by
  have hcellCount := retained_wz_two_scale_cell_count_of_active_fibre_cover
    delta eta retained shadingCells activeTime hdelta hvalid hactive hcellCover
  apply retained_wz_two_scale_source_is_finite_input_of_dyadic_terminal_pruning
    retained shadingCells lowerCell threshold eta delta hretained hdelta
    htubeOne htubeDyadic hcellDyadic hterminal hlowerDiameter hlowerThreshold
    hvalid hseparated habsorb hmeet
  · exact wz_convex_wolff_of_geometric_count
      (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
        (by positivity) hseparated) eta K hgeometric hnormalize
  · exact wz_shading_density_of_pointwise
      (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
        (by positivity) hseparated) eta
      (wz_pointwise_density_atScales_of_cell_count
        (2 * delta) delta eta (retainedIndex retained)
        (fun i => shadingCells (retainedIndex retained i))
        (by positivity) hdelta htubeOne
        (by
          intro a b hab
          exact hseparated (retainedIndex retained a) (retainedIndex_mem retained a)
            (retainedIndex retained b) (retainedIndex_mem retained b)
            (fun h => hab (retainedIndex_injective retained h)))
        (fun i => hvalid (retainedIndex retained i) (retainedIndex_mem retained i))
        hcellCount)

/-- Fully automatic scale-honest active-fibre assembly.  The caller supplies
only the retained carrier geometry and active time sets.  Canonical finite
cell families, their fibre cover, their occurrence witnesses, cubical
measurability, and physical tube containment are all constructed internally.
The active occurrence witnesses are also returned, so later cover readback
does not have to reconstruct their provenance.
The convex-Wolff premise is stated on the empty-shading source because its
contained-tube count depends only on lines and physical thickness. -/
theorem exists_retained_wz_two_scale_finite_input_of_active_fibres
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (htubeOne : 2 * delta ≤ 1)
    (htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hcellDyadic : IsWZDyadicScale delta)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal (2 * delta)).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / (2 * delta))) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta))
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * delta) delta retained
          (fun _ => ∅) (by positivity) hseparated) U : ENNReal) ≤
        K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) * retained.card)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i)) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      IsWangZakharovFiniteInput
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated) eta ∧
      (∀ i, activeTime i ⊆
        ⋃ k ∈ (shadingCells (retainedIndex retained i) : Set (Fin 4 → ℤ)),
          markedLineDyadicCellFibreSet (retainedIndex retained i) delta k) ∧
      ∀ i k, k ∈ shadingCells (retainedIndex retained i) →
        ∃ t : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
          t ∈ activeTime i ∧
          rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈
            wzDyadicCell delta k := by
  obtain ⟨shadingCells, hcellCover, hmeetActive⟩ :=
    exists_finite_retained_active_fibre_covers delta hdelta retained activeTime
  have hgeometric' : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated) U : ENNReal) ≤ K * volume U := by
    intro U hU
    have heq :
        wzContainedTubeCount
          (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
            (by positivity) hseparated) U =
        wzContainedTubeCount
          (retainedWZCellSourceAtScales (2 * delta) delta retained
            (fun _ => ∅) (by positivity) hseparated) U := by
      unfold wzContainedTubeCount
      congr
    rw [heq]
    exact hgeometric U hU
  refine ⟨shadingCells, ?_, hcellCover, hmeetActive⟩
  apply retained_wz_two_scale_source_is_finite_input_of_active_fibre_cover
    retained shadingCells lowerCell threshold eta delta hretained hdelta
    htubeOne htubeDyadic hcellDyadic hterminal hlowerDiameter hlowerThreshold
    hvalid hseparated habsorb
    (by
      intro i k hk
      obtain ⟨t, _htActive, htCell⟩ := hmeetActive i k hk
      exact ⟨t, htCell⟩)
    K hgeometric' hnormalize activeTime hactive hcellCover

/-- Automatic active-fibre assembly together with its physical readback.
The same occurrence witnesses used to build the cubical shading prove that
the entire shaded union lies in the `2 * delta` inflation of the supplied
physical target.  No later argument has to reconstruct cell provenance. -/
theorem exists_retained_wz_two_scale_finite_input_with_target_inflation
    {beta : Type*} {levelZero : ℕ}
    (retained : Finset MarkedLine)
    (lowerCell : Fin (levelZero + 1) → MarkedLine → beta)
    (threshold : Fin (levelZero + 1) → ℕ) (eta delta : ℝ)
    (hretained : retained.Nonempty)
    (hdelta : 0 < delta) (htubeOne : 2 * delta ≤ 1)
    (htubeDyadic : 2 * delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hcellDyadic : IsWZDyadicScale delta)
    (hterminal : ∀ ell b,
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b, b ∈ retained →
      lowerCell ell b = lowerCell ell a →
        dist (direction b, offset b) (direction a, offset a) ≤
          wzDyadicRadius levelZero ell)
    (hlowerThreshold : ∀ ell,
      (ENNReal.ofReal (2 * delta)).rpow eta *
          (ENNReal.ofReal
            ((2 * wzDyadicRadius levelZero ell) / (2 * delta))) ^ 3 ≤
        (threshold ell : ENNReal))
    (hvalid : ∀ line ∈ retained, IsValidLine line)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained, a ≠ b →
      2 * delta ≤ dist (direction a) (direction b))
    (habsorb : (125 : ENNReal) ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta))
    (K : ENNReal)
    (hgeometric : ∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount
        (retainedWZCellSourceAtScales (2 * delta) delta retained
          (fun _ => ∅) (by positivity) hseparated) U : ENNReal) ≤
        K * volume U)
    (hnormalize : K ≤
      (ENNReal.ofReal (2 * delta)).rpow (-eta) * retained.card)
    (activeTime : Fin retained.card →
      Set (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (hactive : ∀ i,
      (4 : ENNReal) *
          (8 * ((ENNReal.ofReal (2 * delta)).rpow eta *
            (32 * ENNReal.ofReal (Real.pi ^ 2 / 2)))) ≤
        (fibreIntervalProbability :
          Measure (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) (activeTime i))
    (target : Set E4)
    (hactiveTarget : ∀ i t, t ∈ activeTime i →
      rawFrontParam (retainedIndex retained i, (t : ℝ)) ∈ target) :
    ∃ shadingCells : MarkedLine → Finset (Fin 4 → ℤ),
      IsWangZakharovFiniteInput
        (retainedWZCellSourceAtScales (2 * delta) delta retained shadingCells
          (by positivity) hseparated) eta ∧
      (⋃ i, (retainedWZCellSourceAtScales (2 * delta) delta retained
        shadingCells (by positivity) hseparated).shading i) ⊆
          ⋃ y ∈ target, Metric.ball y (2 * delta) := by
  obtain ⟨shadingCells, hinput, _hcellCover, hmeet⟩ :=
    exists_retained_wz_two_scale_finite_input_of_active_fibres
      retained lowerCell threshold eta delta hretained hdelta htubeOne
      htubeDyadic hcellDyadic hterminal hlowerDiameter hlowerThreshold
      hvalid hseparated habsorb K hgeometric hnormalize activeTime hactive
  refine ⟨shadingCells, hinput, ?_⟩
  exact retainedWZCellSourceAtScales_shadingUnion_subset_active_target_inflation
    delta hdelta retained shadingCells hseparated activeTime target
      hactiveTarget hmeet

/-- Local-cell version of projected packing.  The counted ball lives in the
full marked carrier metric, separation lives in the direction metric, and
only direction cells meeting this particular carrier ball are charged. -/
theorem metricClosedBall_card_le_of_projected_separated_local_cells
    {alpha beta X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (points : Finset alpha) (ballImage : alpha → X)
    (separationImage : alpha → Y)
    (center : alpha) (radius delta : ℝ) (cell : alpha → beta)
    (localCells : Finset beta)
    (hseparated : ∀ a ∈ points, ∀ b ∈ points,
      a ≠ b → delta ≤ dist (separationImage a) (separationImage b))
    (hlocal : ∀ a ∈
      pointsInMetricClosedBall points ballImage center radius,
        cell a ∈ localCells)
    (hcellDiameter :
      ∀ a ∈ pointsInMetricClosedBall points ballImage center radius,
      ∀ b ∈ pointsInMetricClosedBall points ballImage center radius,
        cell a = cell b →
          dist (separationImage a) (separationImage b) < delta) :
    (pointsInMetricClosedBall points ballImage center radius).card ≤
      localCells.card := by
  classical
  let ball := pointsInMetricClosedBall points ballImage center radius
  have hballSubset : ball ⊆ points := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hfiber : ∀ c ∈ localCells,
      (pointsInCell ball cell c).card ≤ 1 := by
    intro c _hc
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : a ∈ ball ∧ cell a = c := by
      simpa [pointsInCell] using ha
    have hb' : b ∈ ball ∧ cell b = c := by
      simpa [pointsInCell] using hb
    by_contra hne
    have hfar := hseparated a (hballSubset ha'.1)
      b (hballSubset hb'.1) hne
    have hnear := hcellDiameter a ha'.1 b hb'.1
      (ha'.2.trans hb'.2.symm)
    exact (not_lt_of_ge hfar) hnear
  have hpartition := finite_partition_card_bound_on_cells
    ball localCells cell 1 (by
      intro a ha
      exact hlocal a ha) hfiber
  simpa [ball] using hpartition

/-- The terminal pruning statement and the separated-cell packing statement
combine into the two-sided metric count used in the finite WZ input.  The
lower cells may be the cover-adapted carrier cells, while the upper cells may
be a separate scale-dependent packing of direction space. -/
theorem terminal_carrier_pruning_metric_two_sided_count
    {alpha beta level X : Type*} [PseudoMetricSpace X]
    {upperCellType : level → Type*}
    [∀ ell, Fintype (upperCellType ell)]
    (retained : Finset alpha) (lowerCell : level → alpha → beta)
    (threshold : level → ℕ) (image : alpha → X)
    (radius : level → ℝ) (delta : ℝ)
    (upperCell : ∀ ell, alpha → upperCellType ell)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      lowerCell ell b = lowerCell ell a →
        dist (image b) (image a) ≤ radius ell)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained,
      a ≠ b → delta ≤ dist (image a) (image b))
    (hupperDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      upperCell ell a = upperCell ell b →
        dist (image a) (image b) < delta) :
    ∀ ell a, a ∈ retained →
      threshold ell ≤
          (pointsInMetricClosedBall retained image a (radius ell)).card ∧
        (pointsInMetricClosedBall retained image a (radius ell)).card ≤
          Fintype.card (upperCellType ell) := by
  intro ell a ha
  constructor
  · exact terminal_carrier_pruning_metric_lower_count
      retained lowerCell threshold image radius hterminal hlowerDiameter
      ell a ha
  · apply metricClosedBall_card_le_of_separated_cells
      retained image a (radius ell) delta (upperCell ell) hseparated
    intro b hb c hc hcell
    have hbRetained : b ∈ retained := (Finset.mem_filter.mp hb).1
    have hcRetained : c ∈ retained := (Finset.mem_filter.mp hc).1
    exact hupperDiameter ell b hbRetained c hcRetained hcell

/-- Two-sided count with a separate projected metric for the upper packing
bound.  This is the form matching the cover-adapted argument: lower carrier
cells sit in balls of the full line-parameter metric, whereas the upper
packing uses only direction separation. -/
theorem terminal_carrier_pruning_projected_two_sided_count
    {alpha beta level X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {upperCellType : level → Type*}
    [∀ ell, Fintype (upperCellType ell)]
    (retained : Finset alpha) (lowerCell : level → alpha → beta)
    (threshold : level → ℕ) (ballImage : alpha → X)
    (separationImage : alpha → Y)
    (radius : level → ℝ) (delta : ℝ)
    (upperCell : ∀ ell, alpha → upperCellType ell)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      lowerCell ell b = lowerCell ell a →
        dist (ballImage b) (ballImage a) ≤ radius ell)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained,
      a ≠ b →
        delta ≤ dist (separationImage a) (separationImage b))
    (hupperDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      upperCell ell a = upperCell ell b →
        dist (separationImage a) (separationImage b) < delta) :
    ∀ ell a, a ∈ retained →
      threshold ell ≤
          (pointsInMetricClosedBall retained ballImage a (radius ell)).card ∧
        (pointsInMetricClosedBall retained ballImage a (radius ell)).card ≤
          Fintype.card (upperCellType ell) := by
  intro ell a ha
  constructor
  · exact terminal_carrier_pruning_metric_lower_count
      retained lowerCell threshold ballImage radius hterminal hlowerDiameter
      ell a ha
  · apply metricClosedBall_card_le_of_projected_separated_cells
      retained ballImage separationImage a (radius ell) delta
      (upperCell ell) hseparated
    intro b hb c hc hcell
    have hbRetained : b ∈ retained := (Finset.mem_filter.mp hb).1
    have hcRetained : c ∈ retained := (Finset.mem_filter.mp hc).1
    exact hupperDiameter ell b hbRetained c hcRetained hcell

/-- Local-cell strengthening of the projected two-sided count.  The upper
partition is charged only for the cells meeting the carrier ball centered at
`a`; consequently a later spherical-cap grid lemma can contribute
`O((radius ell / delta)^3)` rather than the cardinality of a global grid. -/
theorem terminal_carrier_pruning_projected_local_two_sided_count
    {alpha beta level X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {upperCellType : level → Type*}
    (retained : Finset alpha) (lowerCell : level → alpha → beta)
    (threshold : level → ℕ) (ballImage : alpha → X)
    (separationImage : alpha → Y)
    (radius : level → ℝ) (delta : ℝ)
    (upperCell : ∀ ell, alpha → upperCellType ell)
    (localCells : ∀ ell, alpha → Finset (upperCellType ell))
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell retained (lowerCell ell) b).Nonempty →
        threshold ell ≤ (pointsInCell retained (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      lowerCell ell b = lowerCell ell a →
        dist (ballImage b) (ballImage a) ≤ radius ell)
    (hseparated : ∀ a ∈ retained, ∀ b ∈ retained,
      a ≠ b →
        delta ≤ dist (separationImage a) (separationImage b))
    (hlocal : ∀ ell a, a ∈ retained →
      ∀ b ∈ pointsInMetricClosedBall retained ballImage a (radius ell),
        upperCell ell b ∈ localCells ell a)
    (hupperDiameter : ∀ ell a, a ∈ retained → ∀ b ∈ retained,
      upperCell ell a = upperCell ell b →
        dist (separationImage a) (separationImage b) < delta) :
    ∀ ell a, a ∈ retained →
      threshold ell ≤
          (pointsInMetricClosedBall retained ballImage a (radius ell)).card ∧
        (pointsInMetricClosedBall retained ballImage a (radius ell)).card ≤
          (localCells ell a).card := by
  intro ell a ha
  constructor
  · exact terminal_carrier_pruning_metric_lower_count
      retained lowerCell threshold ballImage radius hterminal hlowerDiameter
      ell a ha
  · apply metricClosedBall_card_le_of_projected_separated_local_cells
      retained ballImage separationImage a (radius ell) delta
      (upperCell ell) (localCells ell a) hseparated
    · exact hlocal ell a ha
    · intro b hb c hc hcell
      have hbRetained : b ∈ retained := (Finset.mem_filter.mp hb).1
      have hcRetained : c ∈ retained := (Finset.mem_filter.mp hc).1
      exact hupperDiameter ell b hbRetained c hcRetained hcell

/-- Exact finite-source specialization of the preceding pruning/packing
lemma.  This is the readback used by `IsWangZakharovFiniteInput`: after the
retained marked family has been reindexed as a `FiniteScaleSource`, both
sides are stated directly in terms of `wzCarrierBallCount`. -/
theorem finite_source_carrier_two_sided_count
    {n : ℕ} {beta level : Type*}
    {upperCellType : level → Type*}
    [∀ ell, Fintype (upperCellType ell)]
    (D : FiniteScaleSource n) (lowerCell : level → Fin n → beta)
    (threshold : level → ℕ) (radius : level → ℝ) (delta : ℝ)
    (upperCell : ∀ ell, Fin n → upperCellType ell)
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell (Finset.univ : Finset (Fin n))
        (lowerCell ell) b).Nonempty →
          threshold ell ≤
            (pointsInCell (Finset.univ : Finset (Fin n))
              (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, ∀ b,
      lowerCell ell b = lowerCell ell a →
        dist (wzCarrierPoint D b) (wzCarrierPoint D a) ≤ radius ell)
    (hseparated : ∀ a b, a ≠ b →
      delta ≤ dist (direction (D.line a)) (direction (D.line b)))
    (hupperDiameter : ∀ ell a, ∀ b,
      upperCell ell a = upperCell ell b →
        dist (direction (D.line a)) (direction (D.line b)) < delta) :
    ∀ ell i,
      threshold ell ≤ wzCarrierBallCount D i (radius ell) ∧
        wzCarrierBallCount D i (radius ell) ≤
          Fintype.card (upperCellType ell) := by
  intro ell i
  have h := terminal_carrier_pruning_projected_two_sided_count
    (Finset.univ : Finset (Fin n)) lowerCell threshold
    (wzCarrierPoint D) (fun j => direction (D.line j))
    radius delta upperCell hterminal
    (by
      intro ell' a _ha b _hb hab
      exact hlowerDiameter ell' a b hab)
    (by
      intro a _ha b _hb hab
      exact hseparated a b hab)
    (by
      intro ell' a _ha b _hb hab
      exact hupperDiameter ell' a b hab)
    ell i (by simp)
  simpa using h

/-- Finite-source readback of the local-cell projected count.  This is the
exact interface at which an explicit three-dimensional spherical-cap grid is
to be inserted: all carrier marks are retained in the ball predicate, while
the local cell cardinality is purely directional. -/
theorem finite_source_carrier_local_two_sided_count
    {n : ℕ} {beta level : Type*}
    {upperCellType : level → Type*}
    (D : FiniteScaleSource n) (lowerCell : level → Fin n → beta)
    (threshold : level → ℕ) (radius : level → ℝ) (delta : ℝ)
    (upperCell : ∀ ell, Fin n → upperCellType ell)
    (localCells : ∀ ell, Fin n → Finset (upperCellType ell))
    (hterminal : ∀ (ell : level) (b : beta),
      (pointsInCell (Finset.univ : Finset (Fin n))
        (lowerCell ell) b).Nonempty →
          threshold ell ≤
            (pointsInCell (Finset.univ : Finset (Fin n))
              (lowerCell ell) b).card)
    (hlowerDiameter : ∀ ell a, ∀ b,
      lowerCell ell b = lowerCell ell a →
        dist (wzCarrierPoint D b) (wzCarrierPoint D a) ≤ radius ell)
    (hseparated : ∀ a b, a ≠ b →
      delta ≤ dist (direction (D.line a)) (direction (D.line b)))
    (hlocal : ∀ ell i j,
      dist (wzCarrierPoint D j) (wzCarrierPoint D i) ≤ radius ell →
        upperCell ell j ∈ localCells ell i)
    (hupperDiameter : ∀ ell a, ∀ b,
      upperCell ell a = upperCell ell b →
        dist (direction (D.line a)) (direction (D.line b)) < delta) :
    ∀ ell i,
      threshold ell ≤ wzCarrierBallCount D i (radius ell) ∧
        wzCarrierBallCount D i (radius ell) ≤
          (localCells ell i).card := by
  intro ell i
  have h := terminal_carrier_pruning_projected_local_two_sided_count
    (Finset.univ : Finset (Fin n)) lowerCell threshold
    (wzCarrierPoint D) (fun j => direction (D.line j))
    radius delta upperCell localCells hterminal
    (by
      intro ell' a _ha b _hb hab
      exact hlowerDiameter ell' a b hab)
    (by
      intro a _ha b _hb hab
      exact hseparated a b hab)
    (by
      intro ell' a _ha b hb
      exact hlocal ell' a b (Finset.mem_filter.mp hb).2)
    (by
      intro ell' a _ha b _hb hab
      exact hupperDiameter ell' a b hab)
    ell i (by simp)
  simpa using h

/-- Assign every point of a finite subfamily to one of the actual centers of
a metric cover.  The subtype of centers is the finite cell-label type, so its
cardinality is exactly the cover cardinality. -/
theorem exists_cover_cell_assignment
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (r : ℝ)
    (points centers : Finset X)
    (hpoints : (points : Set X) ⊆ s)
    (hcover : coversAtRadius s r centers) :
    ∃ cell : points → centers,
      ∀ p : points, dist (p : X) (cell p : X) < r := by
  classical
  have hex : ∀ p : points, ∃ c ∈ centers, dist (p : X) c < r := by
    intro p
    have hp := hcover (hpoints p.property)
    obtain ⟨c, hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hc, hball⟩ := Set.mem_iUnion.mp hp
    exact ⟨c, hc, by simpa [Metric.mem_ball] using hball⟩
  choose c hc hdist using hex
  exact ⟨fun p => ⟨c p, hc p⟩, fun p => hdist p⟩

/-- Points lying in a cell whose current population is below `threshold`.
This is exactly the set deleted at one pruning scale. -/
noncomputable def lowPopulationPoints
    {alpha beta : Type*}
    (points : Finset alpha) (cell : alpha → beta) (threshold : ℕ) :
    Finset alpha := by
  classical
  exact points.filter fun a =>
    (pointsInCell points cell (cell a)).card < threshold

/-- The total number of points removed at one pruning scale is at most the
number of available cells times the deletion threshold. -/
theorem lowPopulationPoints_card_bound
    {alpha beta : Type*} [Fintype beta]
    (points : Finset alpha) (cell : alpha → beta) (threshold : ℕ) :
    (lowPopulationPoints points cell threshold).card ≤
      Fintype.card beta * threshold := by
  classical
  apply finite_partition_card_bound
    (points := lowPopulationPoints points cell threshold)
    (cell := cell) (threshold := threshold)
  intro b
  by_cases hocc : ∃ a ∈ lowPopulationPoints points cell threshold,
      cell a = b
  · obtain ⟨a, ha, hab⟩ := hocc
    have halow :
        (pointsInCell points cell b).card < threshold := by
      have h := (Finset.mem_filter.mp ha).2
      simpa [lowPopulationPoints, hab] using h
    have hsub :
        pointsInCell (lowPopulationPoints points cell threshold) cell b ⊆
          pointsInCell points cell b := by
      intro q hq
      have hq' :
          q ∈ lowPopulationPoints points cell threshold ∧ cell q = b := by
        simpa [pointsInCell] using hq
      have hqLow := Finset.mem_filter.mp hq'.1
      have hqTarget : q ∈ points ∧ cell q = b := ⟨hqLow.1, hq'.2⟩
      simpa [pointsInCell] using hqTarget
    exact (Finset.card_le_card hsub).trans (Nat.le_of_lt halow)
  · have hempty :
        pointsInCell (lowPopulationPoints points cell threshold) cell b = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨a, ha⟩
      have ha' :
          a ∈ lowPopulationPoints points cell threshold ∧ cell a = b := by
        simpa [pointsInCell] using ha
      exact hocc ⟨a, ha'.1, ha'.2⟩
    rw [hempty]
    simp

/-- A genuine metric cover supplies the cell labels needed by pruning, and
the one-scale deletion charge is therefore controlled by the cardinality of
that very cover (not by an unrelated ambient partition). -/
theorem exists_cover_cell_assignment_with_low_population_bound
    {X : Type*} [PseudoMetricSpace X] (s : Set X) (r : ℝ)
    (points centers : Finset X)
    (hpoints : (points : Set X) ⊆ s)
    (hcover : coversAtRadius s r centers) :
    ∃ cell : points → centers,
      (∀ p : points, dist (p : X) (cell p : X) < r) ∧
      ∀ threshold : ℕ,
        (lowPopulationPoints (Finset.univ : Finset points)
          cell threshold).card ≤ centers.card * threshold := by
  classical
  obtain ⟨cell, hcell⟩ :=
    exists_cover_cell_assignment s r points centers hpoints hcover
  refine ⟨cell, hcell, ?_⟩
  intro threshold
  simpa using
    (lowPopulationPoints_card_bound
      (points := (Finset.univ : Finset points))
      (cell := cell) (threshold := threshold))

/-- Simultaneously extract actual finite covers at a finite family of radii
and assign every retained parameter to a genuine centre at each radius.
The last clause is the cover-cell diameter estimate used by the
cover-adapted pruning argument: two parameters assigned to the same centre
are at distance at most the requested radius.  Thus no abstract partition
is substituted for the covering-number witnesses. -/
theorem exists_multiscale_cover_cell_assignments
    {alpha X level : Type*} [PseudoMetricSpace X] [Fintype level]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (radius : level → ℝ) (bound : level → ENNReal)
    (hradius : ∀ ell, 0 < radius ell)
    (hboundTop : ∀ ell, bound ell ≠ ⊤)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ ell,
      coveringNumber s (radius ell / 2) ≤ bound ell) :
    ∃ centers : level → Finset X,
      (∀ ell, coversAtRadius s (radius ell / 2) (centers ell)) ∧
      (∀ ell, ((centers ell).card : ENNReal) < bound ell + 1) ∧
      ∃ cell : ∀ ell, points → {x // x ∈ centers ell},
        (∀ (ell : level) (a : points),
          dist (image (a : alpha)) (cell ell a : X) < radius ell / 2) ∧
        ∀ (ell : level) (a b : points), cell ell a = cell ell b →
          dist (image (a : alpha)) (image (b : alpha)) ≤ radius ell := by
  classical
  have hexCover : ∀ ell, ∃ centers : Finset X,
      coversAtRadius s (radius ell / 2) centers ∧
        (centers.card : ENNReal) < bound ell + 1 := by
    intro ell
    exact coveringNumber_le_extract_finset_cover s (radius ell / 2)
      (hboundTop ell) (hcovering ell)
  choose centers hcentersCover hcentersCard using hexCover
  have hexCell : ∀ (ell : level) (a : points),
      ∃ c ∈ centers ell,
        dist (image (a : alpha)) c < radius ell / 2 := by
    intro ell a
    have haCover := hcentersCover ell (hpoints a a.property)
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp haCover
    obtain ⟨hcCenter, hac⟩ := Set.mem_iUnion.mp hc
    exact ⟨c, hcCenter, by simpa [Metric.mem_ball] using hac⟩
  choose c hcCenter hdist using hexCell
  let cell : ∀ ell, points → {x // x ∈ centers ell} :=
    fun ell a => ⟨c ell a, hcCenter ell a⟩
  refine ⟨centers, hcentersCover, hcentersCard, cell, ?_, ?_⟩
  · intro ell a
    exact hdist ell a
  · intro ell a b hab
    have hcEq : c ell a = c ell b := congrArg Subtype.val hab
    apply le_of_lt
    calc
      dist (image (a : alpha)) (image (b : alpha)) ≤
          dist (image (a : alpha)) (c ell a) +
            dist (c ell a) (image (b : alpha)) :=
        dist_triangle _ _ _
      _ = dist (image (a : alpha)) (c ell a) +
            dist (image (b : alpha)) (c ell b) := by
        rw [hcEq, dist_comm (c ell b) (image (b : alpha))]
      _ < radius ell / 2 + radius ell / 2 :=
        add_lt_add (hdist ell a) (hdist ell b)
      _ = radius ell := by ring

/-- Package the scale-dependent centre subtypes into one finite cell-label
type.  This is the exact shape consumed by
`exists_packing_three_dyadic_carleson_pruning_with_cells_of_absorption`:
each scale keeps its own finite list of genuine metric-cover centres, while
all lists embed into a single finite ambient label type. -/
theorem exists_common_multiscale_cover_cells
    {alpha X level : Type*} [PseudoMetricSpace X] [Fintype level]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (radius : level → ℝ) (bound : level → ENNReal)
    (hradius : ∀ ell, 0 < radius ell)
    (hboundTop : ∀ ell, bound ell ≠ ⊤)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ ell,
      coveringNumber s (radius ell / 2) ≤ bound ell) :
    ∃ allCenters : Finset X,
      ∃ cells : level → Finset {x // x ∈ allCenters},
        (∀ ell, ((cells ell).card : ENNReal) < bound ell + 1) ∧
        ∃ cell : ∀ ell, points → {x // x ∈ allCenters},
          (∀ (ell : level) (a : points), cell ell a ∈ cells ell) ∧
          (∀ (ell : level) (a : points),
            dist (image (a : alpha)) (cell ell a : X) < radius ell / 2) ∧
          ∀ (ell : level) (a b : points), cell ell a = cell ell b →
            dist (image (a : alpha)) (image (b : alpha)) ≤ radius ell := by
  classical
  obtain ⟨centers, _hcover, hcard, assigned, hnear, hdiameter⟩ :=
    exists_multiscale_cover_cell_assignments
      s points image radius bound hradius hboundTop hpoints hcovering
  let allCenters : Finset X :=
    (Finset.univ : Finset level).biUnion centers
  let lift : ∀ ell, {x // x ∈ centers ell} → {x // x ∈ allCenters} :=
    fun ell x =>
      ⟨x.1, Finset.mem_biUnion.mpr
        ⟨ell, Finset.mem_univ ell, x.2⟩⟩
  have hlift : ∀ ell, Function.Injective (lift ell) := by
    intro ell a b hab
    apply Subtype.ext
    exact congrArg (fun z : {x // x ∈ allCenters} => (z : X)) hab
  let cells : level → Finset {x // x ∈ allCenters} :=
    fun ell => (Finset.univ : Finset {x // x ∈ centers ell}).map
      ⟨lift ell, hlift ell⟩
  let cell : ∀ ell, points → {x // x ∈ allCenters} :=
    fun ell a => lift ell (assigned ell a)
  refine ⟨allCenters, cells, ?_, cell, ?_, ?_, ?_⟩
  · intro ell
    have hcellsCard : (cells ell).card = (centers ell).card := by
      simp [cells]
    rw [hcellsCard]
    exact hcard ell
  · intro ell a
    apply Finset.mem_map.mpr
    exact ⟨assigned ell a, Finset.mem_univ _, rfl⟩
  · intro ell a
    simpa [cell, lift] using hnear ell a
  · intro ell a b hab
    apply hdiameter ell a b
    apply Subtype.ext
    simpa [cell, lift] using
      congrArg (fun z : {x // x ∈ allCenters} => (z : X)) hab

/-- Ambient-domain form of `exists_common_multiscale_cover_cells`.  The
assignment is defined on every parameter, as required by the pruning
interface, but every assertion is restricted to the supplied finite family.
The value outside that family is a fixed genuine cover centre, so no dummy
cell is added and all cardinal estimates are preserved exactly. -/
theorem exists_common_multiscale_cover_cells_on_ambient
    {alpha X level : Type*} [PseudoMetricSpace X] [Fintype level]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (radius : level → ℝ) (bound : level → ENNReal)
    (hpointsNonempty : points.Nonempty)
    (hradius : ∀ ell, 0 < radius ell)
    (hboundTop : ∀ ell, bound ell ≠ ⊤)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ ell,
      coveringNumber s (radius ell / 2) ≤ bound ell) :
    ∃ allCenters : Finset X,
      ∃ cells : level → Finset {x // x ∈ allCenters},
        (∀ ell, ((cells ell).card : ENNReal) < bound ell + 1) ∧
        ∃ cell : level → alpha → {x // x ∈ allCenters},
          (∀ ell a, a ∈ points → cell ell a ∈ cells ell) ∧
          (∀ ell a, a ∈ points →
            dist (image a) (cell ell a : X) < radius ell / 2) ∧
          ∀ ell a, a ∈ points → ∀ b, b ∈ points →
            cell ell a = cell ell b →
              dist (image a) (image b) ≤ radius ell := by
  classical
  obtain ⟨allCenters, cells, hcard, assigned, hassigned, hnear, hdiameter⟩ :=
    exists_common_multiscale_cover_cells
      s points image radius bound hradius hboundTop hpoints hcovering
  obtain ⟨defaultPoint, hdefaultPoint⟩ := hpointsNonempty
  let cell : level → alpha → {x // x ∈ allCenters} :=
    fun ell a => if ha : a ∈ points then assigned ell ⟨a, ha⟩
      else assigned ell ⟨defaultPoint, hdefaultPoint⟩
  refine ⟨allCenters, cells, hcard, cell, ?_, ?_, ?_⟩
  · intro ell a ha
    simpa [cell, ha] using hassigned ell ⟨a, ha⟩
  · intro ell a ha
    simpa [cell, ha] using hnear ell ⟨a, ha⟩
  · intro ell a ha b hb hab
    have hab' : assigned ell ⟨a, ha⟩ = assigned ell ⟨b, hb⟩ := by
      simpa [cell, ha, hb] using hab
    simpa using hdiameter ell ⟨a, ha⟩ ⟨b, hb⟩ hab'

/-- Specialize the genuine common-cell construction to the dyadic radii
`1, 2⁻¹, ..., 2⁻ˡ`.  A covering estimate known uniformly on
`(0, 1]` supplies the cell-cardinality bound at every pruning scale.  The
factor `1 / 4` is forced by the two half-radius conventions: cells of
diameter at most `radius ell` are extracted from covers at
`radius ell / 2`, while the covering hypothesis is normalized at `r / 2`.
-/
theorem exists_dyadic_common_cover_cells_on_ambient
    {alpha X : Type*} [PseudoMetricSpace X]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (levelZero : ℕ) (CAll d : ENNReal)
    (hpointsNonempty : points.Nonempty)
    (hCAllTop : CAll ≠ ⊤)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber s r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal)) :
    ∃ allCenters : Finset X,
      ∃ cells : Fin (levelZero + 1) → Finset {x // x ∈ allCenters},
        (∀ ell, ((cells ell).card : ENNReal) <
          CAll *
            (ENNReal.ofReal (wzDyadicRadius levelZero ell / 4)).rpow
              (-d.toReal) + 1) ∧
        ∃ cell : Fin (levelZero + 1) → alpha → {x // x ∈ allCenters},
          (∀ ell a, a ∈ points → cell ell a ∈ cells ell) ∧
          (∀ ell a, a ∈ points →
            dist (image a) (cell ell a : X) <
              wzDyadicRadius levelZero ell / 2) ∧
          ∀ ell a, a ∈ points → ∀ b, b ∈ points →
            cell ell a = cell ell b →
              dist (image a) (image b) ≤
                wzDyadicRadius levelZero ell := by
  classical
  let radius : Fin (levelZero + 1) → ℝ :=
    wzDyadicRadius levelZero
  let bound : Fin (levelZero + 1) → ENNReal := fun ell =>
    CAll * (ENNReal.ofReal (radius ell / 4)).rpow (-d.toReal)
  have hradius : ∀ ell, 0 < radius ell := by
    intro ell
    simp only [radius, wzDyadicRadius]
    positivity
  have hradiusOne : ∀ ell, radius ell / 2 ≤ 1 := by
    intro ell
    have hpow : radius ell ≤ 1 := by
      dsimp [radius, wzDyadicRadius]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hboundTop : ∀ ell, bound ell ≠ ⊤ := by
    intro ell
    apply ENNReal.mul_ne_top hCAllTop
    apply ENNReal.rpow_ne_top_of_ne_zero
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by
        have := hradius ell
        positivity)
    · exact ENNReal.ofReal_ne_top
  have hcoveringHalf : ∀ ell,
      coveringNumber s (radius ell / 2) ≤ bound ell := by
    intro ell
    have h := hcovering (radius ell / 2)
      (by have := hradius ell; positivity) (hradiusOne ell)
    have hquarter : radius ell / 2 / 2 = radius ell / 4 := by ring
    simpa [bound, hquarter] using h
  simpa [radius, bound] using
    (exists_common_multiscale_cover_cells_on_ambient
      s points image radius bound hpointsNonempty hradius hboundTop
        hpoints hcoveringHalf)

/-- Convert a finite ENNReal cardinal estimate to its real-valued form once
the right-hand side is known to be finite. -/
theorem finset_card_real_lt_of_ennreal_cast_lt
    {alpha : Type*} (points : Finset alpha) {bound : ENNReal}
    (hboundTop : bound ≠ ⊤)
    (hcard : (points.card : ENNReal) < bound) :
    (points.card : ℝ) < bound.toReal := by
  have h := (ENNReal.toReal_lt_toReal (by simp) hboundTop).2 hcard
  simpa using h

/-- The carrier-cover coefficient can be normalized uniformly in the
terminal dyadic depth.  If the covering exponent `d` is at most
`3 + packingSlack`, then the fixed coefficient
`CAll.toReal * 4 ^ d.toReal + 1` absorbs both half-radius conventions and
the finite-cover `+1`.  In particular this constant is independent of
`levelZero`, hence independent of the physical thickness. -/
theorem dyadic_cover_bound_normalization
    (levelZero : ℕ) (ell : Fin (levelZero + 1))
    (CAll d : ENNReal) (packingSlack : ℝ)
    (hCAllTop : CAll ≠ ⊤)
    (hpackingSlack : 0 ≤ packingSlack)
    (hd : d.toReal ≤ 3 + packingSlack) :
    (CAll *
          (ENNReal.ofReal (wzDyadicRadius levelZero ell / 4)).rpow
            (-d.toReal) + 1).toReal ≤
      (CAll.toReal * (4 : ℝ) ^ d.toReal + 1) *
        ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val := by
  let radius : ℝ := wzDyadicRadius levelZero ell
  have hradius : 0 < radius := by
    dsimp [radius, wzDyadicRadius]
    positivity
  let base : ENNReal := ENNReal.ofReal (radius / 4)
  have hbaseZero : base ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hbaseTop : base ≠ ⊤ := ENNReal.ofReal_ne_top
  have htermTop : CAll * base.rpow (-d.toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top hCAllTop
      (ENNReal.rpow_ne_top_of_ne_zero hbaseZero hbaseTop)
  have htoReal :
      (CAll * base.rpow (-d.toReal) + 1).toReal =
        CAll.toReal * (radius / 4) ^ (-d.toReal) + 1 := by
    rw [ENNReal.toReal_add htermTop (by norm_num), ENNReal.toReal_mul,
      show (base.rpow (-d.toReal)).toReal =
          base.toReal ^ (-d.toReal) from
        (ENNReal.toReal_rpow base (-d.toReal)).symm,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have hdyadicCore :
      (wzDyadicRadius levelZero ell) ^ (-d.toReal) =
        ((2 : ℝ) ^ d.toReal) ^ ell.val := by
    rw [wzDyadicRadius, dyadic_inverse_nat_pow_eq_rpow_neg]
    calc
      ((2 : ℝ) ^ (-(ell.val : ℝ))) ^ (-d.toReal) =
          (2 : ℝ) ^ ((-(ell.val : ℝ)) * (-d.toReal)) := by
            symm
            exact Real.rpow_mul (by norm_num)
              (-(ell.val : ℝ)) (-d.toReal)
      _ = (2 : ℝ) ^ (d.toReal * (ell.val : ℝ)) := by
            congr 1
            ring
      _ = ((2 : ℝ) ^ d.toReal) ^ (ell.val : ℝ) := by
            exact Real.rpow_mul (by norm_num) d.toReal ell.val
      _ = ((2 : ℝ) ^ d.toReal) ^ ell.val := by
            exact Real.rpow_natCast ((2 : ℝ) ^ d.toReal) ell.val
  have hdyadicPower :
      (radius / 4) ^ (-d.toReal) =
        (4 : ℝ) ^ d.toReal *
          ((2 : ℝ) ^ d.toReal) ^ ell.val := by
    calc
      (radius / 4) ^ (-d.toReal) =
          radius ^ (-d.toReal) / (4 : ℝ) ^ (-d.toReal) := by
            exact Real.div_rpow hradius.le (by norm_num) (-d.toReal)
      _ = (((2 : ℝ) ^ d.toReal) ^ ell.val) /
          ((4 : ℝ) ^ d.toReal)⁻¹ := by
            rw [show radius ^ (-d.toReal) =
                ((2 : ℝ) ^ d.toReal) ^ ell.val by
                  simpa [radius] using hdyadicCore,
              Real.rpow_neg (by norm_num) d.toReal]
      _ = (4 : ℝ) ^ d.toReal *
          ((2 : ℝ) ^ d.toReal) ^ ell.val := by
            rw [div_eq_mul_inv, inv_inv]
            ring
  have hbasePower :
      (2 : ℝ) ^ d.toReal ≤ (2 : ℝ) ^ (3 + packingSlack) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hd
  have hpowNat :
      ((2 : ℝ) ^ d.toReal) ^ ell.val ≤
        ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val := by
    gcongr
  have hqNonneg : 0 ≤ 3 + packingSlack := by linarith
  have hbaseOne :
      (1 : ℝ) ≤ (2 : ℝ) ^ (3 + packingSlack) :=
    Real.one_le_rpow (by norm_num) hqNonneg
  have hpowOne :
      (1 : ℝ) ≤ ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val := by
    exact one_le_pow₀ hbaseOne
  have hcoefficient :
      0 ≤ CAll.toReal * (4 : ℝ) ^ d.toReal := by positivity
  change (CAll * base.rpow (-d.toReal) + 1).toReal ≤ _
  rw [htoReal, hdyadicPower]
  calc
    CAll.toReal *
          ((4 : ℝ) ^ d.toReal *
            ((2 : ℝ) ^ d.toReal) ^ ell.val) + 1 =
        (CAll.toReal * (4 : ℝ) ^ d.toReal) *
            ((2 : ℝ) ^ d.toReal) ^ ell.val + 1 := by ring
    _ ≤ (CAll.toReal * (4 : ℝ) ^ d.toReal) *
          ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val +
            ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val :=
      add_le_add
        (mul_le_mul_of_nonneg_left hpowNat hcoefficient) hpowOne
    _ = (CAll.toReal * (4 : ℝ) ^ d.toReal + 1) *
          ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val := by ring

/-- Real-cardinality version of the dyadic common-cell construction.  The
only extra input is the explicit normalization inequality that absorbs the
finite-cover `+1` into the geometric cell constant.  Its conclusion is in
the precise form required by packing-three pruning. -/
theorem exists_dyadic_common_cover_cells_on_ambient_with_real_bound
    {alpha X : Type*} [PseudoMetricSpace X]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (levelZero : ℕ) (CAll d : ENNReal)
    (packingSlack cellConstant : ℝ)
    (hpointsNonempty : points.Nonempty)
    (hCAllTop : CAll ≠ ⊤)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber s r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal))
    (hnormalize : ∀ ell : Fin (levelZero + 1),
      (CAll *
          (ENNReal.ofReal (wzDyadicRadius levelZero ell / 4)).rpow
            (-d.toReal) + 1).toReal ≤
        cellConstant * ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val) :
    ∃ allCenters : Finset X,
      ∃ cells : Fin (levelZero + 1) → Finset {x // x ∈ allCenters},
        (∀ ell, ((cells ell).card : ℝ) ≤
          cellConstant * ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val) ∧
        ∃ cell : Fin (levelZero + 1) → alpha → {x // x ∈ allCenters},
          (∀ ell a, a ∈ points → cell ell a ∈ cells ell) ∧
          (∀ ell a, a ∈ points →
            dist (image a) (cell ell a : X) <
              wzDyadicRadius levelZero ell / 2) ∧
          ∀ ell a, a ∈ points → ∀ b, b ∈ points →
            cell ell a = cell ell b →
              dist (image a) (image b) ≤
                wzDyadicRadius levelZero ell := by
  classical
  obtain ⟨allCenters, cells, hcard, cell, hcell, hnear, hdiameter⟩ :=
    exists_dyadic_common_cover_cells_on_ambient
      s points image levelZero CAll d hpointsNonempty hCAllTop hpoints
        hcovering
  refine ⟨allCenters, cells, ?_, cell, hcell, hnear, hdiameter⟩
  intro ell
  have hradius : 0 < wzDyadicRadius levelZero ell := by
    simp only [wzDyadicRadius]
    positivity
  have hrightTop :
      CAll *
          (ENNReal.ofReal (wzDyadicRadius levelZero ell / 4)).rpow
            (-d.toReal) + 1 ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.mul_ne_top hCAllTop
      apply ENNReal.rpow_ne_top_of_ne_zero
      · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
      · exact ENNReal.ofReal_ne_top
    · norm_num
  exact (finset_card_real_lt_of_ennreal_cast_lt
    (cells ell) hrightTop (hcard ell)).le.trans (hnormalize ell)

/-- Uniform form of the real-cardinality cover-cell extraction.  The cell
constant is now explicit and independent of both the terminal scale and the
retained finite family. -/
theorem exists_dyadic_common_cover_cells_on_ambient_with_uniform_real_bound
    {alpha X : Type*} [PseudoMetricSpace X]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (levelZero : ℕ) (CAll d : ENNReal) (packingSlack : ℝ)
    (hpointsNonempty : points.Nonempty)
    (hCAllTop : CAll ≠ ⊤)
    (hpackingSlack : 0 ≤ packingSlack)
    (hd : d.toReal ≤ 3 + packingSlack)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber s r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal)) :
    ∃ allCenters : Finset X,
      ∃ cells : Fin (levelZero + 1) → Finset {x // x ∈ allCenters},
        (∀ ell, ((cells ell).card : ℝ) ≤
          (CAll.toReal * (4 : ℝ) ^ d.toReal + 1) *
            ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val) ∧
        ∃ cell : Fin (levelZero + 1) → alpha → {x // x ∈ allCenters},
          (∀ ell a, a ∈ points → cell ell a ∈ cells ell) ∧
          (∀ ell a, a ∈ points →
            dist (image a) (cell ell a : X) <
              wzDyadicRadius levelZero ell / 2) ∧
          ∀ ell a, a ∈ points → ∀ b, b ∈ points →
            cell ell a = cell ell b →
              dist (image a) (image b) ≤
                wzDyadicRadius levelZero ell := by
  apply exists_dyadic_common_cover_cells_on_ambient_with_real_bound
    s points image levelZero CAll d packingSlack
      (CAll.toReal * (4 : ℝ) ^ d.toReal + 1)
      hpointsNonempty hCAllTop hpoints hcovering
  intro ell
  exact dyadic_cover_bound_normalization levelZero ell CAll d packingSlack
    hCAllTop hpackingSlack hd

/-- A uniform carrier covering estimate now feeds the packing-three pruning
ledger directly.  The cover centers, ambient marked-point assignment, and the
terminal retained family are returned together, so the terminal populations
cannot be detached from the genuine carrier cells that produced them. -/
theorem exists_packing_three_dyadic_carleson_pruning_from_uniform_cover
    {alpha X : Type*} [PseudoMetricSpace X]
    (s : Set X) (points : Finset alpha) (image : alpha → X)
    (levelZero : ℕ) (CAll d : ENNReal)
    (delta packingSlack pointSlack kappa thresholdConstant
      pointConstant : ℝ)
    (hpointsNonempty : points.Nonempty)
    (hCAllTop : CAll ≠ ⊤)
    (hdelta : 0 < delta)
    (hdyadic : delta = (2 : ℝ)⁻¹ ^ levelZero)
    (hpackingSlack : 0 < packingSlack)
    (hd : d.toReal ≤ 3 + packingSlack)
    (hthresholdConstant : 0 ≤ thresholdConstant)
    (hpointLower :
      pointConstant * delta ^ (-3 + pointSlack) ≤ (points.card : ℝ))
    (habsorb :
      (4 * (((CAll.toReal * (4 : ℝ) ^ d.toReal + 1) *
          thresholdConstant)) * (2 : ℝ) ^ packingSlack /
            ((2 : ℝ) ^ packingSlack - 1)) *
        delta ^ (kappa - packingSlack - pointSlack) ≤ pointConstant)
    (hpoints : ∀ a ∈ points, image a ∈ s)
    (hcovering : ∀ r : ℝ, 0 < r → r ≤ 1 →
      coveringNumber s r ≤
        CAll * (ENNReal.ofReal (r / 2)).rpow (-d.toReal)) :
    ∃ allCenters : Finset X,
      ∃ cells : Fin (levelZero + 1) → Finset {x // x ∈ allCenters},
        ∃ cell : Fin (levelZero + 1) → alpha → {x // x ∈ allCenters},
          (∀ ell, ((cells ell).card : ℝ) ≤
            (CAll.toReal * (4 : ℝ) ^ d.toReal + 1) *
              ((2 : ℝ) ^ (3 + packingSlack)) ^ ell.val) ∧
          (∀ ell a, a ∈ points → cell ell a ∈ cells ell) ∧
          (∀ ell a, a ∈ points → ∀ b, b ∈ points →
            cell ell a = cell ell b →
              dist (image a) (image b) ≤ wzDyadicRadius levelZero ell) ∧
          ∃ retained : Finset alpha,
            retained ⊆ points ∧
            points.card ≤ 2 * retained.card ∧
            (∀ ell b,
              (pointsInCell retained (cell ell) b).Nonempty →
                activeCarrierPruningThreshold
                    (fun j =>
                      (thresholdConstant * delta ^ (kappa - 3)) *
                        (1 / 8 : ℝ) ^ j.val) ell ≤
                  (pointsInCell retained (cell ell) b).card) ∧
            ∀ ell a, a ∈ retained →
              (thresholdConstant * delta ^ (kappa - 3)) *
                  (1 / 8 : ℝ) ^ ell.val ≤
                ((pointsInMetricClosedBall retained image a
                  (wzDyadicRadius levelZero ell)).card : ℝ) := by
  obtain ⟨allCenters, cells, hcellBound, cell, hcell, _hcenter, hdiam⟩ :=
    exists_dyadic_common_cover_cells_on_ambient_with_uniform_real_bound
      s points image levelZero CAll d packingSlack hpointsNonempty hCAllTop
        hpackingSlack.le hd hpoints hcovering
  refine ⟨allCenters, cells, cell, hcellBound, hcell, hdiam, ?_⟩
  apply exists_packing_three_dyadic_carleson_pruning_with_cells_of_absorption
    levelZero cells points cell
      (fun ell =>
        (thresholdConstant * delta ^ (kappa - 3)) *
          (1 / 8 : ℝ) ^ ell.val)
      image (wzDyadicRadius levelZero)
      delta packingSlack pointSlack kappa
      (CAll.toReal * (4 : ℝ) ^ d.toReal + 1)
      thresholdConstant pointConstant hdelta hdyadic hpackingSlack
  · positivity
  · exact hthresholdConstant
  · exact hpointLower
  · exact habsorb
  · intro ell
    positivity
  · exact hcellBound
  · intro ell
    exact le_rfl
  · intro ell
    dsimp [wzDyadicRadius]
    positivity
  · exact hcell
  · intro ell a ha b hb heq
    exact hdiam ell b hb a ha heq

/-- Union of all points charged to low-population cells over a finite list
of scales. -/
noncomputable def lowPopulationScaleUnion
    {alpha beta level : Type*} [Fintype level]
    [DecidableEq alpha]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) : Finset alpha :=
  Finset.univ.biUnion fun ell =>
    lowPopulationPoints points (cell ell) (threshold ell)

/-- The multiscale deletion charge is bounded by the sum of the cellwise
charges.  No disjointness between scales is assumed. -/
theorem lowPopulationScaleUnion_card_bound
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) :
    (lowPopulationScaleUnion points cell threshold).card ≤
      ∑ ell : level, Fintype.card beta * threshold ell := by
  classical
  calc
    (lowPopulationScaleUnion points cell threshold).card ≤
        ∑ ell ∈ (Finset.univ : Finset level),
          (lowPopulationPoints points (cell ell) (threshold ell)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ ell ∈ (Finset.univ : Finset level),
          Fintype.card beta * threshold ell := by
      apply Finset.sum_le_sum
      intro ell hell
      exact lowPopulationPoints_card_bound
        points (cell ell) (threshold ell)
    _ = ∑ ell : level, Fintype.card beta * threshold ell := by
      rfl

/-- Retain the points not charged to a low-population cell at any selected
scale. -/
noncomputable def retainedAfterLowPopulationPruning
    {alpha beta level : Type*} [Fintype level]
    [DecidableEq alpha]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ) : Finset alpha :=
  points \ lowPopulationScaleUnion points cell threshold

/-- If the total multiscale deletion budget is at most half the original
population, the simultaneous pruning retains at least half the points. -/
theorem retainedAfterLowPopulationPruning_half
    {alpha beta level : Type*} [Fintype beta] [Fintype level]
    [DecidableEq alpha]
    (points : Finset alpha) (cell : level → alpha → beta)
    (threshold : level → ℕ)
    (hbudget :
      2 * (∑ ell : level, Fintype.card beta * threshold ell) ≤
        points.card) :
    points.card ≤
      2 * (retainedAfterLowPopulationPruning points cell threshold).card := by
  classical
  let removed := lowPopulationScaleUnion points cell threshold
  let retained := retainedAfterLowPopulationPruning points cell threshold
  have hremoved : removed.card ≤
      ∑ ell : level, Fintype.card beta * threshold ell := by
    exact lowPopulationScaleUnion_card_bound points cell threshold
  have htworemoved : 2 * removed.card ≤ points.card := by
    exact (Nat.mul_le_mul_left 2 hremoved).trans hbudget
  have hremovedSubset : removed ⊆ points := by
    intro a ha
    dsimp [removed, lowPopulationScaleUnion] at ha
    obtain ⟨ell, hell, haell⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp haell).1
  have hdecomp : retained.card + removed.card = points.card := by
    simpa [retained, retainedAfterLowPopulationPruning, removed] using
      (Finset.card_sdiff_add_card_eq_card hremovedSubset)
  change points.card ≤ 2 * retained.card
  omega

end StickyKakeya4
