import Theorems.Thm_StickyKakeya4_front_parametrization
import Theorems.Thm_StickyKakeya4_compact_front
import Theorems.Thm_StickyKakeya4_frostman_mass_distribution
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace Topology Function

noncomputable section

namespace StickyKakeya4

/-- The metric-sphere model used by `Measure.toSphere`, rewritten as the
norm-one direction subtype used by the sticky selector interface. -/
def metricSphereToNormSphere
    (x : Metric.sphere (0 : E4) 1) : {theta : E4 // ‖theta‖ = 1} :=
  ⟨(x : E4), by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property⟩

def normSphereToMetricSphere
    (x : {theta : E4 // ‖theta‖ = 1}) : Metric.sphere (0 : E4) 1 :=
  ⟨(x : E4), by
    simpa [Metric.mem_sphere, dist_zero_right] using x.property⟩

theorem measurable_metricSphereToNormSphere :
    Measurable metricSphereToNormSphere := by
  exact
    (measurable_subtype_coe :
      Measurable (fun x : Metric.sphere (0 : E4) 1 => (x : E4))).subtype_mk

noncomputable instance metricSphereNonempty :
    Nonempty (Metric.sphere (0 : E4) 1) := by
  let e : E4 := EuclideanSpace.single (0 : Fin 4) 1
  refine ⟨⟨e, ?_⟩⟩
  rw [Metric.mem_sphere, dist_zero_right]
  simp [e]

noncomputable def metricSphereFiniteMeasure :
    FiniteMeasure (Metric.sphere (0 : E4) 1) :=
  ⟨volume.toSphere, inferInstance⟩

theorem metricSphereFiniteMeasure_ne_zero : metricSphereFiniteMeasure ≠ 0 := by
  intro hzero
  have hmeasure := congrArg
    (fun q : FiniteMeasure (Metric.sphere (0 : E4) 1) =>
      (q : Measure (Metric.sphere (0 : E4) 1))) hzero
  change volume.toSphere =
    (0 : Measure (Metric.sphere (0 : E4) 1)) at hmeasure
  exact volume.toSphere_ne_zero hmeasure

/-- Normalized rotation-invariant surface measure on the metric unit sphere.
The explicit basis vector supplies the nonemptiness needed by normalization. -/
noncomputable def metricSphereProbability :
    ProbabilityMeasure (Metric.sphere (0 : E4) 1) := by
  exact metricSphereFiniteMeasure.normalize

/-- The canonical probability measure on the norm-one directions occurring
in the selector statements. -/
noncomputable def normSphereProbability :
    ProbabilityMeasure {theta : E4 // ‖theta‖ = 1} :=
  ProbabilityMeasure.map
    metricSphereProbability
    measurable_metricSphereToNormSphere.aemeasurable

/-- Every nonempty metric ball on the unit sphere has positive normalized
surface measure. -/
theorem metricSphereProbability_ball_ne_zero
    (theta : Metric.sphere (0 : E4) 1) {r : ℝ} (hr : 0 < r) :
    (metricSphereProbability :
      Measure (Metric.sphere (0 : E4) 1)) (Metric.ball theta r) ≠ 0 := by
  let m : FiniteMeasure (Metric.sphere (0 : E4) 1) :=
    metricSphereFiniteMeasure
  have hm : m ≠ 0 := metricSphereFiniteMeasure_ne_zero
  change (m.normalize : Measure (Metric.sphere (0 : E4) 1))
      (Metric.ball theta r) ≠ 0
  rw [m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
  apply mul_ne_zero
  · exact ne_of_gt (by
      have hmass : 0 < m.mass :=
        pos_iff_ne_zero.mpr (m.mass_nonzero_iff.mpr hm)
      positivity)
  · change volume.toSphere (Metric.ball theta r) ≠ 0
    exact Measure.IsOpenPosMeasure.open_pos
      (Metric.ball theta r) Metric.isOpen_ball
        ⟨theta, Metric.mem_ball_self hr⟩

/-- The same positive-ball statement in the norm-one direction model used
by the selector. -/
theorem normSphereProbability_ball_ne_zero
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ} (hr : 0 < r) :
    (normSphereProbability :
      Measure {theta : E4 // ‖theta‖ = 1}) (Metric.ball theta r) ≠ 0 := by
  let theta' : Metric.sphere (0 : E4) 1 := normSphereToMetricSphere theta
  have hpre :
      metricSphereToNormSphere ⁻¹' Metric.ball theta r =
        Metric.ball theta' r := by
    ext phi
    change dist (phi : E4) (theta : E4) < r ↔
      dist (phi : E4) (theta : E4) < r
    rfl
  rw [normSphereProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_metricSphereToNormSphere
    (Metric.isOpen_ball.measurableSet), hpre]
  exact metricSphereProbability_ball_ne_zero theta' hr

/-- The radial unit segment whose endpoint direction is `theta`.  Its mark is
`1/2`, so its actual marked front is exactly `{s • theta | 0 ≤ s ≤ 1}`. -/
def radialMarkedLine (theta : Metric.sphere (0 : E4) 1) : MarkedLine :=
  (((theta : E4), 0), 1 / 2)

/-- The measurable polar piece obtained from a set of unit directions and
radii strictly between zero and one.  It is written through the polar
homeomorphism so measurability is part of the construction rather than an
extra regularity assumption on a pointwise scalar-product image. -/
def radialPolarPiece (directions : Set (Metric.sphere (0 : E4) 1)) : Set E4 :=
  ((fun z : ({0}ᶜ : Set E4) => (z : E4)) ''
    ((homeomorphUnitSphereProd E4) ⁻¹'
      (directions ×ˢ Set.Iio
        (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))))

theorem measurableSet_radialPolarPiece
    {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions) :
    MeasurableSet (radialPolarPiece directions) := by
  unfold radialPolarPiece
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : E4)).compl).measurableSet_image'
  exact (hdirections.prod measurableSet_Iio).preimage
    (homeomorphUnitSphereProd E4).measurable

theorem radialPolarPiece_subset_ball
    (directions : Set (Metric.sphere (0 : E4) 1)) :
    radialPolarPiece directions ⊆ Metric.ball (0 : E4) 1 := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hradius : (((homeomorphUnitSphereProd E4) z).2 : ℝ) < 1 := hz.2
  simpa using hradius

theorem radialPolarPiece_point_representation
    {directions : Set (Metric.sphere (0 : E4) 1)} {x : E4}
    (hx : x ∈ radialPolarPiece directions) :
    ∃ theta ∈ directions, ∃ radius ∈ Set.Ioo (0 : ℝ) 1,
      x = radius • (theta : E4) := by
  rcases hx with ⟨z, hz, rfl⟩
  let theta : Metric.sphere (0 : E4) 1 :=
    ((homeomorphUnitSphereProd E4) z).1
  let radius : ℝ := (((homeomorphUnitSphereProd E4) z).2 : ℝ)
  have htheta : theta ∈ directions := hz.1
  have hradiusPositive : 0 < radius :=
    ((homeomorphUnitSphereProd E4) z).2.property
  have hradiusOne : radius < 1 := by
    exact hz.2
  have hinversePolar :
      (((homeomorphUnitSphereProd E4).symm
        ((homeomorphUnitSphereProd E4) z)) : E4) =
        radius • (theta : E4) := by
    simpa only [radius, theta] using
      (homeomorphUnitSphereProd_symm_apply_coe E4
        ((homeomorphUnitSphereProd E4) z))
  have hzPolar : (z : E4) = radius • (theta : E4) := by
    have hzinverse := congrArg
      (fun w : ({0}ᶜ : Set E4) => (w : E4))
      ((homeomorphUnitSphereProd E4).symm_apply_apply z)
    calc
      (z : E4) =
          (((homeomorphUnitSphereProd E4).symm
            ((homeomorphUnitSphereProd E4) z)) : E4) := hzinverse.symm
      _ = radius • (theta : E4) := hinversePolar
  exact ⟨theta, htheta, radius, ⟨hradiusPositive, hradiusOne⟩, hzPolar⟩

theorem radialPolarPiece_subset_unitFront
    (directions : Set (Metric.sphere (0 : E4) 1)) :
    radialPolarPiece directions ⊆
      unitFront (radialMarkedLine '' directions) := by
  intro x hx
  obtain ⟨theta, htheta, radius, hradius, rfl⟩ :=
    radialPolarPiece_point_representation hx
  refine ⟨radialMarkedLine theta, ⟨theta, htheta, rfl⟩,
    radius - 1 / 2, ?_, ?_⟩
  · constructor <;> linarith [hradius.1, hradius.2]
  · change radius • (theta : E4) =
      (0 : E4) + ((1 / 2 : ℝ) + (radius - 1 / 2)) • (theta : E4)
    simp

theorem radialPolarPiece_volume_ne_zero
    {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0) :
    volume (radialPolarPiece directions) ≠ 0 := by
  have hcone :
      volume (Set.Ioo (0 : ℝ) 1 •
        ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) '' directions)) ≠ 0 := by
    intro hzero
    apply hdirectionsPositive
    rw [volume.toSphere_apply' hdirections, hzero, mul_zero]
  have hpolar := volume.toSphere_apply_aux directions
    (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))
  unfold radialPolarPiece
  rw [hpolar]
  exact hcone

theorem radialPolarPiece_volume_ne_top
    (directions : Set (Metric.sphere (0 : E4) 1)) :
    volume (radialPolarPiece directions) ≠ ⊤ := by
  exact ne_of_lt <|
    (measure_mono (radialPolarPiece_subset_ball directions)).trans_lt
      measure_ball_lt_top

/-- A positive surface-measure bush through one point has a genuine
four-dimensional polar front, hence it lands directly in the Frostman branch
of the corrected Prove2Me milestone. -/
theorem radial_direction_bush_has_front_frostman
    (directions : Set (Metric.sphere (0 : E4) 1))
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0) :
    HasFrontFrostmanMeasures (radialMarkedLine '' directions) := by
  exact hasFrontFrostmanMeasures_of_positive_finite_volume_subset
    (radialMarkedLine '' directions) (radialPolarPiece directions)
    (measurableSet_radialPolarPiece hdirections)
    (radialPolarPiece_subset_unitFront directions)
    (radialPolarPiece_volume_ne_zero hdirections hdirectionsPositive)
    (radialPolarPiece_volume_ne_top directions)

/-- Translate a polar piece to an arbitrary physical bush center. -/
def translatedRadialPolarPiece (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1)) : Set E4 :=
  (fun x : E4 => center + x) '' radialPolarPiece directions

theorem measurableSet_translatedRadialPolarPiece
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions) :
    MeasurableSet (translatedRadialPolarPiece center directions) := by
  exact (Homeomorph.addLeft center).measurableEmbedding.measurableSet_image'
    (measurableSet_radialPolarPiece hdirections)

theorem volume_translatedRadialPolarPiece
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions) :
    volume (translatedRadialPolarPiece center directions) =
      volume (radialPolarPiece directions) := by
  have hpreimage :
      translatedRadialPolarPiece center directions =
        (fun x : E4 => -center + x) ⁻¹' radialPolarPiece directions := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨-center + x, hx, ?_⟩
      module
  rw [hpreimage]
  exact (measurePreserving_add_left volume (-center)).measure_preimage
    (measurableSet_radialPolarPiece hdirections).nullMeasurableSet

/-- If the physical front contains, from one common center, a full radial
interval in a positive surface-measure family of directions, normalized
Lebesgue measure on that translated polar piece supplies the Frostman output.
This is the exact geometric terminal needed after extracting a limiting bush
from the concentration boundary. -/
theorem common_center_direction_bush_has_front_frostman
    (selector : Set MarkedLine) (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0)
    (hfront : ∀ theta ∈ directions, ∀ radius : ℝ,
      radius ∈ Set.Ioo (0 : ℝ) 1 →
        center + radius • (theta : E4) ∈ unitFront selector) :
    HasFrontFrostmanMeasures selector := by
  have hpieceFront :
      translatedRadialPolarPiece center directions ⊆ unitFront selector := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨theta, htheta, radius, hradius, rfl⟩ :=
      radialPolarPiece_point_representation hy
    exact hfront theta htheta radius hradius
  have hpiecePositive :
      volume (translatedRadialPolarPiece center directions) ≠ 0 := by
    rw [volume_translatedRadialPolarPiece center hdirections]
    exact radialPolarPiece_volume_ne_zero hdirections hdirectionsPositive
  have hpieceFinite :
      volume (translatedRadialPolarPiece center directions) ≠ ⊤ := by
    rw [volume_translatedRadialPolarPiece center hdirections]
    exact radialPolarPiece_volume_ne_top directions
  exact hasFrontFrostmanMeasures_of_positive_finite_volume_subset
    selector (translatedRadialPolarPiece center directions)
    (measurableSet_translatedRadialPolarPiece center hdirections)
    hpieceFront hpiecePositive hpieceFinite

/-- The polar piece with an arbitrary positive radial cutoff.  This version is
needed when a common point lies in the interior of the selected unit segments:
one only obtains a one-sided bush of some length `rho`, not necessarily length
one. -/
def radialPolarPieceBelow (directions : Set (Metric.sphere (0 : E4) 1))
    (rho : ℝ) (hrho : 0 < rho) : Set E4 :=
  ((fun z : ({0}ᶜ : Set E4) => (z : E4)) ''
    ((homeomorphUnitSphereProd E4) ⁻¹'
      (directions ×ˢ Set.Iio
        (⟨rho, hrho⟩ : Set.Ioi (0 : ℝ)))))

theorem measurableSet_radialPolarPieceBelow
    {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions) {rho : ℝ} (hrho : 0 < rho) :
    MeasurableSet (radialPolarPieceBelow directions rho hrho) := by
  unfold radialPolarPieceBelow
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : E4)).compl).measurableSet_image'
  exact (hdirections.prod measurableSet_Iio).preimage
    (homeomorphUnitSphereProd E4).measurable

theorem radialPolarPieceBelow_subset_ball
    (directions : Set (Metric.sphere (0 : E4) 1))
    {rho : ℝ} (hrho : 0 < rho) :
    radialPolarPieceBelow directions rho hrho ⊆ Metric.ball (0 : E4) rho := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hradius : (((homeomorphUnitSphereProd E4) z).2 : ℝ) < rho := hz.2
  simpa using hradius

theorem radialPolarPieceBelow_point_representation
    {directions : Set (Metric.sphere (0 : E4) 1)} {rho : ℝ}
    (hrho : 0 < rho) {x : E4}
    (hx : x ∈ radialPolarPieceBelow directions rho hrho) :
    ∃ theta ∈ directions, ∃ radius ∈ Set.Ioo (0 : ℝ) rho,
      x = radius • (theta : E4) := by
  rcases hx with ⟨z, hz, rfl⟩
  let theta : Metric.sphere (0 : E4) 1 :=
    ((homeomorphUnitSphereProd E4) z).1
  let radius : ℝ := (((homeomorphUnitSphereProd E4) z).2 : ℝ)
  have htheta : theta ∈ directions := hz.1
  have hradiusPositive : 0 < radius :=
    ((homeomorphUnitSphereProd E4) z).2.property
  have hradiusRho : radius < rho := hz.2
  have hinversePolar :
      (((homeomorphUnitSphereProd E4).symm
        ((homeomorphUnitSphereProd E4) z)) : E4) =
        radius • (theta : E4) := by
    simpa only [radius, theta] using
      (homeomorphUnitSphereProd_symm_apply_coe E4
        ((homeomorphUnitSphereProd E4) z))
  have hzPolar : (z : E4) = radius • (theta : E4) := by
    have hzinverse := congrArg
      (fun w : ({0}ᶜ : Set E4) => (w : E4))
      ((homeomorphUnitSphereProd E4).symm_apply_apply z)
    calc
      (z : E4) =
          (((homeomorphUnitSphereProd E4).symm
            ((homeomorphUnitSphereProd E4) z)) : E4) := hzinverse.symm
      _ = radius • (theta : E4) := hinversePolar
  exact ⟨theta, htheta, radius,
    ⟨hradiusPositive, hradiusRho⟩, hzPolar⟩

theorem radialPolarPieceBelow_volume_ne_zero
    {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0)
    {rho : ℝ} (hrho : 0 < rho) :
    volume (radialPolarPieceBelow directions rho hrho) ≠ 0 := by
  have hunit :
      volume (Set.Ioo (0 : ℝ) 1 •
        ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) '' directions)) ≠ 0 := by
    intro hzero
    apply hdirectionsPositive
    rw [volume.toSphere_apply' hdirections, hzero, mul_zero]
  have hcone :
      volume (Set.Ioo (0 : ℝ) rho •
        ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) '' directions)) ≠ 0 := by
    have hIoo : Set.Ioo (0 : ℝ) rho = rho • Set.Ioo (0 : ℝ) 1 := by
      rw [LinearOrderedField.smul_Ioo hrho]
      simp
    rw [hIoo, smul_assoc, volume.addHaar_smul_of_nonneg hrho.le]
    exact mul_ne_zero (by positivity) hunit
  have hpolar := volume.toSphere_apply_aux directions
    (⟨rho, hrho⟩ : Set.Ioi (0 : ℝ))
  unfold radialPolarPieceBelow
  rw [hpolar]
  exact hcone

theorem radialPolarPieceBelow_volume_ne_top
    (directions : Set (Metric.sphere (0 : E4) 1))
    {rho : ℝ} (hrho : 0 < rho) :
    volume (radialPolarPieceBelow directions rho hrho) ≠ ⊤ := by
  exact ne_of_lt <|
    (measure_mono
      (radialPolarPieceBelow_subset_ball directions hrho)).trans_lt
      measure_ball_lt_top

def translatedRadialPolarPieceBelow (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (rho : ℝ) (hrho : 0 < rho) : Set E4 :=
  (fun x : E4 => center + x) ''
    radialPolarPieceBelow directions rho hrho

theorem measurableSet_translatedRadialPolarPieceBelow
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    {rho : ℝ} (hrho : 0 < rho) :
    MeasurableSet
      (translatedRadialPolarPieceBelow center directions rho hrho) := by
  exact (Homeomorph.addLeft center).measurableEmbedding.measurableSet_image'
    (measurableSet_radialPolarPieceBelow hdirections hrho)

theorem volume_translatedRadialPolarPieceBelow
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    {rho : ℝ} (hrho : 0 < rho) :
    volume (translatedRadialPolarPieceBelow center directions rho hrho) =
      volume (radialPolarPieceBelow directions rho hrho) := by
  have hpreimage :
      translatedRadialPolarPieceBelow center directions rho hrho =
        (fun x : E4 => -center + x) ⁻¹'
          radialPolarPieceBelow directions rho hrho := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨-center + x, hx, ?_⟩
      module
  rw [hpreimage]
  exact (measurePreserving_add_left volume (-center)).measure_preimage
    (measurableSet_radialPolarPieceBelow hdirections hrho).nullMeasurableSet

/-- A positive surface-measure one-sided bush of any fixed positive length
already supplies the exact Frostman alternative required by milestone 6. -/
theorem common_center_direction_bush_at_radius_has_front_frostman
    (selector : Set MarkedLine) (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0)
    {rho : ℝ} (hrho : 0 < rho)
    (hfront : ∀ theta ∈ directions, ∀ radius : ℝ,
      radius ∈ Set.Ioo (0 : ℝ) rho →
        center + radius • (theta : E4) ∈ unitFront selector) :
    HasFrontFrostmanMeasures selector := by
  have hpieceFront :
      translatedRadialPolarPieceBelow center directions rho hrho ⊆
        unitFront selector := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨theta, htheta, radius, hradius, rfl⟩ :=
      radialPolarPieceBelow_point_representation hrho hy
    exact hfront theta htheta radius hradius
  have hpiecePositive :
      volume (translatedRadialPolarPieceBelow center directions rho hrho) ≠ 0 := by
    rw [volume_translatedRadialPolarPieceBelow center hdirections hrho]
    exact radialPolarPieceBelow_volume_ne_zero
      hdirections hdirectionsPositive hrho
  have hpieceFinite :
      volume (translatedRadialPolarPieceBelow center directions rho hrho) ≠ ⊤ := by
    rw [volume_translatedRadialPolarPieceBelow center hdirections hrho]
    exact radialPolarPieceBelow_volume_ne_top directions hrho
  exact hasFrontFrostmanMeasures_of_positive_finite_volume_subset
    selector
    (translatedRadialPolarPieceBelow center directions rho hrho)
    (measurableSet_translatedRadialPolarPieceBelow center hdirections hrho)
    hpieceFront hpiecePositive hpieceFinite

/-- The reflected translated polar piece models the backward half of a family
of selected segments through a common point. -/
def backwardRadialPolarPieceBelow (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (rho : ℝ) (hrho : 0 < rho) : Set E4 :=
  (fun x : E4 => center + x) ''
    (-radialPolarPieceBelow directions rho hrho)

theorem measurableSet_backwardRadialPolarPieceBelow
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    {rho : ℝ} (hrho : 0 < rho) :
    MeasurableSet
      (backwardRadialPolarPieceBelow center directions rho hrho) := by
  exact (Homeomorph.addLeft center).measurableEmbedding.measurableSet_image'
    (measurableSet_radialPolarPieceBelow hdirections hrho).neg

theorem volume_backwardRadialPolarPieceBelow
    (center : E4) {directions : Set (Metric.sphere (0 : E4) 1)}
    (hdirections : MeasurableSet directions)
    {rho : ℝ} (hrho : 0 < rho) :
    volume (backwardRadialPolarPieceBelow center directions rho hrho) =
      volume (radialPolarPieceBelow directions rho hrho) := by
  let piece := radialPolarPieceBelow directions rho hrho
  have hpiece : MeasurableSet piece :=
    measurableSet_radialPolarPieceBelow hdirections hrho
  have htranslate :
      volume (backwardRadialPolarPieceBelow center directions rho hrho) =
        volume (-piece) := by
    have hpreimage :
        backwardRadialPolarPieceBelow center directions rho hrho =
          (fun x : E4 => -center + x) ⁻¹' (-piece) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [piece] using hy
      · intro hx
        refine ⟨-center + x, hx, ?_⟩
        module
    rw [hpreimage]
    exact (measurePreserving_add_left volume (-center)).measure_preimage
      hpiece.neg.nullMeasurableSet
  rw [htranslate]
  have hneg := (Measure.measurePreserving_neg volume).measure_preimage
    hpiece.nullMeasurableSet
  have hpre : Neg.neg ⁻¹' piece = -piece := by
    ext x
    simp [Set.mem_neg]
  rwa [hpre] at hneg

theorem common_center_backward_direction_bush_at_radius_has_front_frostman
    (selector : Set MarkedLine) (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0)
    {rho : ℝ} (hrho : 0 < rho)
    (hfront : ∀ theta ∈ directions, ∀ radius : ℝ,
      radius ∈ Set.Ioo (0 : ℝ) rho →
        center - radius • (theta : E4) ∈ unitFront selector) :
    HasFrontFrostmanMeasures selector := by
  have hpieceFront :
      backwardRadialPolarPieceBelow center directions rho hrho ⊆
        unitFront selector := by
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_neg] at hy
    obtain ⟨theta, htheta, radius, hradius, hyrepr⟩ :=
      radialPolarPieceBelow_point_representation hrho hy
    have hyneg : y = -(radius • (theta : E4)) := by
      calc
        y = -(-y) := by simp
        _ = -(radius • (theta : E4)) := congrArg Neg.neg hyrepr
    rw [hyneg]
    simpa [sub_eq_add_neg] using hfront theta htheta radius hradius
  have hpiecePositive :
      volume (backwardRadialPolarPieceBelow center directions rho hrho) ≠ 0 := by
    rw [volume_backwardRadialPolarPieceBelow center hdirections hrho]
    exact radialPolarPieceBelow_volume_ne_zero
      hdirections hdirectionsPositive hrho
  have hpieceFinite :
      volume (backwardRadialPolarPieceBelow center directions rho hrho) ≠ ⊤ := by
    rw [volume_backwardRadialPolarPieceBelow center hdirections hrho]
    exact radialPolarPieceBelow_volume_ne_top directions hrho
  exact hasFrontFrostmanMeasures_of_positive_finite_volume_subset
    selector (backwardRadialPolarPieceBelow center directions rho hrho)
    (measurableSet_backwardRadialPolarPieceBelow center hdirections hrho)
    hpieceFront hpiecePositive hpieceFinite

/-- The signed segment parameter of the selected line at a proposed common
physical point. -/
noncomputable def selectorCommonPointParameter
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) (theta : Metric.sphere (0 : E4) 1) : ℝ :=
  let line := selectorLine selector hmeasurable hvalid hselector
    (metricSphereToNormSphere theta)
  inner ℝ (center - offset line) (theta : E4) - mark line

theorem measurable_selectorCommonPointParameter
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) :
    Measurable
      (selectorCommonPointParameter selector hmeasurable hvalid hselector center) := by
  let lineMap : Metric.sphere (0 : E4) 1 → MarkedLine := fun theta =>
    (selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta) : MarkedLine)
  have hlineMap : Measurable lineMap := by
    exact measurable_subtype_coe.comp
      ((measurable_selectorLine selector hmeasurable hvalid hselector).comp
        measurable_metricSphereToNormSphere)
  have hoffset : Measurable (fun theta => offset (lineMap theta)) := by
    change Measurable (fun theta => (lineMap theta).1.2)
    exact measurable_snd.comp (measurable_fst.comp hlineMap)
  have hmark : Measurable (fun theta => mark (lineMap theta)) := by
    change Measurable (fun theta => (lineMap theta).2)
    exact measurable_snd.comp hlineMap
  change Measurable (fun theta =>
    inner ℝ (center - offset (lineMap theta)) (theta : E4) -
      mark (lineMap theta))
  exact ((measurable_const.sub hoffset).inner measurable_subtype_coe).sub hmark

def commonPointForwardDirections
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) : Set (Metric.sphere (0 : E4) 1) :=
  {theta | selectorCommonPointParameter selector hmeasurable hvalid hselector
    center theta ≤ 0}

def commonPointBackwardDirections
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) : Set (Metric.sphere (0 : E4) 1) :=
  {theta | 0 ≤ selectorCommonPointParameter selector hmeasurable hvalid hselector
    center theta}

theorem measurableSet_commonPointForwardDirections
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) :
    MeasurableSet
      (commonPointForwardDirections selector hmeasurable hvalid hselector center) := by
  exact measurableSet_le
    (measurable_selectorCommonPointParameter selector hmeasurable hvalid
      hselector center) measurable_const

theorem measurableSet_commonPointBackwardDirections
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) :
    MeasurableSet
      (commonPointBackwardDirections selector hmeasurable hvalid hselector center) := by
  exact measurableSet_le measurable_const
    (measurable_selectorCommonPointParameter selector hmeasurable hvalid
      hselector center)

theorem commonPoint_forward_or_backward_positive
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) :
    volume.toSphere
        (commonPointForwardDirections selector hmeasurable hvalid hselector center) ≠ 0 ∨
      volume.toSphere
        (commonPointBackwardDirections selector hmeasurable hvalid hselector center) ≠ 0 := by
  by_contra h
  push_neg at h
  have hcover :
      (Set.univ : Set (Metric.sphere (0 : E4) 1)) ⊆
        commonPointForwardDirections selector hmeasurable hvalid hselector center ∪
          commonPointBackwardDirections selector hmeasurable hvalid hselector center := by
    intro theta _
    exact (le_total
      (selectorCommonPointParameter selector hmeasurable hvalid hselector center theta)
      0).elim (fun hle => Or.inl hle) (fun hle => Or.inr hle)
  have hunivZero :
      volume.toSphere (Set.univ : Set (Metric.sphere (0 : E4) 1)) = 0 := by
    apply le_zero_iff.mp
    calc
      volume.toSphere (Set.univ : Set (Metric.sphere (0 : E4) 1)) ≤
          volume.toSphere
            (commonPointForwardDirections selector hmeasurable hvalid hselector center ∪
              commonPointBackwardDirections selector hmeasurable hvalid hselector center) :=
        measure_mono hcover
      _ ≤ volume.toSphere
            (commonPointForwardDirections selector hmeasurable hvalid hselector center) +
          volume.toSphere
            (commonPointBackwardDirections selector hmeasurable hvalid hselector center) :=
        measure_union_le _ _
      _ = 0 := by rw [h.1, h.2, add_zero]
  exact (volume.toSphere_ne_zero :
    (volume.toSphere : Measure (Metric.sphere (0 : E4) 1)) ≠ 0)
    (Measure.measure_univ_eq_zero.mp hunivZero)

/-- If every selected segment passes through one common point, the measurable
sign split of its affine parameter contains a positive-measure half-bush.
Consequently the selector is already in the Frostman alternative. -/
theorem all_direction_common_point_has_front_frostman
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4)
    (hparameter : ∀ theta : Metric.sphere (0 : E4) 1,
      selectorCommonPointParameter selector hmeasurable hvalid hselector center theta ∈
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hcenter : ∀ theta : Metric.sphere (0 : E4) 1,
      center =
        offset (selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)) +
        (mark (selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)) +
          selectorCommonPointParameter selector hmeasurable hvalid hselector center theta) •
        direction (selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta))) :
    HasFrontFrostmanMeasures selector := by
  rcases commonPoint_forward_or_backward_positive selector hmeasurable hvalid
    hselector center with hforward | hbackward
  · apply common_center_direction_bush_at_radius_has_front_frostman
      selector center
      (commonPointForwardDirections selector hmeasurable hvalid hselector center)
      (measurableSet_commonPointForwardDirections selector hmeasurable hvalid
        hselector center)
      hforward (by norm_num : (0 : ℝ) < 1 / 2)
    intro theta htheta radius hradius
    let line := selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
    let parameter := selectorCommonPointParameter selector hmeasurable hvalid
      hselector center theta
    refine ⟨(line : MarkedLine), line.property, parameter + radius, ?_, ?_⟩
    · have hp := hparameter theta
      change parameter ≤ 0 at htheta
      constructor <;> linarith [hp.1, hp.2, hradius.1, hradius.2]
    · have hdir : direction (line : MarkedLine) = (theta : E4) := by
        exact direction_selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)
      change center + radius • (theta : E4) =
        offset (line : MarkedLine) +
          (mark (line : MarkedLine) + (parameter + radius)) •
            direction (line : MarkedLine)
      rw [hcenter theta, hdir]
      module
  · apply common_center_backward_direction_bush_at_radius_has_front_frostman
      selector center
      (commonPointBackwardDirections selector hmeasurable hvalid hselector center)
      (measurableSet_commonPointBackwardDirections selector hmeasurable hvalid
        hselector center)
      hbackward (by norm_num : (0 : ℝ) < 1 / 2)
    intro theta htheta radius hradius
    let line := selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
    let parameter := selectorCommonPointParameter selector hmeasurable hvalid
      hselector center theta
    refine ⟨(line : MarkedLine), line.property, parameter - radius, ?_, ?_⟩
    · have hp := hparameter theta
      change 0 ≤ parameter at htheta
      constructor <;> linarith [hp.1, hp.2, hradius.1, hradius.2]
    · have hdir : direction (line : MarkedLine) = (theta : E4) := by
        exact direction_selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)
      change center - radius • (theta : E4) =
        offset (line : MarkedLine) +
          (mark (line : MarkedLine) + (parameter - radius)) •
            direction (line : MarkedLine)
      rw [hcenter theta, hdir]
      module

/-- Natural common-point interface: every selected marked unit segment passes
through `center`.  The signed parameter is recovered from the inner product,
so no separate parameter function or compatibility equation is assumed. -/
theorem all_selected_segments_through_common_point_have_front_frostman
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4)
    (hcommon : ∀ theta : Metric.sphere (0 : E4) 1,
      ∃ parameter ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        center =
          offset (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) +
          (mark (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) + parameter) •
          direction (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta))) :
    HasFrontFrostmanMeasures selector := by
  have hrecover : ∀ theta : Metric.sphere (0 : E4) 1,
      ∀ parameter : ℝ,
        center =
          offset (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) +
          (mark (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) + parameter) •
          direction (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) →
        selectorCommonPointParameter selector hmeasurable hvalid hselector
          center theta = parameter := by
    intro theta parameter hcenterEq
    let line := selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
    have hdir : direction (line : MarkedLine) = (theta : E4) :=
      direction_selectorLine selector hmeasurable hvalid hselector
        (metricSphereToNormSphere theta)
    have hnorm : ‖(theta : E4)‖ = 1 := by
      exact (metricSphereToNormSphere theta).property
    change inner ℝ (center - offset (line : MarkedLine)) (theta : E4) -
      mark (line : MarkedLine) = parameter
    rw [hcenterEq]
    have hdiff :
        offset (line : MarkedLine) +
            (mark (line : MarkedLine) + parameter) •
              direction (line : MarkedLine) -
          offset (line : MarkedLine) =
        (mark (line : MarkedLine) + parameter) •
          direction (line : MarkedLine) := by
      module
    rw [hdiff]
    rw [inner_smul_left, hdir, real_inner_self_eq_norm_sq, hnorm]
    simp
  apply all_direction_common_point_has_front_frostman selector hmeasurable
    hvalid hselector center
  · intro theta
    obtain ⟨parameter, hparameter, hcenterEq⟩ := hcommon theta
    rw [hrecover theta parameter hcenterEq]
    exact hparameter
  · intro theta
    obtain ⟨parameter, _hparameter, hcenterEq⟩ := hcommon theta
    rw [hrecover theta parameter hcenterEq]
    exact hcenterEq

theorem selectorCommonPointParameter_eq_of_point_eq
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4) (theta : Metric.sphere (0 : E4) 1)
    (parameter : ℝ)
    (hcenterEq : center =
      offset (selectorLine selector hmeasurable hvalid hselector
        (metricSphereToNormSphere theta)) +
      (mark (selectorLine selector hmeasurable hvalid hselector
        (metricSphereToNormSphere theta)) + parameter) •
      direction (selectorLine selector hmeasurable hvalid hselector
        (metricSphereToNormSphere theta))) :
    selectorCommonPointParameter selector hmeasurable hvalid hselector
      center theta = parameter := by
  let line := selectorLine selector hmeasurable hvalid hselector
    (metricSphereToNormSphere theta)
  have hdir : direction (line : MarkedLine) = (theta : E4) :=
    direction_selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
  have hnorm : ‖(theta : E4)‖ = 1 :=
    (metricSphereToNormSphere theta).property
  change inner ℝ (center - offset (line : MarkedLine)) (theta : E4) -
    mark (line : MarkedLine) = parameter
  rw [hcenterEq]
  have hdiff :
      offset (line : MarkedLine) +
          (mark (line : MarkedLine) + parameter) •
            direction (line : MarkedLine) -
        offset (line : MarkedLine) =
      (mark (line : MarkedLine) + parameter) •
        direction (line : MarkedLine) := by
    module
  rw [hdiff, inner_smul_left, hdir, real_inner_self_eq_norm_sq, hnorm]
  simp

/-- The terminal form needed by a fixed-mass concentration limit: it is
enough that a measurable positive surface-measure set of selected directions,
not every direction, passes through one common point.  The sign of the marked
fibre parameter supplies a measurable forward/backward half-bush split. -/
theorem positive_direction_selected_segments_through_common_point_have_front_frostman
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (center : E4)
    (directions : Set (Metric.sphere (0 : E4) 1))
    (hdirections : MeasurableSet directions)
    (hdirectionsPositive : volume.toSphere directions ≠ 0)
    (hcommon : ∀ theta ∈ directions,
      ∃ parameter ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
        center =
          offset (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) +
          (mark (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta)) + parameter) •
          direction (selectorLine selector hmeasurable hvalid hselector
            (metricSphereToNormSphere theta))) :
    HasFrontFrostmanMeasures selector := by
  let forward : Set (Metric.sphere (0 : E4) 1) :=
    directions ∩
      commonPointForwardDirections selector hmeasurable hvalid hselector center
  let backward : Set (Metric.sphere (0 : E4) 1) :=
    directions ∩
      commonPointBackwardDirections selector hmeasurable hvalid hselector center
  have hforwardMeasurable : MeasurableSet forward := by
    exact hdirections.inter
      (measurableSet_commonPointForwardDirections selector hmeasurable hvalid
        hselector center)
  have hbackwardMeasurable : MeasurableSet backward := by
    exact hdirections.inter
      (measurableSet_commonPointBackwardDirections selector hmeasurable hvalid
        hselector center)
  have hpositive :
      volume.toSphere forward ≠ 0 ∨ volume.toSphere backward ≠ 0 := by
    by_contra hnot
    push Not at hnot
    have hcover : directions ⊆ forward ∪ backward := by
      intro theta htheta
      exact (le_total
        (selectorCommonPointParameter selector hmeasurable hvalid hselector
          center theta) 0).elim
        (fun hle => Or.inl ⟨htheta, hle⟩)
        (fun hle => Or.inr ⟨htheta, hle⟩)
    apply hdirectionsPositive
    apply le_zero_iff.mp
    calc
      volume.toSphere directions ≤ volume.toSphere (forward ∪ backward) :=
        measure_mono hcover
      _ ≤ volume.toSphere forward + volume.toSphere backward :=
        measure_union_le _ _
      _ = 0 := by rw [hnot.1, hnot.2, add_zero]
  rcases hpositive with hforwardPositive | hbackwardPositive
  · apply common_center_direction_bush_at_radius_has_front_frostman
      selector center forward hforwardMeasurable hforwardPositive
      (by norm_num : (0 : ℝ) < 1 / 2)
    intro theta htheta radius hradius
    obtain ⟨parameter, hparameter, hcenterEq⟩ := hcommon theta htheta.1
    let line := selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
    have hparameterEq :
        selectorCommonPointParameter selector hmeasurable hvalid hselector
          center theta = parameter :=
      selectorCommonPointParameter_eq_of_point_eq selector hmeasurable hvalid
        hselector center theta parameter hcenterEq
    have hparameterNonpos : parameter ≤ 0 := by
      have hsigned := htheta.2
      change selectorCommonPointParameter selector hmeasurable hvalid hselector
        center theta ≤ 0 at hsigned
      rwa [hparameterEq] at hsigned
    refine ⟨(line : MarkedLine), line.property, parameter + radius, ?_, ?_⟩
    · constructor <;> linarith [hparameter.1, hparameter.2,
        hradius.1, hradius.2]
    · have hdir : direction (line : MarkedLine) = (theta : E4) :=
        direction_selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)
      change center + radius • (theta : E4) =
        offset (line : MarkedLine) +
          (mark (line : MarkedLine) + (parameter + radius)) •
            direction (line : MarkedLine)
      rw [hcenterEq, hdir]
      module
  · apply common_center_backward_direction_bush_at_radius_has_front_frostman
      selector center backward hbackwardMeasurable hbackwardPositive
      (by norm_num : (0 : ℝ) < 1 / 2)
    intro theta htheta radius hradius
    obtain ⟨parameter, hparameter, hcenterEq⟩ := hcommon theta htheta.1
    let line := selectorLine selector hmeasurable hvalid hselector
      (metricSphereToNormSphere theta)
    have hparameterEq :
        selectorCommonPointParameter selector hmeasurable hvalid hselector
          center theta = parameter :=
      selectorCommonPointParameter_eq_of_point_eq selector hmeasurable hvalid
        hselector center theta parameter hcenterEq
    have hparameterNonneg : 0 ≤ parameter := by
      have hsigned := htheta.2
      change 0 ≤ selectorCommonPointParameter selector hmeasurable hvalid
        hselector center theta at hsigned
      rwa [hparameterEq] at hsigned
    refine ⟨(line : MarkedLine), line.property, parameter - radius, ?_, ?_⟩
    · constructor <;> linarith [hparameter.1, hparameter.2,
        hradius.1, hradius.2]
    · have hdir : direction (line : MarkedLine) = (theta : E4) :=
        direction_selectorLine selector hmeasurable hvalid hselector
          (metricSphereToNormSphere theta)
      change center - radius • (theta : E4) =
        offset (line : MarkedLine) +
          (mark (line : MarkedLine) + (parameter - radius)) •
            direction (line : MarkedLine)
      rw [hcenterEq, hdir]
      module

theorem radialMarkedLine_valid (theta : Metric.sphere (0 : E4) 1) :
    IsValidLine (radialMarkedLine theta) := by
  constructor
  · change ‖(theta : E4)‖ = 1
    simpa [Metric.mem_sphere, dist_zero_right] using theta.property
  · change inner ℝ (0 : E4) (theta : E4) = 0
    simp

/-- The polar cone over a spherical cap lies in the physical tube around the
corresponding radial marked segment.  This is the geometric bridge from the
four-dimensional tube estimate to the cubic direction-cap estimate. -/
theorem radialCone_subset_markedUnitTube
    (theta : Metric.sphere (0 : E4) 1) {r : ℝ} (hr : 0 < r) :
    Set.Ioo (0 : ℝ) 1 •
        ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) ''
          (Metric.ball theta r)) ⊆
      markedUnitTube (radialMarkedLine theta) r := by
  intro x hx
  rcases hx with ⟨a, ha, y, ⟨u, hu, rfl⟩, rfl⟩
  change dist (u : E4) (theta : E4) < r at hu
  let t : ℝ := a - 1 / 2
  have ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    dsimp [t]
    constructor <;> linarith [ha.1, ha.2]
  have hfront := rawFrontParam_mem_unitFront_singleton
    (radialMarkedLine theta) ht
  apply (Metric.infDist_le_dist_of_mem hfront).trans
  have hscaled : a * dist (u : E4) (theta : E4) < r := by
    calc
      a * dist (u : E4) (theta : E4) ≤
          1 * dist (u : E4) (theta : E4) :=
        mul_le_mul_of_nonneg_right ha.2.le dist_nonneg
      _ < r := by simpa using hu
  have hparam :
      rawFrontParam (radialMarkedLine theta, t) = a • (theta : E4) := by
    change (0 : E4) + ((1 / 2 : ℝ) + (a - 1 / 2)) • (theta : E4) =
      a • (theta : E4)
    rw [zero_add]
    congr 1
    ring
  rw [hparam, dist_eq_norm]
  have hdiff : a • (u : E4) - a • (theta : E4) =
      a • ((u : E4) - (theta : E4)) := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ha.1]
  simpa [dist_eq_norm] using hscaled.le

/-- Unnormalized rotation-invariant surface measure of a radius-`r` cap is
bounded by an explicit constant times `r^3`.  The proof is the polar formula,
the radial-cone inclusion above, and the actual marked-tube upper bound. -/
theorem toSphere_ball_upper_bound
    (theta : Metric.sphere (0 : E4) 1) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    volume.toSphere (Metric.ball theta r) ≤
      128 * (ENNReal.ofReal r) ^ 3 *
        ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [volume.toSphere_apply' measurableSet_ball]
  have hcone :
      volume (Set.Ioo (0 : ℝ) 1 •
        ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) ''
          (Metric.ball theta r))) ≤
        volume (markedUnitTube (radialMarkedLine theta) r) :=
    measure_mono (radialCone_subset_markedUnitTube theta hr)
  have htube := volume_markedUnitTube_upper_bound
    (radialMarkedLine_valid theta) hr hrone
  calc
    (Module.finrank ℝ E4 : ENNReal) *
          volume (Set.Ioo (0 : ℝ) 1 •
            ((fun z : Metric.sphere (0 : E4) 1 => (z : E4)) ''
              (Metric.ball theta r))) ≤
        (Module.finrank ℝ E4 : ENNReal) *
          volume (markedUnitTube (radialMarkedLine theta) r) :=
      by simpa [mul_comm] using
        (mul_le_mul_right hcone (Module.finrank ℝ E4 : ENNReal))
    _ ≤ (Module.finrank ℝ E4 : ENNReal) *
          (32 * (ENNReal.ofReal r) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) :=
      by simpa [mul_comm] using
        (mul_le_mul_right htube (Module.finrank ℝ E4 : ENNReal))
    _ = 128 * (ENNReal.ofReal r) ^ 3 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) := by
      norm_num
      ring

/-- A fixed finite constant for the normalized metric-sphere probability.
Writing the normalization factor explicitly keeps the statement independent
of any separate closed formula for the total surface area. -/
noncomputable def metricSphereCapConstant : ENNReal :=
  (↑(metricSphereFiniteMeasure.mass⁻¹) : ENNReal) *
    128 * ENNReal.ofReal (Real.pi ^ 2 / 2)

theorem metricSphereCapConstant_ne_top : metricSphereCapConstant ≠ ⊤ := by
  unfold metricSphereCapConstant
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num))
    ENNReal.ofReal_ne_top

theorem metricSphereCapConstant_ne_zero : metricSphereCapConstant ≠ 0 := by
  have hmass : 0 < metricSphereFiniteMeasure.mass :=
    pos_iff_ne_zero.mpr
      (metricSphereFiniteMeasure.mass_nonzero_iff.mpr
        metricSphereFiniteMeasure_ne_zero)
  have hinv : 0 < metricSphereFiniteMeasure.mass⁻¹ := inv_pos.mpr hmass
  have hpi : 0 < Real.pi ^ 2 / 2 := by positivity
  exact ne_of_gt (by
    unfold metricSphereCapConstant
    positivity)

/-- Cubic upper mass bound for caps under the normalized metric-sphere
probability. -/
theorem metricSphereProbability_ball_upper_bound
    (theta : Metric.sphere (0 : E4) 1) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    (metricSphereProbability :
      Measure (Metric.sphere (0 : E4) 1)) (Metric.ball theta r) ≤
      metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
  let m : FiniteMeasure (Metric.sphere (0 : E4) 1) :=
    metricSphereFiniteMeasure
  have hm : m ≠ 0 := by
    intro hzero
    have hmeasure := congrArg
      (fun q : FiniteMeasure (Metric.sphere (0 : E4) 1) =>
        (q : Measure (Metric.sphere (0 : E4) 1))) hzero
    have hv : volume.toSphere ≠
        (0 : Measure (Metric.sphere (0 : E4) 1)) :=
      volume.toSphere_ne_zero
    change volume.toSphere =
      (0 : Measure (Metric.sphere (0 : E4) 1)) at hmeasure
    exact hv hmeasure
  change (m.normalize : Measure (Metric.sphere (0 : E4) 1))
      (Metric.ball theta r) ≤
    metricSphereCapConstant * (ENNReal.ofReal r) ^ 3
  rw [m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
  have hcap := toSphere_ball_upper_bound theta hr hrone
  calc
    (↑m.mass⁻¹ : ENNReal) * volume.toSphere (Metric.ball theta r) ≤
        (↑m.mass⁻¹ : ENNReal) *
          (128 * (ENNReal.ofReal r) ^ 3 *
            ENNReal.ofReal (Real.pi ^ 2 / 2)) := by
      simpa [mul_comm] using
        (mul_le_mul_right hcap (↑m.mass⁻¹ : ENNReal))
    _ = metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
      simp only [metricSphereCapConstant, m]
      ring

theorem metricSphereToNormSphere_preimage_ball
    (theta : {theta : E4 // ‖theta‖ = 1}) (r : ℝ) :
    metricSphereToNormSphere ⁻¹' Metric.ball theta r =
      Metric.ball (normSphereToMetricSphere theta) r := by
  ext x
  change dist (x : E4) (theta : E4) < r ↔
    dist (x : E4) (theta : E4) < r
  rfl

/-- The same cubic cap estimate on the norm-one direction subtype used by
the selector and carrier parametrizations. -/
theorem normSphereProbability_ball_upper_bound
    (theta : {theta : E4 // ‖theta‖ = 1}) {r : ℝ}
    (hr : 0 < r) (hrone : r ≤ 1) :
    (normSphereProbability : Measure {theta : E4 // ‖theta‖ = 1})
        (Metric.ball theta r) ≤
      metricSphereCapConstant * (ENNReal.ofReal r) ^ 3 := by
  rw [normSphereProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_metricSphereToNormSphere
    Metric.isOpen_ball.measurableSet]
  rw [metricSphereToNormSphere_preimage_ball]
  exact metricSphereProbability_ball_upper_bound
    (normSphereToMetricSphere theta) hr hrone

/-- Ambient thickening of a finite set of directions.  This is the
four-dimensional object used for the sharp codimension-one packing count:
the centers lie on the unit sphere, while the balls themselves live in
`E4`. -/
def finiteDirectionBallUnion {alpha : Type*} (s : Finset alpha)
    (center : alpha → E4) (radius : ℝ) : Set E4 :=
  ⋃ a ∈ s, Metric.ball (center a) radius

/-- Exact finite packing identity for separated ambient balls.  The proof
keeps the whole four-dimensional ball volume instead of replacing it by a
weak spherical-cap estimate. -/
theorem volume_finiteDirectionBallUnion_of_separated
    {alpha : Type*} (s : Finset alpha) (center : alpha → E4)
    {radius : ℝ}
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      2 * radius ≤ dist (center a) (center b)) :
    volume (finiteDirectionBallUnion s center radius) =
      (s.card : ENNReal) * volume (Metric.ball (0 : E4) radius) := by
  classical
  have hdisjoint : Set.Pairwise (s : Set alpha)
      (Disjoint on fun a => Metric.ball (center a) radius) := by
    rintro a ha b hb hab
    apply Metric.ball_disjoint_ball
    simpa [two_mul] using hsep a ha b hb hab
  change volume (⋃ a ∈ s, Metric.ball (center a) radius) = _
  rw [measure_biUnion_finset hdisjoint
    (fun _ _ => measurableSet_ball)]
  have hball : ∀ a : alpha,
      volume (Metric.ball (center a) radius) =
        volume (Metric.ball (0 : E4) radius) := by
    intro a
    rw [InnerProductSpace.volume_ball, InnerProductSpace.volume_ball]
  simp_rw [hball]
  simp

/-- Four-dimensional scaling of the packing ball.  Leaving the fixed
positive half-unit-ball volume unexpanded is cleaner than introducing a
separate numerical surface-area normalization. -/
theorem volume_ball_zero_half_scale {delta : ℝ} (hdelta : 0 < delta) :
    volume (Metric.ball (0 : E4) (delta / 2)) =
      (ENNReal.ofReal delta) ^ 4 *
        volume (Metric.ball (0 : E4) (1 / 2)) := by
  rw [InnerProductSpace.volume_ball (0 : E4) (delta / 2),
    InnerProductSpace.volume_ball (0 : E4) (1 / 2)]
  simp only [show Module.finrank ℝ E4 = 4 by simp]
  rw [show delta / 2 = delta * (1 / 2 : ℝ) by ring]
  rw [ENNReal.ofReal_mul hdelta.le]
  rw [mul_pow]
  ring

end StickyKakeya4
