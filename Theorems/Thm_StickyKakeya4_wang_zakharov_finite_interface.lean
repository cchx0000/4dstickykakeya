import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_compact_front
import Theorems.Thm_StickyKakeya4_selector_covering_lower_bound
import Theorems.Thm_StickyKakeya4_wz_common_slab

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-!
The exact finite-scale interface used from Wang--Zakharov.

This file deliberately contains no qualitative Hausdorff-dimension
conclusion.  It describes only a finite family of marked unit tubes at one
dyadic scale, the almost-AD, convex-Wolff, and cubical-density hypotheses,
and the resulting covering-number lower bound for its shaded union.
-/

/-- A half-open axis-parallel cell of side length `delta`. -/
def wzDyadicCell (delta : ℝ) (k : Fin 4 → ℤ) : Set E4 :=
  {x | ∀ j, (k j : ℝ) * delta ≤ x j ∧
    x j < ((k j : ℝ) + 1) * delta}

/-- A shading at scale `delta` is a finite union of scale-`delta` cells. -/
def IsWZCubicalShading (delta : ℝ) (s : Set E4) : Prop :=
  ∃ cells : Finset (Fin 4 → ℤ),
    s = ⋃ k ∈ (cells : Set (Fin 4 → ℤ)), wzDyadicCell delta k

/-- The scales appearing in the finite theorem are dyadic. -/
def IsWZDyadicScale (delta : ℝ) : Prop :=
  ∃ level : ℕ, delta = (2 : ℝ)⁻¹ ^ level

/-- The finite Wang--Zakharov estimate is insensitive to a fixed change of
scale between the physical tube thickness and the cubical mesh.  Keeping the
two scales separate is essential: in four dimensions a side-`delta` cube
meeting a central segment is contained in its `2 * delta`-tube, but need not
be contained in the `delta`-tube.  The factor two is fixed once and for all. -/
def IsWZComparableCubicalShading (tubeDelta : ℝ) (s : Set E4) : Prop :=
  ∃ cellDelta : ℝ,
    0 < cellDelta ∧ cellDelta ≤ tubeDelta ∧ tubeDelta ≤ 2 * cellDelta ∧
      IsWZDyadicScale cellDelta ∧ IsWZCubicalShading cellDelta s

def wzCarrierPoint {n : ℕ} (D : FiniteScaleSource n) (i : Fin n) :
    E4 × E4 :=
  (direction (D.line i), offset (D.line i))

/-- Number of tube parameters within carrier distance `radius` of tube `i`. -/
def wzCarrierBallCount {n : ℕ} (D : FiniteScaleSource n)
    (i : Fin n) (radius : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j =>
    dist (wzCarrierPoint D j) (wzCarrierPoint D i) ≤ radius).card

/-- Number of full tubes from `D` contained in a physical set `U`. -/
def wzContainedTubeCount {n : ℕ} (D : FiniteScaleSource n)
    (U : Set E4) : ℕ := by
  classical
  exact (Finset.univ.filter fun i =>
    markedUnitTube (D.line i) D.thickness ⊆ U).card

def wzTotalTubeVolume {n : ℕ} (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, volume (markedUnitTube (D.line i) D.thickness)

def wzTotalShadingVolume {n : ℕ} (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, volume (D.shading i)

/-- The three hypotheses of the four-dimensional finite WZ theorem, in the
normalization used by the manuscript.  The affine mark is retained in every
tube.  The common exponent `eta` controls all three allowed losses. -/
def IsWangZakharovFiniteInput {n : ℕ}
    (D : FiniteScaleSource n) (eta : ℝ) : Prop :=
  0 < n ∧
  0 < D.thickness ∧ D.thickness ≤ 1 ∧
  IsWZDyadicScale D.thickness ∧
  (∀ i, IsValidLine (D.line i)) ∧
  (∀ i, D.weight i = 1) ∧
  (∀ i, MeasurableSet (D.shading i)) ∧
  (∀ i, IsWZComparableCubicalShading D.thickness (D.shading i)) ∧
  (∀ i, D.shading i ⊆ markedUnitTube (D.line i) D.thickness) ∧
  (∀ i j, i ≠ j →
    D.thickness ≤ dist (direction (D.line i)) (direction (D.line j))) ∧
  (∀ i radius, D.thickness ≤ radius → radius ≤ 1 →
    (ENNReal.ofReal D.thickness).rpow eta *
          (ENNReal.ofReal (radius / D.thickness)) ^ 3 ≤
        (wzCarrierBallCount D i radius : ENNReal) ∧
      (wzCarrierBallCount D i radius : ENNReal) ≤
        (ENNReal.ofReal D.thickness).rpow (-eta) *
          (ENNReal.ofReal (radius / D.thickness)) ^ 3) ∧
  (∀ U : Set E4, Convex ℝ U →
    (wzContainedTubeCount D U : ENNReal) ≤
      (ENNReal.ofReal D.thickness).rpow (-eta) *
        volume U * n) ∧
  (ENNReal.ofReal D.thickness).rpow eta * wzTotalTubeVolume D ≤
    wzTotalShadingVolume D

/-- Literal input to the published graph-tube theorem.  In addition to the
combinatorial/measure hypotheses above, all marked segments must admit one
fixed-size common graph slab in one uniformly nonvertical chart, and their
full unit segments must remain in one fixed-height window. -/
def IsWangZakharovNativeFiniteInput {n : ℕ}
    (D : FiniteScaleSource n) (eta : ℝ) : Prop :=
  IsWangZakharovFiniteInput D eta ∧
    HasNormalizedWZGraphSlab D ∧
    HasFixedWZGraphNormalization D

/-- The published finite theorem, separated from every compact-selection and
Hausdorff-cover readback step.  A proof of the manuscript's qualitative
closure may use this proposition as its sole WZ input. -/
def HasWangZakharovFiniteEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
    ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ deltaZero →
      IsWangZakharovNativeFiniteInput D eta →
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow (-4 + epsilon) ≤
        coveringNumber (sourceUnion D) D.thickness

/-- The published Wang--Zakharov conclusion in its native four-dimensional
volume normalization.  Fixed chart, tube-length, and Euclidean-ball constants
are represented by `A`; the exponent and all three finite hypotheses are
unchanged. -/
def HasWangZakharovFiniteVolumeEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ deltaZero : ℝ, 0 < deltaZero ∧
    ∀ (n : ℕ) (D : FiniteScaleSource n),
      D.thickness ≤ deltaZero →
      IsWangZakharovNativeFiniteInput D eta →
      A⁻¹ * (ENNReal.ofReal D.thickness).rpow epsilon ≤
        volume (sourceUnion D)

/-- In four dimensions, volume divided by the volume of a radius-`2r` ball
is a lower bound for the radius-`r` covering number. -/
theorem volume_div_twoBall_le_coveringNumber (s : Set E4) {r : ℝ}
    (hr : 0 < r) :
    volume s / volume (Metric.ball (0 : E4) (2 * r)) ≤
      coveringNumber s r := by
  apply measure_div_ballBound_le_coveringNumber volume s hr
  · rw [volume_ball_E4]
    positivity
  · rw [volume_ball_E4]
    finiteness
  · intro x hx
    rw [volume_ball_E4 x, volume_ball_E4 (0 : E4)]

/-- The native volume theorem implies the covering-number interface used by
the cover-adapted Hausdorff contradiction.  This is the complete fixed-factor
normalization: the radius-doubling ball contributes only one finite positive
four-dimensional constant. -/
theorem wang_zakharov_volume_estimate_to_covering
    (hWZ : HasWangZakharovFiniteVolumeEstimate) :
    HasWangZakharovFiniteEstimate := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, A, hA0, hATop, deltaZero, hdeltaZero, hvolume⟩ :=
    hWZ epsilon hepsilon
  let Cball : ENNReal :=
    16 * ENNReal.ofReal (Real.pi ^ 2 / 2)
  let Acover : ENNReal := A * Cball
  have hCball0 : Cball ≠ 0 := by
    dsimp [Cball]
    positivity
  have hCballTop : Cball ≠ ⊤ := by
    dsimp [Cball]
    finiteness
  have hAcover0 : Acover ≠ 0 := mul_ne_zero hA0 hCball0
  have hAcoverTop : Acover ≠ ⊤ :=
    ENNReal.mul_ne_top hATop hCballTop
  refine ⟨eta, heta, Acover, hAcover0, hAcoverTop,
    deltaZero, hdeltaZero, ?_⟩
  intro n D hsmall hinput
  have hdelta : 0 < D.thickness := hinput.1.2.1
  let e : ENNReal := ENNReal.ofReal D.thickness
  have he0 : e ≠ 0 := by
    dsimp [e]
    positivity
  have heTop : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.ofReal_ne_top
  have hball : volume (Metric.ball (0 : E4) (2 * D.thickness)) =
      Cball * e ^ 4 := by
    rw [volume_ball_E4]
    have htwo : ENNReal.ofReal (2 * D.thickness) = 2 * e := by
      dsimp [e]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [htwo]
    dsimp [Cball]
    ring
  have hcover :=
    volume_div_twoBall_le_coveringNumber (sourceUnion D) hdelta
  rw [hball] at hcover
  have hvolume' : A⁻¹ * e.rpow epsilon ≤ volume (sourceUnion D) := by
    simpa [e] using hvolume n D hsmall hinput
  have hquotient :
      (A⁻¹ * e.rpow epsilon) / (Cball * e ^ 4) ≤
        coveringNumber (sourceUnion D) D.thickness :=
    (ENNReal.div_le_div_right hvolume' (Cball * e ^ 4)).trans hcover
  have hpower :
      e.rpow (-4 + epsilon) = e.rpow epsilon * (e ^ 4)⁻¹ := by
    calc
      e.rpow (-4 + epsilon) = e.rpow (epsilon + (-4)) := by ring_nf
      _ = e.rpow epsilon * e.rpow (-4) :=
        ENNReal.rpow_add epsilon (-4) he0 heTop
      _ = e.rpow epsilon * (e.rpow 4)⁻¹ := by
        congr 1
        exact ENNReal.rpow_neg e 4
      _ = e.rpow epsilon * (e ^ 4)⁻¹ := by
        congr 1
        exact congrArg Inv.inv (ENNReal.rpow_natCast e 4)
  have hcoeff :
      Acover⁻¹ * e.rpow (-4 + epsilon) =
        (A⁻¹ * e.rpow epsilon) / (Cball * e ^ 4) := by
    rw [hpower]
    dsimp [Acover]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hATop)]
    rw [div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hCball0) (Or.inl hCballTop)]
    ring
  rw [hcoeff]
  exact hquotient

/-- For the unweighted sources used by the finite WZ theorem, the support of
the source function is exactly the geometric union of its shadings.  This is
the readback needed to compare the WZ covering lower bound with a Hausdorff
cover of the physical front. -/
theorem sourceUnion_eq_iUnion_shading_of_weights_one
    {n : ℕ} (D : FiniteScaleSource n)
    (hw : ∀ i, D.weight i = 1) :
    sourceUnion D = ⋃ i, D.shading i := by
  classical
  ext x
  simp [sourceUnion, sourceFunction, hw]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

end StickyKakeya4
