import Theorems.Thm_StickyKakeya4_literal_affine_fiber_coordinates
import Theorems.Thm_StickyKakeya4_real_scalar_ad_interpolation

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace NativeAmbientADGeometry

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment FractionalFiberAlignment
open LiteralAffineFiberCoordinates NormalizedQuantizedPatches RealScalarADInterpolation

noncomputable section
attribute [local instance] Classical.propDecidable

def rawPoint (k : Vertex) : Plane := ![(k.1 : ℝ), (k.2 0 : ℝ)]

lemma rawPoint_injective : Function.Injective rawPoint := by
  intro k l he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change (k.1 : ℝ) = (l.1 : ℝ) at h0
  change (k.2 0 : ℝ) = (l.2 0 : ℝ) at h1
  have hx : k.1 = l.1 := by exact_mod_cast h0
  have hy : k.2 = l.2 := by
    funext i
    fin_cases i
    exact_mod_cast h1
  exact Prod.ext hx hy

lemma rawPoint_close_iff (k l : Vertex) (R : ℕ) :
    dist (rawPoint k) (rawPoint l) ≤ (R : ℝ) ↔
      |k.1 - l.1| ≤ (R : ℤ) ∧ normalClose R k.2 l.2 := by
  constructor
  · intro h
    have hx := (dist_le_pi_dist (rawPoint k) (rawPoint l) 0).trans h
    have hy := (dist_le_pi_dist (rawPoint k) (rawPoint l) 1).trans h
    change |(k.1 : ℝ) - (l.1 : ℝ)| ≤ (R : ℝ) at hx
    change |(k.2 0 : ℝ) - (l.2 0 : ℝ)| ≤ (R : ℝ) at hy
    constructor
    · exact_mod_cast hx
    · intro i
      fin_cases i
      exact_mod_cast hy
  · rintro ⟨hx, hy⟩
    apply (dist_pi_le_iff (Nat.cast_nonneg R : (0 : ℝ) ≤ R)).mpr
    intro i
    fin_cases i
    · change |(k.1 : ℝ) - (l.1 : ℝ)| ≤ (R : ℝ)
      exact_mod_cast hx
    · change |(k.2 0 : ℝ) - (l.2 0 : ℝ)| ≤ (R : ℝ)
      exact_mod_cast hy 0

def actualPoint (μ angle L : ℝ) (c : Plane) (k : Vertex) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanAlignmentPatches.euclidean (affine c L (realized μ angle k))

lemma actualPoint_injective (μ angle L : ℝ) (c : Plane) (hμ : 0 < μ) (hL : 0 < L) :
    Function.Injective (actualPoint μ angle L c) := by
  intro k l he
  have he' : affine c L (realized μ angle k) = affine c L (realized μ angle l) :=
    WithLp.toLp_injective 2 he
  rw [actual_affine_graph, actual_affine_graph] at he'
  have hx := congrFun he' 0
  have hy := congrFun he' 1
  change timeCoord μ (c 0) L k.1 = timeCoord μ (c 0) L l.1 at hx
  change angle * timeCoord μ (c 0) L k.1 + normalCoord μ angle L c k.2 =
    angle * timeCoord μ (c 0) L l.1 + normalCoord μ angle L c l.2 at hy
  rw [hx] at hy
  exact Prod.ext (timeCoord_injective μ _ L hμ hL hx)
    (normalCoord_injective μ angle L c hμ hL (add_left_cancel hy))

lemma image_ball_card {X : Type*} [PseudoMetricSpace X] (P : Finset Vertex)
    (f : Vertex → X) (hf : Function.Injective f) (p : Vertex) (r : ℝ) :
    ballCount (P.image f) (f p) r = ((P.filter (fun k => dist (f k) (f p) ≤ r)).card : ℝ) := by
  classical
  unfold ballCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ hf]

lemma rawPoint_ball_card (P : Finset Vertex) (p : Vertex) (R : ℕ) :
    ballCount (P.image rawPoint) (rawPoint p) (R : ℝ) = ((spatialBall P R p).card : ℝ) := by
  classical
  unfold ballCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ rawPoint_injective]
  congr 2
  ext k
  simp only [Finset.mem_filter, spatialBall, rawPoint_close_iff]

/-- Bounded shear followed by normalization is 4μ/L-Lipschitz from the raw
integer sup metric to the genuine Euclidean metric. -/
theorem raw_close_imp_actual_close (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (hangle : |angle| ≤ 1)
    {k l : Vertex} {R : ℝ} (hR : 0 ≤ R) (hclose : dist (rawPoint k) (rawPoint l) ≤ R) :
    dist (actualPoint μ angle L c k) (actualPoint μ angle L c l) ≤ 4 * (μ / L) * R := by
  have hx : |(k.1 : ℝ) - (l.1 : ℝ)| ≤ R := by
    simpa [rawPoint, Real.dist_eq] using (dist_le_pi_dist (rawPoint k) (rawPoint l) 0).trans hclose
  have hy : |(k.2 0 : ℝ) - (l.2 0 : ℝ)| ≤ R := by
    simpa [rawPoint, Real.dist_eq] using (dist_le_pi_dist (rawPoint k) (rawPoint l) 1).trans hclose
  have htime : |μ * ((k.1 : ℝ) - (l.1 : ℝ))| ≤ μ * R := by
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hx hμ.le
  have hnormal : |μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ))| ≤ μ * R := by
    rw [abs_mul, abs_of_pos hμ]
    exact mul_le_mul_of_nonneg_left hy hμ.le
  have hslope : |angle * (μ * ((k.1 : ℝ) - (l.1 : ℝ)))| ≤ μ * R := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hangle htime (abs_nonneg _) zero_le_one
  have hcoords : ∀ i, |realized μ angle k i - realized μ angle l i| ≤ 2 * μ * R := by
    intro i
    fin_cases i
    · change |μ * (k.1 : ℝ) - μ * (l.1 : ℝ)| ≤ _
      rw [← mul_sub]
      nlinarith only [htime, mul_nonneg hμ.le hR]
    · change |(μ * (k.2 0 : ℝ) + angle * (μ * (k.1 : ℝ))) -
        (μ * (l.2 0 : ℝ) + angle * (μ * (l.1 : ℝ)))| ≤ _
      have he : (μ * (k.2 0 : ℝ) + angle * (μ * (k.1 : ℝ))) -
          (μ * (l.2 0 : ℝ) + angle * (μ * (l.1 : ℝ))) =
          μ * ((k.2 0 : ℝ) - (l.2 0 : ℝ)) + angle * (μ * ((k.1 : ℝ) - (l.1 : ℝ))) := by ring
      rw [he]
      exact (abs_add_le _ _).trans (by linarith only [hnormal, hslope])
  have he := EuclideanAlignmentPatches.euclidean_dist_le_card_mul (realized μ angle k) (realized μ angle l)
    (2 * μ * R) (by positivity) hcoords
  change dist (EuclideanAlignmentPatches.euclidean (affine c L (realized μ angle k)))
    (EuclideanAlignmentPatches.euclidean (affine c L (realized μ angle l))) ≤ _
  rw [affine_euclidean_dist c hL]
  have hh := div_le_div_of_nonneg_right he hL.le
  have hright : ((2 : ℝ) * (2 * μ * R)) / L = 4 * (μ / L) * R := by ring
  simpa only [Nat.cast_ofNat, hright] using hh

theorem actual_close_imp_raw_close (μ angle L : ℝ) (c : Plane)
    (hμ : 0 < μ) (hL : 0 < L) (hangle : |angle| ≤ 1)
    {k l : Vertex} {r : ℝ} (hr : 0 ≤ r)
    (hclose : dist (actualPoint μ angle L c k) (actualPoint μ angle L c l) ≤ r) :
    dist (rawPoint k) (rawPoint l) ≤ (2 * L / μ) * r := by
  change dist (EuclideanAlignmentPatches.euclidean (affine c L (realized μ angle k)))
    (EuclideanAlignmentPatches.euclidean (affine c L (realized μ angle l))) ≤ r at hclose
  rw [affine_euclidean_dist c hL] at hclose
  have heuc := (div_le_iff₀ hL).mp hclose
  have hsup := (EuclideanAlignmentPatches.sup_dist_le (realized μ angle k) (realized μ angle l)).trans heuc
  have hc := realized_coordinate_bounds μ angle hμ hangle k l (r * L) hsup
  apply (dist_pi_le_iff (by positivity : 0 ≤ (2 * L / μ) * r)).mpr
  intro i
  have hbound : (2 * L / μ) * r = (2 * (r * L)) / μ := by ring
  rw [hbound]
  apply (le_div_iff₀ hμ).mpr
  fin_cases i
  · change |(k.1 : ℝ) - (l.1 : ℝ)| * μ ≤ _
    have hh : μ * |(k.1 : ℝ) - (l.1 : ℝ)| ≤ r * L := by exact_mod_cast hc.1
    nlinarith only [hh, mul_nonneg hr hL.le]
  · change |(k.2 0 : ℝ) - (l.2 0 : ℝ)| * μ ≤ _
    have hh : μ * |(k.2 0 : ℝ) - (l.2 0 : ℝ)| ≤ 2 * (r * L) := by exact_mod_cast hc.2
    nlinarith only [hh]

end
end NativeAmbientADGeometry
