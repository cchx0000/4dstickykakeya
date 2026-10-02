import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A global bound for terminal old-edge occurrences

This is a measure-level replacement for the disputed per-node marginal-product
bound in Proposition 9.29, equation (453), of the original manuscript.

The hypotheses retain the original ordered endpoint pair. Terminal measures
must sum to a submeasure of a single root occurrence; equality or inequality
of total masses alone does not suffice. Each counted terminal occurrence must
be supported in a common direction-distance band. No bounded overlap of the
terminal caps, and no domination by an occurrence's own source marginal times
the base direction measure, is assumed.

The geometric construction of the terminal restrictions, their endpoint
support, and the density bound for the original selector remain application
obligations. None of these lemmas asserts the final sticky Kakeya theorem.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StickyKakeya4.GlobalTerminalBand

variable {X D I : Type*} [MeasurableSpace X]

/-- Genuine disjoint restrictions of one occurrence measure have the required
measure-valued budget. This is stronger than a budget for total masses. -/
theorem sum_le_of_disjoint_restrictions [Countable I]
    (root : Measure X) (terminal : I → Measure X) (pieces : I → Set X)
    (hpieces : ∀ i, MeasurableSet (pieces i))
    (hdisjoint : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hterminal : ∀ i, terminal i ≤ root.restrict (pieces i)) :
    Measure.sum terminal ≤ root := by
  have hsum : Measure.sum terminal ≤ Measure.sum (fun i => root.restrict (pieces i)) := by
    apply Measure.le_iff.mpr
    intro s hs
    simp only [Measure.sum_apply _ hs]
    exact ENNReal.tsum_le_tsum (fun i => hterminal i s)
  rw [← Measure.restrict_iUnion hdisjoint hpieces] at hsum
  exact hsum.trans Measure.restrict_le_self

/-- Pushing every occurrence through the same measurable endpoint map preserves
the measure-valued budget. The occurrence space may retain time, generation,
kernel-extension data, or duplicate labels for the same physical pair. -/
theorem sum_map_le_map_of_sum_le {Y : Type*} [MeasurableSpace Y]
    (root : Measure X) (terminal : I → Measure X) {endpoint : X → Y}
    (hendpoint : Measurable endpoint) (hbudget : Measure.sum terminal ≤ root) :
    Measure.sum (fun i => (terminal i).map endpoint) ≤ root.map endpoint := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.map_apply hendpoint hs]
  simp_rw [Measure.map_apply hendpoint hs]
  rw [← Measure.sum_apply _ (hendpoint hs)]
  exact hbudget (endpoint ⁻¹' s)

/-- Support plus a measure-valued root budget gives a bound on the sum of all
terminal masses by the root mass of the support set. -/
theorem terminal_mass_le_root_band
    (root : Measure X) (terminal : I → Measure X) (band : Set X)
    (hband : MeasurableSet band)
    (hbudget : Measure.sum terminal ≤ root)
    (hsupport : ∀ i, terminal i bandᶜ = 0) :
    (∑' i, terminal i univ) ≤ root band := by
  have hmass (i : I) : terminal i univ = terminal i band := by
    simpa [hsupport i] using (measure_add_measure_compl (μ := terminal i) hband).symm
  simp_rw [hmass]
  rw [← Measure.sum_apply _ hband]
  exact hbudget band

variable [PseudoMetricSpace D]

/-- Ordered endpoint pairs whose inherited directions are at distance at most
`R`. The direction map is evaluated on the original endpoints. -/
def directionBand (direction : X → D) (R : ℝ) : Set (X × X) :=
  {p | dist (direction p.1) (direction p.2) ≤ R}

omit [MeasurableSpace X] in
/-- Membership of both endpoints in one cap implies the global band invariant.
The cap center can vary arbitrarily from one terminal piece to the next. -/
theorem mem_directionBand_of_same_cap (direction : X → D)
    {p : X × X} {center : D} {radius T : ℝ}
    (hleft : direction p.1 ∈ Metric.closedBall center radius)
    (hright : direction p.2 ∈ Metric.closedBall center radius)
    (hradius : radius ≤ T) : p ∈ directionBand direction (2 * T) := by
  have hl : dist (direction p.1) center ≤ radius := hleft
  have hr : dist center (direction p.2) ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_comm] using hright
  exact (dist_triangle _ center _).trans (by linarith)

/-- Almost-everywhere membership in nodewise caps supplies the band-support
invariant. There is no hypothesis relating distinct cap centers or overlaps. -/
theorem band_support_of_cap_support
    (terminal : I → Measure (X × X)) (direction : X → D)
    (center : I → D) (radius : I → ℝ) (T : ℝ)
    (hradius : ∀ i, radius i ≤ T)
    (hcaps : ∀ i, terminal i
      {p | direction p.1 ∈ Metric.closedBall (center i) (radius i) ∧
        direction p.2 ∈ Metric.closedBall (center i) (radius i)}ᶜ = 0) :
    ∀ i, terminal i (directionBand direction (2 * T))ᶜ = 0 := by
  intro i
  apply measure_mono_null _ (hcaps i)
  apply compl_subset_compl.mpr
  intro p hp
  exact mem_directionBand_of_same_cap direction hp.1 hp.2 (hradius i)

variable [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]

theorem measurableSet_directionBand {direction : X → D}
    (hdirection : Measurable direction) (R : ℝ) :
    MeasurableSet (directionBand direction R) := by
  exact measurableSet_le
    ((hdirection.comp measurable_fst).dist (hdirection.comp measurable_snd))
    measurable_const

/-- Tonelli's theorem: a uniform bound on all direction-ball sections bounds
the product measure of the direction-distance band. -/
theorem product_band_le_of_ball_bound
    (σ : Measure X) [SFinite σ] {direction : X → D}
    (hdirection : Measurable direction) (R : ℝ) (B : ℝ≥0∞)
    (hball : ∀ a : D, σ (direction ⁻¹' Metric.closedBall a R) ≤ B) :
    (σ.prod σ) (directionBand direction R) ≤ B * σ univ := by
  rw [Measure.prod_apply (measurableSet_directionBand hdirection R)]
  calc
    (∫⁻ x, σ (Prod.mk x ⁻¹' directionBand direction R) ∂σ)
        ≤ ∫⁻ _x, B ∂σ := by
      apply lintegral_mono
      intro x
      change σ (Prod.mk x ⁻¹' directionBand direction R) ≤ B
      have hsection : Prod.mk x ⁻¹' directionBand direction R =
          direction ⁻¹' Metric.closedBall (direction x) R := by
        ext y
        simp only [mem_preimage, directionBand, mem_ofPred_eq, Metric.mem_closedBall]
        rw [dist_comm]
      rw [hsection]
      exact hball (direction x)
    _ = B * σ univ := lintegral_const B

/-- The aggregate terminal bound, with the root and product dominations kept
as distinct, explicitly measure-valued hypotheses. -/
theorem terminal_mass_le_product_band
    (σ : Measure X) (root : Measure (X × X))
    (terminal : I → Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) (R : ℝ)
    (hbudget : Measure.sum terminal ≤ root)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i (directionBand direction R)ᶜ = 0) :
    (∑' i, terminal i univ) ≤ (σ.prod σ) (directionBand direction R) := by
  exact (terminal_mass_le_root_band root terminal (directionBand direction R)
    (measurableSet_directionBand hdirection R) hbudget hsupport).trans
    (hroot (directionBand direction R))

/-- Three-dimensional ball density bounds the product-band mass. -/
theorem product_band_le_cubic
    (σ : Measure X) [SFinite σ] {direction : X → D}
    (hdirection : Measurable direction) (C : ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T)
    (hdensity : ∀ a : D, ∀ R : ℝ, 0 ≤ R →
      σ (direction ⁻¹' Metric.closedBall a R) ≤ C * ENNReal.ofReal R ^ 3) :
    (σ.prod σ) (directionBand direction (2 * T)) ≤
      8 * C * σ univ * ENNReal.ofReal T ^ 3 := by
  calc
    (σ.prod σ) (directionBand direction (2 * T)) ≤
        (C * ENNReal.ofReal (2 * T) ^ 3) * σ univ :=
      product_band_le_of_ball_bound σ hdirection (2 * T) _
        (fun a => hdensity a (2 * T) (by positivity))
    _ = 8 * C * σ univ * ENNReal.ofReal T ^ 3 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
      norm_num
      ring

/-- A bounded three-dimensional direction density at the common terminal scale
gives the desired global `C m T^3` estimate. The factor eight is `(2 T)^3 / T^3`.
Here `C` belongs to the original selector measure, not to a normalized old-neighbor
conditional probability. -/
theorem terminal_mass_le_cubic
    (σ : Measure X) [SFinite σ] (root : Measure (X × X))
    (terminal : I → Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) (C : ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T)
    (hbudget : Measure.sum terminal ≤ root)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i (directionBand direction (2 * T))ᶜ = 0)
    (hdensity : ∀ a : D, ∀ R : ℝ, 0 ≤ R →
      σ (direction ⁻¹' Metric.closedBall a R) ≤ C * ENNReal.ofReal R ^ 3) :
    (∑' i, terminal i univ) ≤ 8 * C * σ univ * ENNReal.ofReal T ^ 3 := by
  exact (terminal_mass_le_product_band σ root terminal hdirection (2 * T)
    hbudget hroot hsupport).trans (product_band_le_cubic σ hdirection C hT hdensity)

/-- If orientation bookkeeping only gives domination by the original root plus
its transpose, the same estimate holds with the explicit extra factor two.
This hypothesis still concerns measures of original endpoint pairs. -/
theorem terminal_mass_le_cubic_with_reversal
    (σ : Measure X) [SFinite σ] (root : Measure (X × X))
    (terminal : I → Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) (C : ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T)
    (hbudget : Measure.sum terminal ≤ root + root.map Prod.swap)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i (directionBand direction (2 * T))ᶜ = 0)
    (hdensity : ∀ a : D, ∀ R : ℝ, 0 ≤ R →
      σ (direction ⁻¹' Metric.closedBall a R) ≤ C * ENNReal.ofReal R ^ 3) :
    (∑' i, terminal i univ) ≤ 16 * C * σ univ * ENNReal.ofReal T ^ 3 := by
  have htranspose : root.map Prod.swap ≤ σ.prod σ := by
    simpa only [Measure.prod_swap] using Measure.map_mono hroot measurable_swap
  have hdom : root + root.map Prod.swap ≤ σ.prod σ + σ.prod σ :=
    add_le_add hroot htranspose
  have hband := measurableSet_directionBand hdirection (2 * T)
  have hproduct := product_band_le_cubic σ hdirection C hT hdensity
  calc
    (∑' i, terminal i univ) ≤
        (root + root.map Prod.swap) (directionBand direction (2 * T)) :=
      terminal_mass_le_root_band _ terminal _ hband hbudget hsupport
    _ ≤ (σ.prod σ + σ.prod σ) (directionBand direction (2 * T)) := hdom _
    _ = (σ.prod σ) (directionBand direction (2 * T)) +
        (σ.prod σ) (directionBand direction (2 * T)) := Measure.add_apply _ _ _
    _ ≤ (8 * C * σ univ * ENNReal.ofReal T ^ 3) +
        (8 * C * σ univ * ENNReal.ofReal T ^ 3) := add_le_add hproduct hproduct
    _ = 16 * C * σ univ * ENNReal.ofReal T ^ 3 := by ring

/-- At a stopping scale satisfying `T^3 ≤ m q`, the global terminal estimate
has the quadratic selector-mass budget `8 C m^2 q`. The source-mass factor is
the mass of the original selector measure throughout. -/
theorem terminal_mass_le_quadratic
    (σ : Measure X) [SFinite σ] (root : Measure (X × X))
    (terminal : I → Measure (X × X)) {direction : X → D}
    (hdirection : Measurable direction) (C q : ℝ≥0∞) {T : ℝ} (hT : 0 ≤ T)
    (hbudget : Measure.sum terminal ≤ root)
    (hroot : root ≤ σ.prod σ)
    (hsupport : ∀ i, terminal i (directionBand direction (2 * T))ᶜ = 0)
    (hdensity : ∀ a : D, ∀ R : ℝ, 0 ≤ R →
      σ (direction ⁻¹' Metric.closedBall a R) ≤ C * ENNReal.ofReal R ^ 3)
    (hscale : ENNReal.ofReal T ^ 3 ≤ σ univ * q) :
    (∑' i, terminal i univ) ≤ 8 * C * (σ univ) ^ 2 * q := by
  calc
    (∑' i, terminal i univ) ≤ 8 * C * σ univ * ENNReal.ofReal T ^ 3 :=
      terminal_mass_le_cubic σ root terminal hdirection C hT hbudget hroot hsupport hdensity
    _ ≤ 8 * C * σ univ * (σ univ * q) := mul_le_mul_right hscale _
    _ = 8 * C * (σ univ) ^ 2 * q := by ring

end StickyKakeya4.GlobalTerminalBand
