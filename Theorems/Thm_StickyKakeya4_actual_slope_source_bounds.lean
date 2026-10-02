import Theorems.Thm_StickyKakeya4_actual_slope_source
import Theorems.Thm_StickyKakeya4_collision_edge_contact_residual

/-!
# Compact-source intercept bounds

These bounds are derived from the original compact marked family. They do
not assume a bounded intercept as a new source certificate. The pointwise
selector-line argument gives `‖b(a)‖ ≤ 2 R` whenever all original offsets
have norm at most `R`. A second argument uses the already proved front
support at a single common height, preserving the source returned by the
existing existential theorem without changing its construction.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.ActualSlopeSource

theorem horizontalProjection_heightPoint (x : E3) (s : ℝ) :
    horizontalProjection (heightPoint x s) = x := by
  ext i
  exact heightPoint_castSucc x s i

/-- The slope-one chart loses at most a factor two from offset to intercept. -/
theorem norm_northGraphIntercept_le_twice_offset (line : MarkedLine)
    (hslope : ‖northGraphSlope line‖ ≤ 1) :
    ‖northGraphIntercept line‖ ≤ 2 * ‖offset line‖ := by
  have hcoord : |offset line (3 : Fin 4)| ≤ ‖offset line‖ := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (offset line) (3 : Fin 4))
  calc
    ‖northGraphIntercept line‖ ≤
        ‖horizontalProjection (offset line)‖ +
          ‖offset line (3 : Fin 4) • northGraphSlope line‖ := norm_sub_le _ _
    _ = ‖horizontalProjection (offset line)‖ +
        |offset line (3 : Fin 4)| * ‖northGraphSlope line‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖offset line‖ + ‖offset line‖ * 1 :=
      add_le_add (norm_horizontalProjection_le _)
        (mul_le_mul hcoord hslope (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖offset line‖ := by ring

/-- Compactness supplies one offset bound for the whole original datum. -/
theorem compact_offset_bound (ambient : Set MarkedLine) (hcompact : IsCompact ambient) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ line ∈ ambient, ‖offset line‖ ≤ R := by
  have hoffset : Continuous (offset : MarkedLine → E4) := by
    unfold offset
    fun_prop
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn hoffset.continuousOn
  exact ⟨max R 0, le_max_right _ _, fun line hline => (hR line hline).trans (le_max_left _ _)⟩

/-- The constructed source inherits an explicit intercept bound from its
original marked-line offsets; no new source truncation is performed. -/
theorem sourceMeasure_intercept_le_twice_offset_bound
    (ambient selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (hsubset : selector ⊆ ambient)
    (R : ℝ) (hR : ∀ line ∈ ambient, ‖offset line‖ ≤ R) (k : ℤ) :
    ∀ᵐ a ∂sourceMeasure selector hmeas hvalid hselector k,
      ‖intercept selector hmeas hvalid hselector a‖ ≤ 2 * R := by
  filter_upwards [sourceMeasure_slope_norm_le_one selector hmeas hvalid hselector k]
    with a ha
  have hslope : ‖northGraphSlope (slopeLine selector hmeas hvalid hselector a)‖ ≤ 1 := by
    rw [slope_slopeLine]
    exact ha
  exact (norm_northGraphIntercept_le_twice_offset _ hslope).trans
    (mul_le_mul_of_nonneg_left
      (hR _ (hsubset (slopeLine_mem selector hmeas hvalid hselector a))) (by norm_num))

/-- A single compactness bound works for every centre bin of the source. -/
theorem sourceMeasure_intercept_bound_of_compact
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (hsubset : selector ⊆ ambient) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℤ,
      ∀ᵐ a ∂sourceMeasure selector hmeas hvalid hselector k,
        ‖intercept selector hmeas hvalid hselector a‖ ≤ B := by
  obtain ⟨R, hR0, hR⟩ := compact_offset_bound ambient hcompact
  exact ⟨2 * R, mul_nonneg (by norm_num) hR0, fun k =>
    sourceMeasure_intercept_le_twice_offset_bound ambient selector hmeas hvalid
      hselector hsubset R hR k⟩

/-- Actual compact-front support at one height bounds any slope-one source's
intercept. This formulation also applies after the selector lineage has been
hidden by an existential statement. -/
theorem intercept_bound_of_compact_front_support
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) (b : E3 → E3) (s : ℝ)
    (hslope : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (hsupport : ∀ᵐ a ∂σ, heightPoint (b a + s • a) s ∈ unitFront ambient) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ a ∂σ, ‖b a‖ ≤ B := by
  obtain ⟨M, hM⟩ := (StickyKakeya4.IsCompact.unitFront hcompact).isBounded.exists_norm_le
  refine ⟨max M 0 + |s|, add_nonneg (le_max_right _ _) (abs_nonneg _), ?_⟩
  filter_upwards [hslope, hsupport] with a ha hpoint
  have hpointBound : ‖heightPoint (b a + s • a) s‖ ≤ max M 0 :=
    (hM _ hpoint).trans (le_max_left _ _)
  have hhorizontal := (norm_horizontalProjection_le _).trans hpointBound
  rw [horizontalProjection_heightPoint] at hhorizontal
  calc
    ‖b a‖ = ‖(b a + s • a) - s • a‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖b a + s • a‖ + ‖s • a‖ := norm_sub_le _ _
    _ ≤ max M 0 + |s| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hhorizontal (by simpa using mul_le_mul_of_nonneg_left ha (abs_nonneg s))

/-- The actual-source theorem sharpened with a finite nonnegative intercept
bound, preserving its positive mass, density, slopes, interval, and support. -/
theorem compact_full_direction_actual_slope_source_bounded
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (hvalid : ∀ line ∈ ambient, IsValidLine line) (hfull : FullDirection ambient) :
    ∃ (σ : Measure E3) (b : E3 → E3) (u v B : ℝ),
      IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
      v - u = 3 / 8 ∧ 0 ≤ B ∧
      (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧ (∀ᵐ a ∂σ, ‖b a‖ ≤ B) ∧
      ∀ᵐ a ∂σ, ∀ s ∈ Icc u v, heightPoint (b a + s • a) s ∈ unitFront ambient := by
  obtain ⟨σ, b, u, v, hfinite, hmass, hdensity, hb, hlength, hslope, hsupport⟩ :=
    compact_full_direction_actual_slope_source ambient hcompact hvalid hfull
  have huv : u ≤ v := by linarith
  have hatu : ∀ᵐ a ∂σ, heightPoint (b a + u • a) u ∈ unitFront ambient :=
    hsupport.mono (fun a ha => ha u ⟨le_rfl, huv⟩)
  obtain ⟨B, hB0, hB⟩ :=
    intercept_bound_of_compact_front_support ambient hcompact σ b u hslope hatu
  exact ⟨σ, b, u, v, B, hfinite, hmass, hdensity, hb, hlength, hB0, hslope, hB, hsupport⟩

end StickyKakeya4.ActualSlopeSource
