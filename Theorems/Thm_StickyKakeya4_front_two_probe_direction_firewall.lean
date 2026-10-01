import Theorems.Thm_StickyKakeya4_front_direction_cap_firewall
import Theorems.Thm_StickyKakeya4_north_graph_contact_coordinates
import Mathlib.Analysis.Normed.Module.Normalize

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4

/-- Normalization is two-Lipschitz on the complement of the open unit ball.
This elementary estimate is used to return from graph slopes to actual unit
directions; no compactness or Kakeya input occurs here. -/
theorem norm_normalize_sub_normalize_le_two_of_one_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      2 * ‖x - y‖ := by
  have hxpos : 0 < ‖x‖ := zero_lt_one.trans_le hx
  have hypos : 0 < ‖y‖ := zero_lt_one.trans_le hy
  have hxinv : ‖x‖⁻¹ ≤ 1 := (inv_le_one₀ hxpos).2 hx
  have hfirst : ‖x‖⁻¹ * ‖x - y‖ ≤ ‖x - y‖ := by
    simpa using mul_le_mul_of_nonneg_right hxinv (norm_nonneg (x - y))
  have hinvIdentity :
      |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [show ‖x‖⁻¹ - ‖y‖⁻¹ =
        (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) by
      field_simp [ne_of_gt hxpos, ne_of_gt hypos]]
    rw [abs_div, abs_mul, abs_of_pos hxpos, abs_of_pos hypos]
    field_simp [ne_of_gt hxpos, ne_of_gt hypos]
  have hsecond : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ ≤ ‖x - y‖ := by
    rw [hinvIdentity]
    calc
      |‖y‖ - ‖x‖| / ‖x‖ ≤ ‖y - x‖ / ‖x‖ := by
        gcongr
        simpa [abs_sub_comm, norm_sub_rev] using abs_norm_sub_norm_le x y
      _ ≤ ‖y - x‖ := (div_le_iff₀ hxpos).2 (by
        nlinarith [norm_nonneg (y - x)])
      _ = ‖x - y‖ := norm_sub_rev y x
  calc
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ =
        ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      congr 1
      simp only [NormedSpace.normalize]
      module
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ :=
      norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add hfirst hsecond
    _ = 2 * ‖x - y‖ := by ring

/-- The inverse graph-chart lift of a north slope: its fourth coordinate is
one and its first three coordinates are the slope. -/
def northSlopeLift (a : E3) : E4 :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun i : Fin 3 => a i))

@[simp] theorem northSlopeLift_castSucc (a : E3) (i : Fin 3) :
    northSlopeLift a i.castSucc = a i := by
  simp [northSlopeLift]

@[simp] theorem northSlopeLift_last (a : E3) :
    northSlopeLift a (Fin.last 3) = 1 := by
  simpa [northSlopeLift] using
    (Fin.lastCases_last (motive := fun _ : Fin 4 => ℝ)
      (last := (1 : ℝ)) (cast := fun i : Fin 3 => a i))

theorem northSlopeLift_norm_ge_one (a : E3) :
    1 ≤ ‖northSlopeLift a‖ := by
  have hsq : 1 ≤ ‖northSlopeLift a‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
      northSlopeLift_last]
    simp [northSlopeLift]
    positivity
  nlinarith [norm_nonneg (northSlopeLift a)]

theorem northSlopeLift_sub_norm (a b : E3) :
    ‖northSlopeLift a - northSlopeLift b‖ = ‖a - b‖ := by
  have hsq : ‖northSlopeLift a - northSlopeLift b‖ ^ 2 =
      ‖a - b‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_castSucc]
    simp only [PiLp.sub_apply]
    rw [northSlopeLift_last, northSlopeLift_last]
    simp [northSlopeLift]
  nlinarith [norm_nonneg (northSlopeLift a - northSlopeLift b),
    norm_nonneg (a - b)]

/-- On the positive north chart, normalizing the lifted graph slope recovers
the actual oriented unit direction. -/
theorem normalize_northSlopeLift
    (line : MarkedLine) (hvalid : IsValidLine line)
    (hpos : 0 < direction line (3 : Fin 4)) :
    NormedSpace.normalize (northSlopeLift (northGraphSlope line)) =
      direction line := by
  have hlift : northSlopeLift (northGraphSlope line) =
      (direction line (3 : Fin 4))⁻¹ • direction line := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change 1 = (direction line (3 : Fin 4))⁻¹ *
        direction line (3 : Fin 4)
      exact (inv_mul_cancel₀ hpos.ne').symm
    · simp [northSlopeLift, northGraphSlope, horizontalProjection]
  rw [hlift, NormedSpace.normalize_smul_of_pos (inv_pos.mpr hpos)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hvalid.1

/-- The positive north-chart inverse is uniformly two-Lipschitz from slopes
to actual unit directions. -/
theorem northGraphSlope_direction_bound
    (line line' : MarkedLine)
    (hvalid : IsValidLine line) (hvalid' : IsValidLine line')
    (hpos : 0 < direction line (3 : Fin 4))
    (hpos' : 0 < direction line' (3 : Fin 4)) :
    dist (direction line) (direction line') ≤
      2 * ‖northGraphSlope line - northGraphSlope line'‖ := by
  rw [← normalize_northSlopeLift line hvalid hpos,
    ← normalize_northSlopeLift line' hvalid' hpos']
  simpa [dist_eq_norm, northSlopeLift_sub_norm] using
    norm_normalize_sub_normalize_le_two_of_one_le
      (northSlopeLift (northGraphSlope line))
      (northSlopeLift (northGraphSlope line'))
      (northSlopeLift_norm_ge_one _)
      (northSlopeLift_norm_ge_one _)

/-- Two separated common-height probes control the actual spherical direction
distance, not merely the auxiliary graph slope. -/
theorem northGraph_two_probe_direction_bound
    (line line' : MarkedLine)
    (hvalid : IsValidLine line) (hvalid' : IsValidLine line')
    (hpos : 0 < direction line (3 : Fin 4))
    (hpos' : 0 < direction line' (3 : Fin 4))
    (s t Rs Rt g : ℝ)
    (hRs : ‖northGraphEvaluation line s -
      northGraphEvaluation line' s‖ ≤ Rs)
    (hRt : ‖northGraphEvaluation line t -
      northGraphEvaluation line' t‖ ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) :
    dist (direction line) (direction line') ≤
      2 * ((Rs + Rt) / g) := by
  have hslope : ‖northGraphSlope line - northGraphSlope line'‖ ≤
      (Rs + Rt) / g := by
    simpa [northGraphSecant] using
      northGraph_two_probe_slope_secant_bound line line' s t Rs Rt g
        hRs hRt hg hsep
  exact (northGraphSlope_direction_bound line line' hvalid hvalid'
    hpos hpos').trans (mul_le_mul_of_nonneg_left hslope (by norm_num))

/-- Source-hereditary two-probe localization.  If every retained occurrence
has the same two separated physical probes relative to one reference line,
then all retained directions lie in one explicit spherical cap. -/
theorem source_subset_frontDirectionCap_of_two_probe
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : Set FrontParameterSpace) (reference : MarkedLine)
    (href : reference ∈ selector)
    (hsourcePos : ∀ z ∈ source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hrefPos : 0 < direction reference (3 : Fin 4))
    (s t Rs Rt g eta : ℝ)
    (hRs : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) s -
        northGraphEvaluation reference s‖ ≤ Rs)
    (hRt : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) (heta : 0 < eta) :
    source ⊆ frontDirectionCap
      ⟨direction reference, (hvalid reference href).1⟩
      (2 * ((Rs + Rt) / g) + eta) := by
  intro z hz
  let line := selectorLine selector hmeasurable hvalid hselector z.1
  have hlineValid : IsValidLine line := hvalid line line.property
  have hdir := northGraph_two_probe_direction_bound line reference
    hlineValid (hvalid reference href) (hsourcePos z hz) hrefPos
    s t Rs Rt g (hRs z hz) (hRt z hz) hg hsep
  change dist (z.1 : E4) (direction reference) <
    2 * ((Rs + Rt) / g) + eta
  rw [← direction_selectorLine selector hmeasurable hvalid hselector z.1]
  exact hdir.trans_lt (lt_add_of_pos_right _ heta)

/-- Quantitative family-level firewall obtained by combining two-probe
localization with the cubic spherical-cap law.  The statement applies to any
retained measurable or weighted source through its underlying parameter set. -/
theorem frontParameterProbability_source_le_of_two_probe
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : Set FrontParameterSpace) (reference : MarkedLine)
    (href : reference ∈ selector)
    (hsourcePos : ∀ z ∈ source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hrefPos : 0 < direction reference (3 : Fin 4))
    (s t Rs Rt g eta : ℝ)
    (hRs : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) s -
        northGraphEvaluation reference s‖ ≤ Rs)
    (hRt : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ Rt)
    (hRsNonneg : 0 ≤ Rs) (hRtNonneg : 0 ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) (heta : 0 < eta)
    (hradiusOne : 2 * ((Rs + Rt) / g) + eta ≤ 1) :
    (frontParameterProbability : Measure FrontParameterSpace) source ≤
      metricSphereCapConstant *
        (ENNReal.ofReal (2 * ((Rs + Rt) / g) + eta)) ^ 3 := by
  apply frontParameterProbability_source_le_directionCap source
    ⟨direction reference, (hvalid reference href).1⟩
  · exact source_subset_frontDirectionCap_of_two_probe
      selector hmeasurable hvalid hselector source reference href
      hsourcePos hrefPos s t Rs Rt g eta hRs hRt hg hsep heta
  · have hquotient : 0 ≤ (Rs + Rt) / g :=
      div_nonneg (add_nonneg hRsNonneg hRtNonneg) hg.le
    nlinarith
  · exact hradiusOne

/-- Terminal coefficient-one contradiction.  A retained source with a fixed
positive mass floor cannot simultaneously satisfy two separated probe bounds
whose induced direction cap is below the cubic mass threshold. -/
theorem no_positive_mass_source_of_two_probe
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (source : Set FrontParameterSpace) (reference : MarkedLine)
    (href : reference ∈ selector)
    (hsourcePos : ∀ z ∈ source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4))
    (hrefPos : 0 < direction reference (3 : Fin 4))
    (s t Rs Rt g eta : ℝ)
    (hRs : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) s -
        northGraphEvaluation reference s‖ ≤ Rs)
    (hRt : ∀ z ∈ source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ Rt)
    (hRsNonneg : 0 ≤ Rs) (hRtNonneg : 0 ≤ Rt)
    (hg : 0 < g) (hsep : g ≤ |t - s|) (heta : 0 < eta)
    (hradiusOne : 2 * ((Rs + Rt) / g) + eta ≤ 1)
    (q : ENNReal)
    (hq : q ≤ (frontParameterProbability : Measure FrontParameterSpace) source)
    (hsmall : metricSphereCapConstant *
      (ENNReal.ofReal (2 * ((Rs + Rt) / g) + eta)) ^ 3 < q) : False := by
  have hupper := frontParameterProbability_source_le_of_two_probe
    selector hmeasurable hvalid hselector source reference href
    hsourcePos hrefPos s t Rs Rt g eta hRs hRt hRsNonneg hRtNonneg
    hg hsep heta hradiusOne
  exact (not_lt_of_ge (hq.trans hupper)) hsmall

end StickyKakeya4
