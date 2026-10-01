import Theorems.Thm_StickyKakeya4_compact_front

open Set

noncomputable section

namespace StickyKakeya4

/-!
The fixed-slab chart used when transporting the ordinary-tube theorem of
Wang--Zakharov to marked unit segments.

The unmarked carrier `(direction, offset)` determines the point at a fixed
fourth coordinate.  The affine mark is used only to certify that this point
lies on the selected unit segment.  Keeping these two roles separate prevents
carrier proximity from being confused with proximity at equal relative Reeb
time.
-/

/-- Affine-line time at which `line` reaches fourth coordinate `s`. -/
def wzGraphTime (line : MarkedLine) (s : ℝ) : ℝ :=
  (s - offset line (3 : Fin 4)) / direction line (3 : Fin 4)

/-- Point of the underlying affine line at fourth coordinate `s`.  On a
direction chart avoiding the equator this depends only on the unmarked
carrier. -/
def wzGraphPoint (line : MarkedLine) (s : ℝ) : E4 :=
  offset line + wzGraphTime line s • direction line

/-- Fourth coordinate of the point selected by the affine mark. -/
def wzMarkedCenterHeight (line : MarkedLine) : ℝ :=
  rawFrontParam (line, 0) (3 : Fin 4)

theorem continuous_wzMarkedCenterHeight :
    Continuous wzMarkedCenterHeight := by
  unfold wzMarkedCenterHeight rawFrontParam offset mark direction
  fun_prop

theorem measurable_wzMarkedCenterHeight :
    Measurable wzMarkedCenterHeight :=
  continuous_wzMarkedCenterHeight.measurable

theorem wzMarkedCenterHeight_eq (line : MarkedLine) :
    wzMarkedCenterHeight line =
      offset line (3 : Fin 4) +
        mark line * direction line (3 : Fin 4) := by
  simp [wzMarkedCenterHeight, rawFrontParam]

/-- A marked unit segment contains every graph point over the height set
`I`.  The nonvanishing direction-coordinate clause is the chart condition. -/
def ContainsWZHeightSlab (line : MarkedLine) (I : Set ℝ) : Prop :=
  direction line (3 : Fin 4) ≠ 0 ∧
    ∀ s ∈ I,
      wzGraphTime line s - mark line ∈
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- Exact change from the fixed-height graph parametrization to the marked
Reeb-time parametrization. -/
theorem wzGraphPoint_eq_rawFrontParam (line : MarkedLine) (s : ℝ) :
    wzGraphPoint line s =
      rawFrontParam (line, wzGraphTime line s - mark line) := by
  unfold wzGraphPoint rawFrontParam
  rw [show mark line + (wzGraphTime line s - mark line) =
      wzGraphTime line s by ring]

/-- The graph point really has the prescribed fourth coordinate. -/
theorem wzGraphPoint_fourth_coordinate (line : MarkedLine) (s : ℝ)
    (hchart : direction line (3 : Fin 4) ≠ 0) :
    wzGraphPoint line s (3 : Fin 4) = s := by
  simp only [wzGraphPoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    wzGraphTime]
  field_simp [hchart]
  ring

/-- Relative marked time is exactly normalized height displacement from the
marked centre. -/
theorem wzGraphTime_sub_mark_eq
    (line : MarkedLine) (s : ℝ)
    (hchart : direction line (3 : Fin 4) ≠ 0) :
    wzGraphTime line s - mark line =
      (s - wzMarkedCenterHeight line) /
        direction line (3 : Fin 4) := by
  rw [wzMarkedCenterHeight_eq]
  unfold wzGraphTime
  field_simp [hchart]
  ring

/-- If the positive fourth direction coordinate is bounded below by `c` and
the marked centre height lies in one bin `[u,u+h]`, then the segment contains
the common height interval displayed below. -/
theorem containsWZHeightSlab_of_center_bin
    (line : MarkedLine) {c u h : ℝ}
    (hc : 0 < c)
    (hdir : c ≤ direction line (3 : Fin 4))
    (hcenterLower : u ≤ wzMarkedCenterHeight line)
    (hcenterUpper : wzMarkedCenterHeight line ≤ u + h) :
    ContainsWZHeightSlab line
      (Set.Icc (u + h - c / 2) (u + c / 2)) := by
  have hdirPos : 0 < direction line (3 : Fin 4) := hc.trans_le hdir
  constructor
  · exact ne_of_gt hdirPos
  · intro s hs
    rw [wzGraphTime_sub_mark_eq line s (ne_of_gt hdirPos)]
    constructor
    · rw [le_div_iff₀ hdirPos]
      nlinarith [hs.1]
    · rw [div_le_iff₀ hdirPos]
      nlinarith [hs.2]

/-- The common interval supplied by one centre bin is nonempty. -/
theorem commonWZHeightInterval_nonempty
    {c u h : ℝ} (hh : h ≤ c) :
    (Set.Icc (u + h - c / 2) (u + c / 2)).Nonempty := by
  exact Set.nonempty_Icc.mpr (by linarith)

/-- Exact denominator identity behind the fixed-height chart comparison.
It keeps the two sources of variation separate: displacement of the offsets
and displacement of the directions. -/
theorem wzGraphTime_sub_eq
    (line line' : MarkedLine) (s : ℝ)
    (hline : direction line (3 : Fin 4) ≠ 0)
    (hline' : direction line' (3 : Fin 4) ≠ 0) :
    wzGraphTime line s - wzGraphTime line' s =
      (offset line' (3 : Fin 4) - offset line (3 : Fin 4)) /
          direction line (3 : Fin 4) +
        (s - offset line' (3 : Fin 4)) *
          (direction line' (3 : Fin 4) - direction line (3 : Fin 4)) /
          (direction line (3 : Fin 4) * direction line' (3 : Fin 4)) := by
  unfold wzGraphTime
  field_simp [hline, hline']
  ring

/-- Quantitative denominator estimate for the graph-time comparison.  A
uniform lower bound on the two fourth direction coordinates now gives the
chart Lipschitz constant by monotonicity of division. -/
theorem abs_wzGraphTime_sub_le
    (line line' : MarkedLine) (s : ℝ)
    (hline : direction line (3 : Fin 4) ≠ 0)
    (hline' : direction line' (3 : Fin 4) ≠ 0) :
    |wzGraphTime line s - wzGraphTime line' s| ≤
      |offset line' (3 : Fin 4) - offset line (3 : Fin 4)| /
          |direction line (3 : Fin 4)| +
        (|s - offset line' (3 : Fin 4)| *
          |direction line' (3 : Fin 4) - direction line (3 : Fin 4)|) /
          (|direction line (3 : Fin 4)| *
            |direction line' (3 : Fin 4)|) := by
  rw [wzGraphTime_sub_eq line line' s hline hline']
  calc
    |(offset line' (3 : Fin 4) - offset line (3 : Fin 4)) /
          direction line (3 : Fin 4) +
        (s - offset line' (3 : Fin 4)) *
          (direction line' (3 : Fin 4) - direction line (3 : Fin 4)) /
          (direction line (3 : Fin 4) * direction line' (3 : Fin 4))| ≤
        |(offset line' (3 : Fin 4) - offset line (3 : Fin 4)) /
          direction line (3 : Fin 4)| +
        |(s - offset line' (3 : Fin 4)) *
          (direction line' (3 : Fin 4) - direction line (3 : Fin 4)) /
          (direction line (3 : Fin 4) * direction line' (3 : Fin 4))| :=
      abs_add_le _ _
    _ = |offset line' (3 : Fin 4) - offset line (3 : Fin 4)| /
          |direction line (3 : Fin 4)| +
        (|s - offset line' (3 : Fin 4)| *
          |direction line' (3 : Fin 4) - direction line (3 : Fin 4)|) /
          (|direction line (3 : Fin 4)| *
            |direction line' (3 : Fin 4)|) := by
      simp only [abs_div, abs_mul]

/-- Exact affine decomposition of the difference of two fixed-height graph
points.  Unlike equal relative Reeb time, this comparison is independent of
the two affine marks. -/
theorem wzGraphPoint_sub_eq
    (line line' : MarkedLine) (s : ℝ) :
    wzGraphPoint line s - wzGraphPoint line' s =
      (offset line - offset line') +
        wzGraphTime line s • (direction line - direction line') +
        (wzGraphTime line s - wzGraphTime line' s) • direction line' := by
  ext j
  simp only [wzGraphPoint, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-- Metric consequence of the exact affine decomposition.  Subsequent chart
bounds only need to estimate the two scalar graph times. -/
theorem dist_wzGraphPoint_le
    (line line' : MarkedLine) (s : ℝ) :
    dist (wzGraphPoint line s) (wzGraphPoint line' s) ≤
      dist (offset line) (offset line') +
        |wzGraphTime line s| * dist (direction line) (direction line') +
        |wzGraphTime line s - wzGraphTime line' s| * ‖direction line'‖ := by
  rw [dist_eq_norm, wzGraphPoint_sub_eq, dist_eq_norm, dist_eq_norm]
  calc
    ‖(offset line - offset line') +
          wzGraphTime line s • (direction line - direction line') +
          (wzGraphTime line s - wzGraphTime line' s) • direction line'‖ ≤
        ‖offset line - offset line'‖ +
            ‖wzGraphTime line s • (direction line - direction line')‖ +
          ‖(wzGraphTime line s - wzGraphTime line' s) • direction line'‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ = ‖offset line - offset line'‖ +
          |wzGraphTime line s| * ‖direction line - direction line'‖ +
          |wzGraphTime line s - wzGraphTime line' s| * ‖direction line'‖ := by
      simp only [norm_smul, Real.norm_eq_abs]

/-- The slab certificate, rather than carrier closeness alone, licenses the
passage from an unmarked graph point to the actual marked unit front. -/
theorem wzGraphPoint_mem_unitFront_singleton
    (line : MarkedLine) (I : Set ℝ) (hslab : ContainsWZHeightSlab line I)
    {s : ℝ} (hs : s ∈ I) :
    wzGraphPoint line s ∈ unitFront {line} := by
  rw [wzGraphPoint_eq_rawFrontParam]
  exact rawFrontParam_mem_unitFront_singleton line (hslab.2 s hs)

/-- A finite marked source is normalized to one common graph slab when all of
its selected unit segments contain the same nonempty height set. -/
def HasCommonWZHeightSlab {n : ℕ} (D : FiniteScaleSource n)
    (I : Set ℝ) : Prop :=
  I.Nonempty ∧ ∀ i, ContainsWZHeightSlab (D.line i) I

/-- Native graph-chart certificate for the Wang--Zakharov normalization.
The fourth direction coordinate has one fixed positive lower bound and the
common absolute-height interval has one fixed positive length.  These fixed
constants may be absorbed into the theorem constant, whereas a
scale-dependent or merely nonempty slab could not. -/
def HasNormalizedWZGraphSlab {n : ℕ} (D : FiniteScaleSource n) : Prop :=
  (∀ i, (1 / 2 : ℝ) ≤ direction (D.line i) (3 : Fin 4)) ∧
  ∃ a b : ℝ, (1 / 8 : ℝ) ≤ b - a ∧
    HasCommonWZHeightSlab D (Set.Icc a b)

/-- The full marked segments, not only their common inner slab, lie in one
fixed-height window.  This is the remaining bounded-chart datum in the
ordinary graph-tube normalization used by Wang--Zakharov. -/
def HasFixedWZGraphNormalization {n : ℕ} (D : FiniteScaleSource n) : Prop :=
  ∃ a b : ℝ, (1 / 8 : ℝ) ≤ b - a ∧
    (∀ i, ContainsWZHeightSlab (D.line i) (Set.Icc a b)) ∧
    ∀ i t, t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) →
      rawFrontParam (D.line i, t) (3 : Fin 4) ∈
        Set.Icc (a - 1) (b + 1)

/-- Every coordinate of a valid unit direction is at most one.  We record
the fourth-coordinate instance used by the fixed graph chart. -/
theorem validLine_direction_fourth_le_one (line : MarkedLine)
    (hvalid : IsValidLine line) :
    direction line (3 : Fin 4) ≤ 1 := by
  let e : E4 := EuclideanSpace.single (3 : Fin 4) (1 : ℝ)
  have he : ‖e‖ = 1 := by
    simp [e]
  have hinner := abs_real_inner_le_norm e (direction line)
  rw [he, one_mul, hvalid.1] at hinner
  have hcoordinate : |direction line (3 : Fin 4)| ≤ 1 := by
    simpa [e, EuclideanSpace.inner_single_left] using hinner
  exact (le_abs_self _).trans hcoordinate

/-- A normalized common slab and unit-speed validity imply the complete
fixed-window graph normalization.  Thus no scale-dependent translation or
tube-length loss is hidden when the marked family is passed to the published
ordinary-tube theorem. -/
theorem hasFixedWZGraphNormalization_of_normalizedSlab
    {n : ℕ} (D : FiniteScaleSource n)
    (hvalid : ∀ i, IsValidLine (D.line i))
    (hslab : HasNormalizedWZGraphSlab D) :
    HasFixedWZGraphNormalization D := by
  obtain ⟨hdirLower, a, b, hlength, hcommon⟩ := hslab
  have hab : a ≤ b := by linarith
  refine ⟨a, b, hlength, hcommon.2, ?_⟩
  intro i t ht
  have haMem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hrelative := (hcommon.2 i).2 a haMem
  have hchart : direction (D.line i) (3 : Fin 4) ≠ 0 :=
    (hcommon.2 i).1
  have haPoint :
      rawFrontParam
          (D.line i, wzGraphTime (D.line i) a - mark (D.line i))
          (3 : Fin 4) = a := by
    rw [← wzGraphPoint_eq_rawFrontParam,
      wzGraphPoint_fourth_coordinate (D.line i) a hchart]
  have hdirUpper : direction (D.line i) (3 : Fin 4) ≤ 1 :=
    validLine_direction_fourth_le_one (D.line i) (hvalid i)
  simp only [rawFrontParam, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    at haPoint ⊢
  constructor <;>
    nlinarith [hdirLower i, hdirUpper, hrelative.1, hrelative.2,
      ht.1, ht.2]

/-- Finite-source form of the centre-bin localization.  It packages the
pointwise geometric lemma into the certificate consumed by the WZ adapter. -/
theorem hasCommonWZHeightSlab_of_center_bin
    {n : ℕ} (D : FiniteScaleSource n) {c u h : ℝ}
    (hc : 0 < c) (hhNonneg : 0 ≤ h) (hh : h ≤ c)
    (hdir : ∀ i, c ≤ direction (D.line i) (3 : Fin 4))
    (hcenterLower : ∀ i, u ≤ wzMarkedCenterHeight (D.line i))
    (hcenterUpper : ∀ i, wzMarkedCenterHeight (D.line i) ≤ u + h) :
    HasCommonWZHeightSlab D
      (Set.Icc (u + h - c / 2) (u + c / 2)) := by
  refine ⟨commonWZHeightInterval_nonempty hh, ?_⟩
  intro i
  exact containsWZHeightSlab_of_center_bin (D.line i) hc (hdir i)
    (hcenterLower i) (hcenterUpper i)

/-- Readback of a common-slab source into its literal marked fronts. -/
theorem commonWZHeightSlab_graphPoint_mem
    {n : ℕ} (D : FiniteScaleSource n) (I : Set ℝ)
    (hslab : HasCommonWZHeightSlab D I) (i : Fin n)
    {s : ℝ} (hs : s ∈ I) :
    wzGraphPoint (D.line i) s ∈ unitFront {D.line i} :=
  wzGraphPoint_mem_unitFront_singleton (D.line i) I (hslab.2 i) hs

end StickyKakeya4
