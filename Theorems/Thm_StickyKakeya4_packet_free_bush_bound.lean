import Theorems.Thm_StickyKakeya4_separated_bush_fiber
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Packet-free all-target bound for one physical bush

The old collision time is not confined to a packet.  The actual ordered
occurrence remains dominated by the original selector product.  An explicit
measurable affine-line residual and a one-dimensional finite cover yield a
codimension-two estimate; no normalized-neighbor product bound is used.
-/

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4.PacketFreeBushBound

/-- A unit direction when the line is nondegenerate, and zero otherwise. -/
def lineUnit (v : E3) : E3 := ‖v‖⁻¹ • v

/-- The perpendicular base point of the target's affine line. -/
def lineBase (q v : E3) : E3 := q - inner ℝ q (lineUnit v) • lineUnit v

/-- Explicit residual, including the degenerate line with direction zero. -/
def lineResidual (x q v : E3) : E3 :=
  x - (lineBase q v + inner ℝ x (lineUnit v) • lineUnit v)

theorem norm_lineUnit_le_one (v : E3) : ‖lineUnit v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [lineUnit, hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [lineUnit, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

theorem projection_line_direction (v : E3) :
    inner ℝ v (lineUnit v) • lineUnit v = v := by
  by_cases hv : v = 0
  · simp [hv, lineUnit]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp only [lineUnit, real_inner_smul_right, real_inner_self_eq_norm_sq, smul_smul]
    rw [show (‖v‖⁻¹ * ‖v‖ ^ 2) * ‖v‖⁻¹ = 1 by field_simp, one_smul]

theorem lineResidual_eq_projected_error (x q v : E3) (t : ℝ) :
    lineResidual x q v =
      (x - (q + t • v)) -
        inner ℝ (x - (q + t • v)) (lineUnit v) • lineUnit v := by
  simp only [lineResidual, lineBase, inner_sub_left, inner_add_left,
    real_inner_smul_left, sub_smul, add_smul, mul_smul,
    projection_line_direction]
  module

/-- Nearness to any point on the original target line controls the explicit
residual. The factor two avoids any choice of orthogonal coordinates. -/
theorem norm_lineResidual_le (x q v : E3) (δ : ℝ)
    (hnear : ∃ t : ℝ, ‖x - (q + t • v)‖ ≤ δ) :
    ‖lineResidual x q v‖ ≤ 2 * δ := by
  obtain ⟨t, ht⟩ := hnear
  rw [lineResidual_eq_projected_error x q v t]
  have hproj : ‖inner ℝ (x - (q + t • v)) (lineUnit v) • lineUnit v‖ ≤
      ‖x - (q + t • v)‖ := by
    rw [norm_smul]
    calc
      _ ≤ (‖x - (q + t • v)‖ * ‖lineUnit v‖) * ‖lineUnit v‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ ≤ (‖x - (q + t • v)‖ * 1) * 1 := by
        gcongr <;> exact norm_lineUnit_le_one v
      _ = _ := by ring
  exact (norm_sub_le _ _).trans (by linarith)

theorem measurable_lineUnit : Measurable lineUnit := by
  unfold lineUnit
  fun_prop

theorem measurable_lineResidual {X : Type*} [MeasurableSpace X]
    (x q v : X → E3) (hx : Measurable x) (hq : Measurable q) (hv : Measurable v) :
    Measurable (fun z => lineResidual (x z) (q z) (v z)) := by
  have hu : Measurable (fun z => lineUnit (v z)) := measurable_lineUnit.comp hv
  unfold lineResidual lineBase
  fun_prop

/-- The scalar grid has at most `3/δ` points for `0<δ≤1`. -/
theorem scalar_grid_card_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((⌊2 / δ⌋₊ + 1 : ℕ) : ℝ) * δ ≤ 3 := by
  have hf := Nat.floor_le (show 0 ≤ 2 / δ by positivity)
  have hmul := (mul_le_mul_of_nonneg_right hf hδ.le)
  rw [div_mul_cancel₀ _ hδ.ne'] at hmul
  push_cast
  nlinarith

/-- Every parameter in the unit interval lies within one mesh width of a
member of the explicit finite grid. -/
theorem scalar_grid_cover (δ s : ℝ) (hδ : 0 < δ) (hs : |s| ≤ 1) :
    ∃ i ∈ Finset.range (⌊2 / δ⌋₊ + 1), |s - (-1 + (i : ℝ) * δ)| ≤ δ := by
  have hs' := abs_le.mp hs
  let i : ℕ := ⌊(s + 1) / δ⌋₊
  have hnonneg : 0 ≤ (s + 1) / δ := div_nonneg (by linarith) hδ.le
  have hlo : (i : ℝ) ≤ (s + 1) / δ := Nat.floor_le hnonneg
  have hhi : (s + 1) / δ < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hi : i ≤ ⌊2 / δ⌋₊ := Nat.floor_mono (by gcongr; linarith)
  refine ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
  have hlo' := (le_div_iff₀ hδ).mp hlo
  have hhi' := (div_lt_iff₀ hδ).mp hhi
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- A tube in the unit direction ball is covered by the explicit scalar grid.
The centers depend only on the line, rather than on a source point. -/
theorem residual_tube_finite_cover (x q v : E3) (δ : ℝ) (hδ : 0 < δ)
    (hx : ‖x‖ ≤ 1) (hres : ‖lineResidual x q v‖ ≤ 2 * δ) :
    ∃ i ∈ Finset.range (⌊2 / δ⌋₊ + 1),
      x ∈ Metric.closedBall (lineBase q v + (-1 + (i : ℝ) * δ) • lineUnit v)
        (3 * δ) := by
  have hs : |inner ℝ x (lineUnit v)| ≤ 1 := by
    calc
      _ = ‖inner ℝ x (lineUnit v)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ * ‖lineUnit v‖ := norm_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul hx (norm_lineUnit_le_one v) (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  obtain ⟨i, hi, hdist⟩ := scalar_grid_cover δ (inner ℝ x (lineUnit v)) hδ hs
  refine ⟨i, hi, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have heq : x - (lineBase q v + (-1 + (i : ℝ) * δ) • lineUnit v) =
      lineResidual x q v +
        (inner ℝ x (lineUnit v) - (-1 + (i : ℝ) * δ)) • lineUnit v := by
    unfold lineResidual
    module
  rw [heq]
  have hn : ‖(inner ℝ x (lineUnit v) - (-1 + (i : ℝ) * δ)) • lineUnit v‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hdist (norm_lineUnit_le_one v) (norm_nonneg _) hδ.le).trans_eq
      (mul_one δ)
  exact (norm_add_le _ _).trans (by linarith)

/-- Cubic direction-ball density pays each affine-line tube quadratically,
including arbitrary target lines and the degenerate direction-zero case. -/
theorem residual_tube_measure_le_quadratic
    {X : Type*} [MeasurableSpace X] (σ : Measure X) (a : X → E3)
    (hunit : ∀ᵐ z ∂σ, ‖a z‖ ≤ 1) (C : ℝ≥0∞)
    (hdensity : ∀ x : E3, ∀ T : ℝ, 0 ≤ T →
      σ (a ⁻¹' Metric.closedBall x T) ≤ C * ENNReal.ofReal T ^ 3)
    (q v : E3) (δ : ℝ) (hδ : 0 < δ) :
    σ {z | ‖lineResidual (a z) q v‖ ≤ 2 * δ} ≤
      81 * C * ENNReal.ofReal δ ^ 2 := by
  classical
  by_cases hδ1 : δ ≤ 1
  · let n : ℕ := ⌊2 / δ⌋₊ + 1
    let caps : ℕ → Set X := fun i => a ⁻¹' Metric.closedBall
      (lineBase q v + (-1 + (i : ℝ) * δ) • lineUnit v) (3 * δ)
    have hsub : ∀ᵐ z ∂σ,
        z ∈ {z | ‖lineResidual (a z) q v‖ ≤ 2 * δ} →
          z ∈ ⋃ i ∈ Finset.range n, caps i := by
      filter_upwards [hunit] with z hz hres
      obtain ⟨i, hi, hcap⟩ := residual_tube_finite_cover (a z) q v δ hδ hz hres
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hcap⟩⟩
    have hcard : (n : ℝ≥0∞) * ENNReal.ofReal δ ≤ 3 := by
      have hh := ENNReal.ofReal_le_ofReal (scalar_grid_card_bound δ hδ hδ1)
      simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat] using hh
    calc
      _ ≤ σ (⋃ i ∈ Finset.range n, caps i) := measure_mono_ae hsub
      _ ≤ ∑ i ∈ Finset.range n, σ (caps i) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, C * ENNReal.ofReal (3 * δ) ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hdensity _ _ (by positivity)
      _ = (n : ℝ≥0∞) * (C * ENNReal.ofReal (3 * δ) ^ 3) := by simp
      _ = 27 * C * ((n : ℝ≥0∞) * ENNReal.ofReal δ) * ENNReal.ofReal δ ^ 2 := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
        ring
      _ ≤ 27 * C * 3 * ENNReal.ofReal δ ^ 2 := by gcongr
      _ = 81 * C * ENNReal.ofReal δ ^ 2 := by ring
  · have hlarge : 1 ≤ δ := le_of_not_ge hδ1
    have htotal : σ univ ≤ C := by
      calc
        _ ≤ σ (a ⁻¹' Metric.closedBall 0 1) := by
          apply measure_mono_ae
          filter_upwards [hunit] with z hz _hz
          change dist (a z) 0 ≤ 1
          simpa only [dist_zero_right] using hz
        _ ≤ C * ENNReal.ofReal 1 ^ 3 := hdensity 0 1 (by norm_num)
        _ = C := by norm_num
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
      simpa using ENNReal.ofReal_le_ofReal hlarge
    calc
      _ ≤ σ univ := measure_mono (subset_univ _)
      _ ≤ C := htotal
      _ = 1 * C * 1 ^ 2 := by ring
      _ ≤ 81 * C * ENNReal.ofReal δ ^ 2 := by gcongr; norm_num

/-- The old target specifies the base point and line direction; the source
and target are the original ordered endpoints. -/
def lineTubeSet {X : Type*} (a q v : X → E3) (δ : ℝ) : Set (X × X) :=
  {p | ‖lineResidual (a p.1) (q p.2) (v p.2)‖ ≤ 2 * δ}

theorem measurableSet_lineTubeSet {X : Type*} [MeasurableSpace X]
    (a q v : X → E3) (ha : Measurable a) (hq : Measurable q) (hv : Measurable v)
    (δ : ℝ) : MeasurableSet (lineTubeSet a q v δ) := by
  exact measurableSet_le
    (measurable_lineResidual _ _ _ (ha.comp measurable_fst)
      (hq.comp measurable_snd) (hv.comp measurable_snd)).norm measurable_const

/-- Tonelli integrates the uniform source-tube estimate in the actual old
 target. No cap condition is imposed on that target. -/
theorem product_lineTubeSet_le_quadratic
    {X : Type*} [MeasurableSpace X] (σ : Measure X) [SFinite σ]
    (a q v : X → E3) (ha : Measurable a) (hq : Measurable q) (hv : Measurable v)
    (hunit : ∀ᵐ z ∂σ, ‖a z‖ ≤ 1) (C : ℝ≥0∞)
    (hdensity : ∀ x : E3, ∀ T : ℝ, 0 ≤ T →
      σ (a ⁻¹' Metric.closedBall x T) ≤ C * ENNReal.ofReal T ^ 3)
    (δ : ℝ) (hδ : 0 < δ) :
    (σ.prod σ) (lineTubeSet a q v δ) ≤
      (81 * C * ENNReal.ofReal δ ^ 2) * σ univ := by
  rw [Measure.prod_apply_symm (measurableSet_lineTubeSet a q v ha hq hv δ)]
  calc
    (∫⁻ y, σ ((fun x => (x, y)) ⁻¹' lineTubeSet a q v δ) ∂σ) ≤
        ∫⁻ _y, (81 * C * ENNReal.ofReal δ ^ 2) ∂σ := by
      apply lintegral_mono
      intro y
      exact residual_tube_measure_le_quadratic σ a hunit C hdensity (q y) (v y) δ hδ
    _ = _ := lintegral_const _

/-- One physical source bush pays every original old target with codimension
two, without any old-time packet hypothesis. The old collision error `r`
and the original ordered product domination are retained verbatim.

This is a one-bush estimate. It asserts neither a varying-center summation
bound nor a global sticky Kakeya conclusion. -/
theorem physical_packet_free_occurrence_le_quadratic
    {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (Γ : Measure (X × X))
    (a b : X → E3) (ha : Measurable a) (hb : Measurable b)
    (hunit : ∀ᵐ z ∂σ, ‖a z‖ ≤ 1)
    (c : E3) (s₀ R r g : ℝ) (C : ℝ≥0∞)
    (hscale : 0 < R + r) (hg : 0 < g)
    (hdom : Γ ≤ σ.prod σ)
    (hphysical : ∀ᵐ p ∂Γ, ∃ t : ℝ,
      ‖b p.1 + s₀ • a p.1 - c‖ ≤ R ∧
      ‖(b p.1 - b p.2) + t • (a p.1 - a p.2)‖ ≤ r ∧
      g ≤ |t - s₀|)
    (hdensity : ∀ x : E3, ∀ T : ℝ, 0 ≤ T →
      σ (a ⁻¹' Metric.closedBall x T) ≤ C * ENNReal.ofReal T ^ 3) :
    Γ univ ≤ (81 * C * ENNReal.ofReal ((R + r) / g) ^ 2) * σ univ := by
  let v : X → E3 := fun z => b z + s₀ • a z - c
  have hv : Measurable v := by dsimp [v]; fun_prop
  let δ : ℝ := (R + r) / g
  have hδ : 0 < δ := div_pos hscale hg
  have hs : MeasurableSet (lineTubeSet a a v δ) :=
    measurableSet_lineTubeSet a a v ha ha hv δ
  have hsupport : Γ (lineTubeSet a a v δ)ᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [hphysical] with p hp
    obtain ⟨t, hbush, hcollision, hsep⟩ := hp
    exact norm_lineResidual_le (a p.1) (a p.2) (v p.2) δ
      (SeparatedBushFiber.source_near_target_line (a p.1) (b p.1)
        (a p.2) (b p.2) c s₀ t R r g hbush hcollision hg hsep)
  have hmass : Γ univ = Γ (lineTubeSet a a v δ) := by
    simpa only [hsupport, add_zero] using (measure_add_measure_compl (μ := Γ) hs).symm
  rw [hmass]
  exact (hdom _).trans
    (product_lineTubeSet_le_quadratic σ a a v ha ha hv hunit C hdensity δ hδ)

end StickyKakeya4.PacketFreeBushBound
