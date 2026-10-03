import Theorems.Thm_StickyKakeya4_actual_slope_source

set_option autoImplicit false
set_option warningAsError true

/-!
# A native marked unit line from a graph and a center height

This is a small adapter into the existing `MarkedLine`, `northSlopeDirection`,
`ActualSlopeSource.heightPoint`, and native WZ common-slab framework. It does
not introduce a second line or segment type. All segment and window facts
below follow from the actual graph parameters.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace StickyKakeya4.NativeGraphMarkedLine

/-- The canonical marked unit line with graph `b + s • a` and marked center at height `s₀`. -/
def ofGraph (a b : E3) (s₀ : ℝ) : MarkedLine :=
  let θ : E4 := northSlopeDirection a
  let x₀ : E4 := ActualSlopeSource.heightPoint (b + s₀ • a) s₀
  ((θ, x₀ - inner ℝ x₀ θ • θ), inner ℝ x₀ θ)

@[simp] theorem direction_ofGraph (a b : E3) (s₀ : ℝ) :
    direction (ofGraph a b s₀) = (northSlopeDirection a : E4) := rfl

/-- The orthogonal-offset/mark pair defines a valid native unit line. -/
theorem valid (a b : E3) (s₀ : ℝ) : IsValidLine (ofGraph a b s₀) := by
  constructor
  · exact (northSlopeDirection a).property
  · change inner ℝ
      (ActualSlopeSource.heightPoint (b + s₀ • a) s₀ -
        inner ℝ (ActualSlopeSource.heightPoint (b + s₀ • a) s₀)
          (northSlopeDirection a : E4) • (northSlopeDirection a : E4))
      (northSlopeDirection a : E4) = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (northSlopeDirection a).property]
    ring

@[simp] theorem direction_castSucc (a b : E3) (s₀ : ℝ) (j : Fin 3) :
    direction (ofGraph a b s₀) j.castSucc = ‖northSlopeLift a‖⁻¹ * a j := by
  change (‖northSlopeLift a‖⁻¹ • northSlopeLift a) j.castSucc = _
  simp only [PiLp.smul_apply, smul_eq_mul, northSlopeLift_castSucc]

@[simp] theorem direction_fourth (a b : E3) (s₀ : ℝ) :
    direction (ofGraph a b s₀) (3 : Fin 4) = ‖northSlopeLift a‖⁻¹ :=
  ActualSlopeSource.northSlopeDirection_fourth a

theorem direction_fourth_pos (a b : E3) (s₀ : ℝ) :
    0 < direction (ofGraph a b s₀) (3 : Fin 4) := by
  rw [direction_fourth]
  exact inv_pos.mpr (zero_lt_one.trans_le (northSlopeLift_norm_ge_one a))

/-- The affine mark retains the chosen physical graph center exactly. -/
theorem rawFrontParam_eq_center (a b : E3) (s₀ u : ℝ) :
    rawFrontParam (ofGraph a b s₀, u) =
      ActualSlopeSource.heightPoint (b + s₀ • a) s₀ +
        u • direction (ofGraph a b s₀) := by
  dsimp [rawFrontParam, ofGraph, direction, offset, mark]
  module

@[simp] theorem center_height (a b : E3) (s₀ : ℝ) :
    wzMarkedCenterHeight (ofGraph a b s₀) = s₀ := by
  unfold wzMarkedCenterHeight
  rw [rawFrontParam_eq_center, zero_smul, add_zero]
  exact ActualSlopeSource.heightPoint_last (b + s₀ • a) s₀

/-- Exact graph occurrence at its native relative unit-speed parameter. -/
theorem rawFrontParam_graph (a b : E3) (s₀ s : ℝ) :
    rawFrontParam
      (ofGraph a b s₀, (s - s₀) / direction (ofGraph a b s₀) (3 : Fin 4)) =
        ActualSlopeSource.heightPoint (b + s • a) s := by
  have hdir : ‖northSlopeLift a‖ • direction (ofGraph a b s₀) = northSlopeLift a :=
    NormedSpace.norm_smul_normalize _
  rw [rawFrontParam_eq_center, direction_fourth, div_inv_eq_mul, mul_smul, hdir]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      ActualSlopeSource.heightPoint_last, northSlopeLift_last]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      ActualSlopeSource.heightPoint_castSucc, northSlopeLift_castSucc]
    ring

/-- The graph-height parameter agrees with the existing native chart parameter. -/
theorem relative_graph_time (a b : E3) (s₀ s : ℝ) :
    wzGraphTime (ofGraph a b s₀) s - mark (ofGraph a b s₀) =
      (s - s₀) / direction (ofGraph a b s₀) (3 : Fin 4) := by
  rw [wzGraphTime_sub_mark_eq (ofGraph a b s₀) s
    (ne_of_gt (direction_fourth_pos a b s₀)), center_height]

/-- Identification with the repository's existing fixed-height graph point. -/
theorem wzGraphPoint_eq_heightPoint (a b : E3) (s₀ s : ℝ) :
    wzGraphPoint (ofGraph a b s₀) s = ActualSlopeSource.heightPoint (b + s • a) s := by
  rw [wzGraphPoint_eq_rawFrontParam, relative_graph_time]
  exact rawFrontParam_graph a b s₀ s

/-- Coordinatewise unit slope bounds imply the sharp four-dimensional lift bound. -/
theorem lift_norm_sq_le_four (a : E3) (ha : ∀ j, |a j| ≤ 1) :
    ‖northSlopeLift a‖ ^ 2 ≤ 4 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [northSlopeLift_castSucc, northSlopeLift_last, Fin.sum_univ_three]
  have h0 := (sq_le_one_iff_abs_le_one (a (0 : Fin 3))).mpr (ha 0)
  have h1 := (sq_le_one_iff_abs_le_one (a (1 : Fin 3))).mpr (ha 1)
  have h2 := (sq_le_one_iff_abs_le_one (a (2 : Fin 3))).mpr (ha 2)
  nlinarith

theorem lift_norm_le_two (a : E3) (ha : ∀ j, |a j| ≤ 1) :
    ‖northSlopeLift a‖ ≤ 2 := by
  nlinarith [lift_norm_sq_le_four a ha, norm_nonneg (northSlopeLift a)]

/-- The actual normalized direction lies in the native fixed north chart. -/
theorem direction_fourth_ge_half (a b : E3) (s₀ : ℝ) (ha : ∀ j, |a j| ≤ 1) :
    (1 / 2 : ℝ) ≤ direction (ofGraph a b s₀) (3 : Fin 4) := by
  have hn : 0 < ‖northSlopeLift a‖ := zero_lt_one.trans_le (northSlopeLift_norm_ge_one a)
  rw [direction_fourth, inv_eq_one_div]
  apply (le_div_iff₀ hn).mpr
  nlinarith [lift_norm_le_two a ha]

/-- Heights within one quarter of the mark fit inside the genuine unit segment. -/
theorem relative_parameter_le_half (a b : E3) (s₀ s : ℝ)
    (ha : ∀ j, |a j| ≤ 1) (hs : |s - s₀| ≤ 1 / 4) :
    |(s - s₀) / direction (ofGraph a b s₀) (3 : Fin 4)| ≤ 1 / 2 := by
  rw [abs_div, abs_of_pos (direction_fourth_pos a b s₀)]
  apply (div_le_iff₀ (direction_fourth_pos a b s₀)).mpr
  linarith [direction_fourth_ge_half a b s₀ ha]

/-- The eighth-height window leaves a quarter unit-speed buffer at both segment ends. -/
theorem relative_parameter_le_quarter (a b : E3) (s₀ s : ℝ)
    (ha : ∀ j, |a j| ≤ 1) (hs : |s - s₀| ≤ 1 / 8) :
    |(s - s₀) / direction (ofGraph a b s₀) (3 : Fin 4)| ≤ 1 / 4 := by
  rw [abs_div, abs_of_pos (direction_fourth_pos a b s₀)]
  apply (div_le_iff₀ (direction_fourth_pos a b s₀)).mpr
  linarith [direction_fourth_ge_half a b s₀ ha]

/-- Literal graph-point containment in the marked unit front. -/
theorem graphPoint_mem_unitFront (a b : E3) (s₀ s : ℝ)
    (ha : ∀ j, |a j| ≤ 1) (hs : |s - s₀| ≤ 1 / 4) :
    ActualSlopeSource.heightPoint (b + s • a) s ∈ unitFront {ofGraph a b s₀} := by
  rw [← rawFrontParam_graph a b s₀ s]
  exact rawFrontParam_mem_unitFront_singleton (ofGraph a b s₀)
    (abs_le.mp (relative_parameter_le_half a b s₀ s ha hs))

/-- An explicit native occurrence witness with a quarter-parameter endpoint buffer. -/
theorem graphPoint_has_buffered_parameter (a b : E3) (s₀ s : ℝ)
    (ha : ∀ j, |a j| ≤ 1) (hs : |s - s₀| ≤ 1 / 8) :
    ∃ u : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      |(u : ℝ)| ≤ 1 / 4 ∧
      rawFrontParam (ofGraph a b s₀, (u : ℝ)) = ActualSlopeSource.heightPoint (b + s • a) s := by
  have hu := relative_parameter_le_quarter a b s₀ s ha hs
  refine ⟨⟨(s - s₀) / direction (ofGraph a b s₀) (3 : Fin 4), ?_⟩, hu, ?_⟩
  · obtain ⟨hl, hr⟩ := abs_le.mp hu
    constructor <;> linarith
  · exact rawFrontParam_graph a b s₀ s

/-- The existing center-bin theorem provides the exact common height slab. -/
theorem contains_height_slab (a b : E3) (s₀ : ℝ) (ha : ∀ j, |a j| ≤ 1) :
    ContainsWZHeightSlab (ofGraph a b s₀) (Set.Icc (s₀ - 1 / 4) (s₀ + 1 / 4)) := by
  have h := containsWZHeightSlab_of_center_bin (ofGraph a b s₀)
    (c := (1 / 2 : ℝ)) (u := s₀) (h := 0) (by norm_num)
    (direction_fourth_ge_half a b s₀ ha)
    (by rw [center_height]) (by rw [center_height]; simp)
  simpa only [add_zero, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using h

/-- Every native source built from these actual graph lines has a fixed common slab. -/
theorem family_hasNormalizedWZGraphSlab {n : ℕ} (D : FiniteScaleSource n)
    (a b : Fin n → E3) (s₀ : ℝ)
    (hline : ∀ i, D.line i = ofGraph (a i) (b i) s₀)
    (ha : ∀ i j, |a i j| ≤ 1) : HasNormalizedWZGraphSlab D := by
  refine ⟨?_, s₀ - 1 / 4, s₀ + 1 / 4, by linarith, ?_⟩
  · intro i
    rw [hline i]
    exact direction_fourth_ge_half (a i) (b i) s₀ (ha i)
  · refine ⟨Set.nonempty_Icc.mpr (by linarith), ?_⟩
    intro i
    rw [hline i]
    exact contains_height_slab (a i) (b i) s₀ (ha i)

/-- Full unit-segment height normalization is derived, not provided as a window certificate. -/
theorem family_hasFixedWZGraphNormalization {n : ℕ} (D : FiniteScaleSource n)
    (a b : Fin n → E3) (s₀ : ℝ)
    (hline : ∀ i, D.line i = ofGraph (a i) (b i) s₀)
    (ha : ∀ i j, |a i j| ≤ 1) : HasFixedWZGraphNormalization D := by
  exact hasFixedWZGraphNormalization_of_normalizedSlab D
    (fun i => by rw [hline i]; exact valid (a i) (b i) s₀)
    (family_hasNormalizedWZGraphSlab D a b s₀ hline ha)

end StickyKakeya4.NativeGraphMarkedLine
