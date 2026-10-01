import Mathlib
import Theorems.Thm_StickyKakeya4_dimension_witness_extraction
import Theorems.Thm_StickyKakeya4_wang_zakharov_finite_interface

open scoped ENNReal NNReal
open MeasureTheory

noncomputable section

namespace StickyKakeya4

/-!
The numerical part of the cover-adapted Wang--Zakharov readback.

The manuscript chooses

`alpha = theta / 4`, `beta = 2 * theta`, `kappa = 3 * theta`

and then takes `4 * theta < eta`.  The lemmas below record, without an
external axiom, every exponent comparison used by the pruning, convex-Wolff,
and shading steps.  The second lemma is the countable-layer pigeonhole step
used to choose a Hausdorff-cover scale carrying more mass than its prescribed
summable threshold.
-/

/-- Unpack vanishing Hausdorff measure into the countable fine cover used by
the cover-adapted readback.  The cost is written exactly as it occurs in
`Measure.hausdorffMeasure_apply`; empty covering sets contribute zero. -/
theorem exists_small_diameter_cover_of_hausdorffMeasure_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : Set X) (d : ℝ)
    (hzero : MeasureTheory.Measure.hausdorffMeasure d s = 0)
    {r epsilon : ENNReal} (hr : 0 < r) (hepsilon : 0 < epsilon) :
    ∃ cover : ℕ → Set X,
      s ⊆ ⋃ n, cover n ∧
      (∀ n, Metric.ediam (cover n) ≤ r) ∧
      (∑' n, ⨆ _ : (cover n).Nonempty,
        (Metric.ediam (cover n)).rpow d) < epsilon := by
  let coverCost : (ℕ → Set X) → ENNReal := fun cover =>
    ∑' n, ⨆ _ : (cover n).Nonempty,
      (Metric.ediam (cover n)).rpow d
  have hcomponent :
      (⨅ cover : ℕ → Set X,
        ⨅ _ : s ⊆ ⋃ n, cover n,
          ⨅ _ : ∀ n, Metric.ediam (cover n) ≤ r,
            coverCost cover) = 0 := by
    apply le_antisymm
    · calc
        (⨅ cover : ℕ → Set X,
          ⨅ _ : s ⊆ ⋃ n, cover n,
            ⨅ _ : ∀ n, Metric.ediam (cover n) ≤ r,
              coverCost cover) ≤
            ⨆ (rho : ENNReal) (_ : 0 < rho),
              ⨅ cover : ℕ → Set X,
                ⨅ _ : s ⊆ ⋃ n, cover n,
                  ⨅ _ : ∀ n, Metric.ediam (cover n) ≤ rho,
                    coverCost cover := by
              exact le_iSup_of_le r (le_iSup_of_le hr (le_refl _))
        _ = MeasureTheory.Measure.hausdorffMeasure d s := by
          rw [MeasureTheory.Measure.hausdorffMeasure_apply]
          rfl
        _ = 0 := hzero
    · exact bot_le
  have hlt :
      (⨅ cover : ℕ → Set X,
        ⨅ _ : s ⊆ ⋃ n, cover n,
          ⨅ _ : ∀ n, Metric.ediam (cover n) ≤ r,
            coverCost cover) < epsilon := by
    rw [hcomponent]
    exact hepsilon
  simpa only [coverCost, iInf_lt_iff, exists_prop] using hlt

/-- The dimension hypothesis used in the contradiction argument already
produces the fine low-cost cover required by the finite-scale readback.  The
strict inequality is essential: it is exactly the hypothesis of
`hausdorffMeasure_of_dimH_lt`, so no endpoint attainment is being assumed. -/
theorem exists_small_diameter_cover_of_dimH_lt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : Set X) {d : NNReal} (hdim : dimH s < (d : ENNReal))
    {r epsilon : ENNReal} (hr : 0 < r) (hepsilon : 0 < epsilon) :
    ∃ cover : ℕ → Set X,
      s ⊆ ⋃ n, cover n ∧
      (∀ n, Metric.ediam (cover n) ≤ r) ∧
      (∑' n, ⨆ _ : (cover n).Nonempty,
        (Metric.ediam (cover n)).rpow (d : ℝ)) < epsilon := by
  exact exists_small_diameter_cover_of_hausdorffMeasure_eq_zero
    s (d : ℝ) (hausdorffMeasure_of_dimH_lt hdim) hr hepsilon

/-- Measurable replacement of a Hausdorff-cover member: close-thicken it by
its own diameter.  This contains the original member, is closed, and changes
the diameter by at most the fixed factor three. -/
def closedDiameterThickening {X : Type*} [MetricSpace X]
    (cover : ℕ → Set X) (i : ℕ) : Set X :=
  Metric.cthickening ((Metric.ediam (cover i)).toNNReal : ℝ) (cover i)

theorem measurableSet_closedDiameterThickening
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (cover : ℕ → Set X) (i : ℕ) :
    MeasurableSet (closedDiameterThickening cover i) := by
  exact Metric.isClosed_cthickening.measurableSet

theorem cover_subset_closedDiameterThickening
    {X : Type*} [MetricSpace X]
    (cover : ℕ → Set X) (i : ℕ) :
    cover i ⊆ closedDiameterThickening cover i := by
  exact Metric.self_subset_cthickening (cover i)

theorem ediam_closedDiameterThickening_le_three_mul
    {X : Type*} [MetricSpace X]
    (cover : ℕ → Set X) (i : ℕ)
    (hfinite : Metric.ediam (cover i) ≠ ⊤) :
    Metric.ediam (closedDiameterThickening cover i) ≤
      3 * Metric.ediam (cover i) := by
  calc
    Metric.ediam (closedDiameterThickening cover i) ≤
        Metric.ediam (cover i) +
          2 * ((Metric.ediam (cover i)).toNNReal : ENNReal) := by
      exact Metric.ediam_cthickening_le
        (Metric.ediam (cover i)).toNNReal
    _ = 3 * Metric.ediam (cover i) := by
      rw [ENNReal.coe_toNNReal hfinite]
      ring

/-- Replacing every member by its closed diameter thickening preserves the
covering property while making the whole countable cover measurable. -/
theorem subset_iUnion_closedDiameterThickening
    {X : Type*} [MetricSpace X]
    (s : Set X) (cover : ℕ → Set X)
    (hcover : s ⊆ ⋃ i, cover i) :
  s ⊆ ⋃ i, closedDiameterThickening cover i := by
  intro x hx
  have hxcover := hcover hx
  simp only [Set.mem_iUnion] at hxcover ⊢
  obtain ⟨i, hxi⟩ := hxcover
  exact ⟨i, cover_subset_closedDiameterThickening cover i hxi⟩

/-- A countable fine cover of a compact set can be converted into the finite
family needed by a finite-scale incidence estimate.  Each nonempty covering
piece is placed inside a ball centred in that piece; the positive inflation
`tau` makes these balls open, so compactness supplies a finite subcover. -/
theorem exists_finite_inflated_ball_cover_of_compact
    {X : Type*} [MetricSpace X] [Nonempty X]
    {s : Set X} (hs : IsCompact s)
    (cover : ℕ → Set X) (hcover : s ⊆ ⋃ n, cover n)
    {r : ENNReal} (hrtop : r ≠ ⊤)
    (hdiam : ∀ n, Metric.ediam (cover n) ≤ r)
    {tau : ℝ} (htau : 0 < tau) :
    ∃ F : Finset ℕ, ∃ center : ℕ → X,
      s ⊆ ⋃ n ∈ (F : Set ℕ),
        Metric.ball (center n) ((Metric.ediam (cover n)).toReal + tau) ∧
      ∀ n ∈ F,
        (Metric.ediam (cover n)).toReal + tau ≤ r.toReal + tau := by
  classical
  let center : ℕ → X := fun n =>
    if h : (cover n).Nonempty then h.choose else Classical.choice inferInstance
  have hcenter : ∀ n, (cover n).Nonempty → center n ∈ cover n := by
    intro n hn
    unfold center
    split
    · next h => exact h.choose_spec
    · next h => exact (h hn).elim
  have hpiece : ∀ n,
      cover n ⊆ Metric.ball (center n)
        ((Metric.ediam (cover n)).toReal + tau) := by
    intro n x hx
    have hn : (cover n).Nonempty := ⟨x, hx⟩
    have hdiamtop : Metric.ediam (cover n) ≠ ⊤ :=
      ne_top_of_le_ne_top hrtop (hdiam n)
    have hed : edist x (center n) ≤ Metric.ediam (cover n) :=
      Metric.edist_le_ediam_of_mem hx (hcenter n hn)
    have hdist : dist x (center n) ≤ (Metric.ediam (cover n)).toReal := by
      simpa [edist_dist] using ENNReal.toReal_mono hdiamtop hed
    rw [Metric.mem_ball]
    linarith
  have hballs :
      s ⊆ ⋃ n, Metric.ball (center n)
        ((Metric.ediam (cover n)).toReal + tau) := by
    intro x hx
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover ⊢
    obtain ⟨n, hxn⟩ := hxcover
    exact ⟨n, hpiece n hxn⟩
  obtain ⟨F, hF⟩ := hs.elim_finite_subcover
    (fun n => Metric.ball (center n)
      ((Metric.ediam (cover n)).toReal + tau))
    (fun _ => Metric.isOpen_ball) hballs
  refine ⟨F, center, hF, ?_⟩
  intro n hn
  have hreal : (Metric.ediam (cover n)).toReal ≤ r.toReal :=
    ENNReal.toReal_mono hrtop (hdiam n)
  linarith

/-- Combined Hausdorff-to-finite-scale readback.  Under a strict dimension
upper bound, a compact set has a low-cost countable cover together with a
finite inflated-ball subcover at the same prescribed outer scale.  Thus the
finite family is extracted without discarding the Hausdorff cost ledger. -/
theorem exists_finite_low_cost_ball_cover_of_compact_dimH_lt
    {X : Type*} [MetricSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (s : Set X) (hs : IsCompact s)
    {d : NNReal} (hdim : dimH s < (d : ENNReal))
    {r epsilon : ENNReal} (hr : 0 < r) (hrtop : r ≠ ⊤)
    (hepsilon : 0 < epsilon) {tau : ℝ} (htau : 0 < tau) :
    ∃ cover : ℕ → Set X,
      (∀ n, Metric.ediam (cover n) ≤ r) ∧
      (∑' n, ⨆ _ : (cover n).Nonempty,
        (Metric.ediam (cover n)).rpow (d : ℝ)) < epsilon ∧
      ∃ F : Finset ℕ, ∃ center : ℕ → X,
        s ⊆ ⋃ n ∈ (F : Set ℕ),
          Metric.ball (center n)
            ((Metric.ediam (cover n)).toReal + tau) ∧
        ∀ n ∈ F,
          (Metric.ediam (cover n)).toReal + tau ≤ r.toReal + tau := by
  obtain ⟨cover, hcover, hdiam, hcost⟩ :=
    exists_small_diameter_cover_of_dimH_lt s hdim hr hepsilon
  obtain ⟨F, center, hfinite, hradius⟩ :=
    exists_finite_inflated_ball_cover_of_compact hs cover hcover
      hrtop hdiam htau
  exact ⟨cover, hdiam, hcost, F, center, hfinite, hradius⟩

/-- A strict sub-four-dimensional hypothesis contains a quantitative exponent
gap.  The chosen Hausdorff exponent is `d = 4 - chi`, with `chi > 0`, and is
still strictly above the actual Hausdorff dimension. -/
theorem exists_hausdorff_exponent_gap_below_four
    {X : Type*} [MetricSpace X] (s : Set X)
    (hdim : dimH s < (4 : ENNReal)) :
    ∃ chi : ℝ, 0 < chi ∧ chi < 4 ∧
      ∃ d : NNReal, (d : ℝ) = 4 - chi ∧
        dimH s < (d : ENNReal) := by
  have hfourTop : (4 : ENNReal) ≠ ⊤ := by norm_num
  have hdimTop : dimH s ≠ ⊤ :=
    ne_top_of_lt (hdim.trans (show (4 : ENNReal) < ⊤ by norm_num))
  have hdimRealLt : (dimH s).toReal < 4 :=
    (ENNReal.toReal_lt_toReal hdimTop hfourTop).2 hdim
  let chi : ℝ := (4 - (dimH s).toReal) / 2
  have hchi : 0 < chi := by
    dsimp [chi]
    linarith
  have hchiFour : chi < 4 := by
    have hdimRealNonneg : 0 ≤ (dimH s).toReal := ENNReal.toReal_nonneg
    dsimp [chi]
    linarith
  let d : NNReal := ⟨4 - chi, le_of_lt (sub_pos.mpr hchiFour)⟩
  have hdReal : (d : ℝ) = 4 - chi := rfl
  have hdimRealD : (dimH s).toReal < (d : ℝ) := by
    rw [hdReal]
    dsimp [chi]
    linarith
  have hdTop : (d : ENNReal) ≠ ⊤ := by simp
  have hdimD : dimH s < (d : ENNReal) :=
    (ENNReal.toReal_lt_toReal hdimTop hdTop).1 (by simpa using hdimRealD)
  exact ⟨chi, hchi, hchiFour, d, hdReal, hdimD⟩

/-- All strict exponent inequalities in the cover-adapted readback follow
from the single choice `4 * theta < eta`. -/
theorem wz_parameter_bookkeeping {theta eta : ℝ}
    (htheta : 0 < theta) (heta : 4 * theta < eta) :
    let alpha := theta / 4
    let beta := 2 * theta
    let kappa := 3 * theta
    0 < alpha ∧
      0 < beta ∧
      0 < kappa ∧
      kappa > alpha + beta ∧
      kappa < eta ∧
      beta < eta := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- If the total prescribed threshold mass is strictly smaller than the
actual total mass, at least one layer beats its threshold. -/
theorem exists_cover_layer_above_threshold
    (threshold mass : ℕ → ENNReal)
    (hstrict : (∑' n, threshold n) < ∑' n, mass n) :
    ∃ n, threshold n < mass n := by
  by_contra hnone
  push_neg at hnone
  exact (not_le_of_gt hstrict) (ENNReal.tsum_le_tsum hnone)

/-- Probability normalization turns the preceding abstract comparison into
the Hausdorff-cover layer selection used in the paper. -/
theorem exists_probability_cover_layer_above_threshold
    (threshold mass : ℕ → ENNReal)
    (hmass : (∑' n, mass n) = 1)
    (hthreshold : (∑' n, threshold n) < 1) :
    ∃ n, threshold n < mass n := by
  apply exists_cover_layer_above_threshold threshold mass
  simpa [hmass] using hthreshold

/-- Every positive extended-real radius at most one belongs to a dyadic
annulus.  Choosing the least power below the radius supplies both sides of
the annular bound. -/
theorem exists_dyadic_ennreal_scale {r : ENNReal}
    (hr : 0 < r) (hrone : r ≤ 1) :
    ∃ n : ℕ,
      ((2 : ENNReal)⁻¹) ^ (n + 1) < r ∧
      r ≤ ((2 : ENNReal)⁻¹) ^ n := by
  have hrTop : r ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hrone
  have hrNN : 0 < r.toNNReal := ENNReal.toNNReal_pos hr.ne' hrTop
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((2 : NNReal)⁻¹) ^ k < r.toNNReal :=
    NNReal.exists_pow_lt_of_lt_one hrNN (by norm_num)
  have hk' : ((2 : ENNReal)⁻¹) ^ k < r := by
    rw [← ENNReal.coe_toNNReal hrTop]
    have hcoe := ENNReal.coe_lt_coe.mpr hk
    change ((↑((2 : NNReal)⁻¹) : ENNReal) ^ k <
      (↑r.toNNReal : ENNReal)) at hcoe
    have hbaseEq : (↑((2 : NNReal)⁻¹) : ENNReal) =
        (2 : ENNReal)⁻¹ := by norm_num
    rw [hbaseEq] at hcoe
    exact hcoe
  have hex : ∃ k : ℕ, ((2 : ENNReal)⁻¹) ^ k < r := ⟨k, hk'⟩
  let k := Nat.find hex
  have hk : ((2 : ENNReal)⁻¹) ^ k < r := Nat.find_spec hex
  have hkZero : k ≠ 0 := by
    intro hzero
    rw [hzero, pow_zero] at hk
    exact (not_lt_of_ge hrone) hk
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkZero
  refine ⟨n, ?_, ?_⟩
  · simpa [hn] using hk
  apply le_of_not_gt
  intro hnlt
  have hminimal : k ≤ n := Nat.find_min' hex hnlt
  rw [hn] at hminimal
  omega

/-- Total dyadic scale label.  Only the positive, at-most-one branch is used
in the Hausdorff cover; defining the other branch as zero makes the label a
plain function suitable for countable grouping. -/
noncomputable def dyadicENNRealScale (r : ENNReal) : ℕ :=
  if h : 0 < r ∧ r ≤ 1 then
    (exists_dyadic_ennreal_scale h.1 h.2).choose
  else 0

theorem dyadicENNRealScale_spec {r : ENNReal}
    (hr : 0 < r) (hrone : r ≤ 1) :
    ((2 : ENNReal)⁻¹) ^ (dyadicENNRealScale r + 1) < r ∧
      r ≤ ((2 : ENNReal)⁻¹) ^ dyadicENNRealScale r := by
  rw [dyadicENNRealScale, dif_pos ⟨hr, hrone⟩]
  exact (exists_dyadic_ennreal_scale hr hrone).choose_spec

/-- Ratio of the geometric mass thresholds at successive dyadic Hausdorff
scales.  It is exactly `(1/2)^theta`. -/
def dyadicMassRatio (theta : ℝ) : ENNReal :=
  ((2 : ENNReal)⁻¹).rpow theta

theorem dyadicMassRatio_lt_one {theta : ℝ} (htheta : 0 < theta) :
    dyadicMassRatio theta < 1 := by
  exact ENNReal.rpow_lt_one (by norm_num) htheta

theorem dyadicMassRatio_pos (theta : ℝ) :
    0 < dyadicMassRatio theta := by
  exact ENNReal.rpow_pos (by norm_num) (by norm_num)

/-- Summable threshold used in the scale pigeonhole.  The prefactor makes
the entire series have mass exactly `1/2`; apart from this harmless fixed
constant, the `n`th threshold is the manuscript's `2^(-theta n)` scale. -/
def dyadicMassThreshold (theta : ℝ) (n : ℕ) : ENNReal :=
  ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹) *
    (dyadicMassRatio theta) ^ n

/-- The geometric factor in the dyadic mass threshold is exactly the
`theta`-power of the corresponding dyadic physical scale. -/
theorem dyadicMassRatio_pow_eq_scale_rpow (theta : ℝ) (n : ℕ) :
    (dyadicMassRatio theta) ^ n =
      (((2 : ENNReal)⁻¹) ^ n).rpow theta := by
  unfold dyadicMassRatio
  calc
    (((2 : ENNReal)⁻¹).rpow theta) ^ n =
        ((2 : ENNReal)⁻¹).rpow (theta * (n : ℝ)) :=
      (ENNReal.rpow_mul_natCast ((2 : ENNReal)⁻¹) theta n).symm
    _ = ((2 : ENNReal)⁻¹).rpow ((n : ℝ) * theta) := by ring
    _ = (((2 : ENNReal)⁻¹) ^ n).rpow theta :=
      ENNReal.rpow_natCast_mul ((2 : ENNReal)⁻¹) n theta

/-- Exact power form of the summable dyadic layer threshold. -/
theorem dyadicMassThreshold_eq_prefactor_mul_scale_rpow
    (theta : ℝ) (n : ℕ) :
    dyadicMassThreshold theta n =
      ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹) *
        (((2 : ENNReal)⁻¹) ^ n).rpow theta := by
  unfold dyadicMassThreshold
  rw [dyadicMassRatio_pow_eq_scale_rpow]

/-- The Hausdorff-layer mass threshold supplies the active-fibre density
required at WZ exponent `3 * theta`.  Only the extra `2 * theta` power must
be absorbed into the fixed prefactor; the remaining `theta` power is exactly
the mass already guaranteed by the dyadic pigeonhole threshold. -/
theorem dyadicMassThreshold_dominates_active_fibre_requirement
    (theta : ℝ) (n : ℕ) (delta : ℝ) (C mass : ENNReal)
    (htheta : 0 < theta)
    (hdelta : delta = ((((2 : ENNReal)⁻¹) ^ n).toReal))
    (hsmall :
      C * (ENNReal.ofReal delta).rpow (2 * theta) ≤
        ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹) / 2)
    (hmass : dyadicMassThreshold theta n ≤ mass) :
    C * (ENNReal.ofReal delta).rpow (3 * theta) ≤ mass / 2 := by
  let q : ENNReal := ((2 : ENNReal)⁻¹) ^ n
  have hqTop : q ≠ ⊤ := by simp [q]
  have hofRealDelta : ENNReal.ofReal delta = q := by
    rw [hdelta]
    exact ENNReal.ofReal_toReal hqTop
  have hsplit :
      (ENNReal.ofReal delta).rpow (3 * theta) =
        (ENNReal.ofReal delta).rpow (2 * theta) *
          (ENNReal.ofReal delta).rpow theta := by
    rw [show 3 * theta = 2 * theta + theta by ring]
    exact ENNReal.rpow_add_of_nonneg (2 * theta) theta
      (by positivity) htheta.le
  have hthreshold :
      dyadicMassThreshold theta n =
        ((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹) *
          (ENNReal.ofReal delta).rpow theta := by
    rw [dyadicMassThreshold_eq_prefactor_mul_scale_rpow, hofRealDelta]
  rw [hsplit, ← mul_assoc]
  calc
    (C * (ENNReal.ofReal delta).rpow (2 * theta)) *
          (ENNReal.ofReal delta).rpow theta ≤
        (((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹) / 2) *
          (ENNReal.ofReal delta).rpow theta := by
      gcongr
    _ = dyadicMassThreshold theta n / 2 := by
      rw [hthreshold]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ mass / 2 := by gcongr

theorem dyadicMassThreshold_pos {theta : ℝ} (htheta : 0 < theta) (n : ℕ) :
    0 < dyadicMassThreshold theta n := by
  unfold dyadicMassThreshold
  have hq : dyadicMassRatio theta < 1 := dyadicMassRatio_lt_one htheta
  apply bot_lt_iff_ne_bot.mpr
  exact mul_ne_zero
    (mul_ne_zero (tsub_pos_iff_lt.mpr hq).ne' (by norm_num))
    (pow_ne_zero n (dyadicMassRatio_pos theta).ne')

theorem tsum_dyadicMassThreshold {theta : ℝ} (htheta : 0 < theta) :
    (∑' n, dyadicMassThreshold theta n) = (2 : ENNReal)⁻¹ := by
  let q := dyadicMassRatio theta
  have hq : q < 1 := dyadicMassRatio_lt_one htheta
  have hsubNe : 1 - q ≠ 0 := by
    exact (tsub_pos_iff_lt.mpr hq).ne'
  have hsubTop : 1 - q ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by norm_num) (tsub_le_self : 1 - q ≤ 1)
  calc
    (∑' n, dyadicMassThreshold theta n) =
        ((1 - q) * (2 : ENNReal)⁻¹) * (1 - q)⁻¹ := by
      simp only [dyadicMassThreshold, q, ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
    _ = (2 : ENNReal)⁻¹ * ((1 - q) * (1 - q)⁻¹) := by ac_rfl
    _ = (2 : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hsubNe hsubTop, mul_one]

theorem tsum_dyadicMassThreshold_lt_one {theta : ℝ} (htheta : 0 < theta) :
    (∑' n, dyadicMassThreshold theta n) < 1 := by
  rw [tsum_dyadicMassThreshold htheta]
  norm_num

/-- A non-atomic measure vanishes on every subsingleton set, including the
empty set.  This formulation avoids requiring the set itself to be
measurable. -/
theorem measure_eq_zero_of_subsingleton
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (hsingleton : ∀ x, mu {x} = 0)
    {s : Set X} (hsub : s.Subsingleton) :
    mu s = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact measure_empty
  · obtain ⟨x, hx⟩ := hs
    apply measure_mono_null _ (hsingleton x)
    intro y hy
    exact Set.mem_singleton_iff.mpr (hsub hy hx)

/-- The union of all zero-diameter members of a countable cover has zero mass
for a non-atomic measure.  Hence the positive dyadic scale groups retain the
entire probability mass. -/
theorem measure_iUnion_cover_ediam_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (hsingleton : ∀ x, mu {x} = 0)
    (cover : ℕ → Set X) :
    mu (⋃ i : {i : ℕ // Metric.ediam (cover i) = 0}, cover i.1) = 0 := by
  apply measure_iUnion_null
  intro i
  exact measure_eq_zero_of_subsingleton mu hsingleton
    (Metric.ediam_eq_zero_iff.mp i.property)

/-- Zero original diameter remains zero after the closed-diameter
thickening, so the measurable replacement does not manufacture mass at the
discarded zero scale. -/
theorem measure_iUnion_closedDiameterThickening_ediam_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (hsingleton : ∀ x, mu {x} = 0)
    (cover : ℕ → Set X) :
    mu (⋃ i : {i : ℕ // Metric.ediam (cover i) = 0},
      closedDiameterThickening cover i.1) = 0 := by
  apply measure_iUnion_null
  intro i
  apply measure_eq_zero_of_subsingleton mu hsingleton
  rw [← Metric.ediam_eq_zero_iff]
  have hfinite : Metric.ediam (cover i.1) ≠ ⊤ := by
    rw [i.property]
    exact ENNReal.zero_ne_top
  have hbound :=
    ediam_closedDiameterThickening_le_three_mul cover i.1 hfinite
  rw [i.property, mul_zero] at hbound
  exact nonpos_iff_eq_zero.mp hbound

/-- If a measure is supported on a set covered by the original Hausdorff
family, then after measurable diameter thickening and removal of the
zero-diameter members it is still supported on the positive-diameter part.
This is the exact support statement needed before dyadic scale grouping. -/
theorem measure_compl_iUnion_positive_closedDiameterThickening_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (hsingleton : ∀ x, mu {x} = 0)
    (s : Set X) (hsupport : mu sᶜ = 0)
    (cover : ℕ → Set X) (hcover : s ⊆ ⋃ i, cover i) :
    mu ((⋃ i : {i : ℕ // Metric.ediam (cover i) ≠ 0},
      closedDiameterThickening cover i.1)ᶜ) = 0 := by
  let allPieces : Set X := ⋃ i, closedDiameterThickening cover i
  let positivePieces : Set X :=
    ⋃ i : {i : ℕ // Metric.ediam (cover i) ≠ 0},
      closedDiameterThickening cover i.1
  let zeroPieces : Set X :=
    ⋃ i : {i : ℕ // Metric.ediam (cover i) = 0},
      closedDiameterThickening cover i.1
  have hcoverAll : s ⊆ allPieces :=
    subset_iUnion_closedDiameterThickening s cover hcover
  have hAllCompl : mu allPiecesᶜ = 0 := by
    apply measure_mono_null _ hsupport
    intro x hxall hxs
    exact hxall (hcoverAll hxs)
  have hZero : mu zeroPieces = 0 := by
    exact measure_iUnion_closedDiameterThickening_ediam_eq_zero
      mu hsingleton cover
  apply measure_mono_null _ (measure_union_null hAllCompl hZero)
  intro x hx
  by_cases hxall : x ∈ allPieces
  · right
    simp only [allPieces, Set.mem_iUnion] at hxall
    obtain ⟨i, hxi⟩ := hxall
    have hzero : Metric.ediam (cover i) = 0 := by
      by_contra hne
      apply hx
      simp only [Set.mem_iUnion]
      exact ⟨⟨i, hne⟩, hxi⟩
    simp only [zeroPieces, Set.mem_iUnion]
    exact ⟨⟨i, hzero⟩, hxi⟩
  · exact Or.inl hxall

/-- Countably indexed measurable cover obtained by retaining the closed
diameter thickening at positive original diameter and replacing every
zero-diameter entry by the empty set. -/
def positiveClosedDiameterCover {X : Type*} [MetricSpace X]
    (cover : ℕ → Set X) (i : ℕ) : Set X :=
  if Metric.ediam (cover i) ≠ 0 then
    closedDiameterThickening cover i
  else ∅

theorem measurableSet_positiveClosedDiameterCover
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (cover : ℕ → Set X) (i : ℕ) :
    MeasurableSet (positiveClosedDiameterCover cover i) := by
  unfold positiveClosedDiameterCover
  split
  · exact measurableSet_closedDiameterThickening cover i
  · exact MeasurableSet.empty

/-- The indices of the nonempty measurable replacements belonging to one
dyadic diameter layer. -/
def positiveDyadicCoverLayerIndices {X : Type*} [MetricSpace X]
    (cover : ℕ → Set X) (n : ℕ) : Set ℕ :=
  {i |
    dyadicENNRealScale (Metric.ediam (cover i)) = n ∧
      (positiveClosedDiameterCover cover i).Nonempty}

/-- If an `ENNReal` series has finite total mass, only finitely many terms
can stay above a fixed positive threshold. -/
theorem finite_setOf_le_of_tsum_ne_top
    {ι : Type*} (f : ι → ENNReal) (hfinite : (∑' i, f i) ≠ ⊤)
    {c : ENNReal} (hc : 0 < c) :
    {i | c ≤ f i}.Finite := by
  have hevent : ∀ᶠ i in Filter.cofinite, f i < c :=
    (ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hfinite).eventually_lt_const hc
  rw [Filter.eventually_cofinite] at hevent
  simpa only [not_lt] using hevent

/-- A finite-cost Hausdorff cover has only finitely many nonempty members in
each positive dyadic diameter layer.  This is the finiteness needed before
turning a first-assigned layer into a finite-scale covering input. -/
theorem finite_positiveDyadicCoverLayerIndices
    {X : Type*} [MetricSpace X] (cover : ℕ → Set X)
    {d : NNReal} (hd : 0 < d)
    (hdiam : ∀ i, Metric.ediam (cover i) ≤ 1)
    (hcostFinite :
      (∑' i, ⨆ _ : (cover i).Nonempty,
        (Metric.ediam (cover i)).rpow (d : ℝ)) ≠ ⊤)
    (n : ℕ) :
    (positiveDyadicCoverLayerIndices cover n).Finite := by
  let cost : ℕ → ENNReal := fun i =>
    ⨆ _ : (cover i).Nonempty,
      (Metric.ediam (cover i)).rpow (d : ℝ)
  let threshold : ENNReal :=
    (((2 : ENNReal)⁻¹) ^ (n + 1)).rpow (d : ℝ)
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hbasePos : 0 < ((2 : ENNReal)⁻¹) ^ (n + 1) := by
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
  have hbaseTop : ((2 : ENNReal)⁻¹) ^ (n + 1) ≠ ⊤ := by norm_num
  have hthresholdPos : 0 < threshold := by
    exact ENNReal.rpow_pos hbasePos hbaseTop
  have hfinite : {i | threshold ≤ cost i}.Finite :=
    finite_setOf_le_of_tsum_ne_top cost hcostFinite hthresholdPos
  apply hfinite.subset
  intro i hi
  rcases hi with ⟨hscale, hpositiveNonempty⟩
  have hdiamNe : Metric.ediam (cover i) ≠ 0 := by
    intro hzero
    simpa [positiveClosedDiameterCover, hzero] using hpositiveNonempty
  have hdiamPos : 0 < Metric.ediam (cover i) :=
    bot_lt_iff_ne_bot.mpr hdiamNe
  have hlower :
      ((2 : ENNReal)⁻¹) ^ (n + 1) < Metric.ediam (cover i) := by
    have hspec := dyadicENNRealScale_spec hdiamPos (hdiam i)
    rw [hscale] at hspec
    exact hspec.1
  have hcoverNonempty : (cover i).Nonempty := by
    by_contra hempty
    have hcoverEmpty : cover i = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    apply hdiamNe
    simp [hcoverEmpty]
  have hpow : threshold < (Metric.ediam (cover i)).rpow (d : ℝ) :=
    ENNReal.rpow_lt_rpow hlower hdReal
  exact hpow.le.trans (le_iSup (fun _ : (cover i).Nonempty =>
    (Metric.ediam (cover i)).rpow (d : ℝ)) hcoverNonempty)

/-- Quantitative version of dyadic-layer finiteness: the number of nonempty
members in one layer, multiplied by the least possible `d`-cost of a member
of that layer, is strictly below the total Hausdorff-cover budget. -/
theorem positiveDyadicCoverLayerIndices_ncard_mul_rpow_lt
    {X : Type*} [MetricSpace X] (cover : ℕ → Set X)
    {d : NNReal} (hd : 0 < d)
    (hdiam : ∀ i, Metric.ediam (cover i) ≤ 1)
    {epsilon : ENNReal}
    (hcost :
      (∑' i, ⨆ _ : (cover i).Nonempty,
        (Metric.ediam (cover i)).rpow (d : ℝ)) < epsilon)
    (n : ℕ) :
    ((positiveDyadicCoverLayerIndices cover n).ncard : ENNReal) *
        (((2 : ENNReal)⁻¹) ^ (n + 1)).rpow (d : ℝ) < epsilon := by
  let cost : ℕ → ENNReal := fun i =>
    ⨆ _ : (cover i).Nonempty,
      (Metric.ediam (cover i)).rpow (d : ℝ)
  let threshold : ENNReal :=
    (((2 : ENNReal)⁻¹) ^ (n + 1)).rpow (d : ℝ)
  have hcostFinite : (∑' i, cost i) ≠ ⊤ := by
    exact ne_of_lt (hcost.trans_le le_top)
  have hlayerFinite : (positiveDyadicCoverLayerIndices cover n).Finite :=
    finite_positiveDyadicCoverLayerIndices cover hd hdiam hcostFinite n
  rw [Set.ncard_eq_toFinset_card _ hlayerFinite]
  calc
    (hlayerFinite.toFinset.card : ENNReal) * threshold =
        ∑ i ∈ hlayerFinite.toFinset, threshold := by simp
    _ ≤ ∑ i ∈ hlayerFinite.toFinset, cost i := by
      apply Finset.sum_le_sum
      intro i hi
      have hiLayer : i ∈ positiveDyadicCoverLayerIndices cover n :=
        hlayerFinite.mem_toFinset.mp hi
      rcases hiLayer with ⟨hscale, hpositiveNonempty⟩
      have hdiamNe : Metric.ediam (cover i) ≠ 0 := by
        intro hzero
        simpa [positiveClosedDiameterCover, hzero] using hpositiveNonempty
      have hdiamPos : 0 < Metric.ediam (cover i) :=
        bot_lt_iff_ne_bot.mpr hdiamNe
      have hlower :
          ((2 : ENNReal)⁻¹) ^ (n + 1) < Metric.ediam (cover i) := by
        have hspec := dyadicENNRealScale_spec hdiamPos (hdiam i)
        rw [hscale] at hspec
        exact hspec.1
      have hcoverNonempty : (cover i).Nonempty := by
        by_contra hempty
        have hcoverEmpty : cover i = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
        apply hdiamNe
        simp [hcoverEmpty]
      have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
      have hpow : threshold < (Metric.ediam (cover i)).rpow (d : ℝ) :=
        ENNReal.rpow_lt_rpow hlower hdReal
      exact hpow.le.trans (le_iSup (fun _ : (cover i).Nonempty =>
        (Metric.ediam (cover i)).rpow (d : ℝ)) hcoverNonempty)
    _ ≤ ∑' i, cost i := ENNReal.sum_le_tsum hlayerFinite.toFinset
    _ < epsilon := hcost

theorem iUnion_positiveClosedDiameterCover
    {X : Type*} [MetricSpace X] (cover : ℕ → Set X) :
    (⋃ i, positiveClosedDiameterCover cover i) =
      ⋃ i : {i : ℕ // Metric.ediam (cover i) ≠ 0},
        closedDiameterThickening cover i.1 := by
  classical
  ext x
  simp [positiveClosedDiameterCover]

theorem measure_compl_iUnion_positiveClosedDiameterCover_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : Measure X) (hsingleton : ∀ x, mu {x} = 0)
    (s : Set X) (hsupport : mu sᶜ = 0)
    (cover : ℕ → Set X) (hcover : s ⊆ ⋃ i, cover i) :
    mu ((⋃ i, positiveClosedDiameterCover cover i)ᶜ) = 0 := by
  rw [iUnion_positiveClosedDiameterCover]
  exact measure_compl_iUnion_positive_closedDiameterThickening_eq_zero
    mu hsingleton s hsupport cover hcover

/-- A countable measurable cover of a probability support can be assigned by
first occurrence without losing mass.  Consequently every summable threshold
of total mass below one is beaten by one actual, measurable, disjoint cover
piece.  This is the measure-theoretic form of the manuscript's instruction
to assign each front occurrence to the first covering set containing it. -/
theorem exists_disjointed_probability_cover_piece_above_threshold
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (cover : ℕ → Set X) (hcoverMeasurable : ∀ n, MeasurableSet (cover n))
    (hsupport : mu ((⋃ n, cover n)ᶜ) = 0)
    (threshold : ℕ → ENNReal)
    (hthreshold : (∑' n, threshold n) < 1) :
    ∃ n,
      threshold n < mu (disjointed cover n) ∧
      MeasurableSet (disjointed cover n) ∧
      disjointed cover n ⊆ cover n := by
  have hdisjointMeasurable : ∀ n, MeasurableSet (disjointed cover n) :=
    fun n => MeasurableSet.disjointed hcoverMeasurable n
  have hmass : (∑' n, mu (disjointed cover n)) = 1 := by
    rw [← measure_iUnion (disjoint_disjointed cover) hdisjointMeasurable]
    rw [iUnion_disjointed]
    let U : Set X := ⋃ n, cover n
    have hU : MeasurableSet U := MeasurableSet.iUnion hcoverMeasurable
    calc
      mu U = mu U + mu Uᶜ := by rw [hsupport, add_zero]
      _ = mu (U ∪ Uᶜ) := (measure_union disjoint_compl_right hU.compl).symm
      _ = mu Set.univ := by rw [Set.union_compl_self]
      _ = 1 := measure_univ
  obtain ⟨n, hn⟩ :=
    exists_probability_cover_layer_above_threshold threshold
      (fun n => mu (disjointed cover n)) hmass hthreshold
  exact ⟨n, hn, hdisjointMeasurable n, disjointed_subset cover n⟩

/-- Group the first-occurrence pieces of a countable cover by an arbitrary
natural-number scale label. -/
def disjointedCoverScaleGroup {X : Type*}
    (cover : ℕ → Set X) (scale : ℕ → ℕ) (n : ℕ) : Set X :=
  ⋃ i : {i : ℕ // scale i = n}, disjointed cover i.1

theorem measurableSet_disjointedCoverScaleGroup
    {X : Type*} [MeasurableSpace X]
    (cover : ℕ → Set X) (scale : ℕ → ℕ)
    (hcoverMeasurable : ∀ i, MeasurableSet (cover i)) (n : ℕ) :
    MeasurableSet (disjointedCoverScaleGroup cover scale n) := by
  exact MeasurableSet.iUnion fun i =>
    MeasurableSet.disjointed hcoverMeasurable i.1

theorem disjointedCoverScaleGroup_pairwise_disjoint
    {X : Type*} (cover : ℕ → Set X) (scale : ℕ → ℕ) :
    Pairwise (fun n m => Disjoint
      (disjointedCoverScaleGroup cover scale n)
      (disjointedCoverScaleGroup cover scale m)) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro x hxn hxm
  simp only [disjointedCoverScaleGroup, Set.mem_iUnion] at hxn hxm
  obtain ⟨i, hxi⟩ := hxn
  obtain ⟨j, hxj⟩ := hxm
  have hij : (i : ℕ) ≠ (j : ℕ) := by
    intro hij
    apply hnm
    calc
      n = scale (i : ℕ) := i.property.symm
      _ = scale (j : ℕ) := congrArg scale hij
      _ = m := j.property
  exact Set.disjoint_left.mp (disjoint_disjointed cover hij) hxi hxj

theorem iUnion_disjointedCoverScaleGroup
    {X : Type*} (cover : ℕ → Set X) (scale : ℕ → ℕ) :
    (⋃ n, disjointedCoverScaleGroup cover scale n) = ⋃ i, cover i := by
  calc
    (⋃ n, disjointedCoverScaleGroup cover scale n) =
        ⋃ i, disjointed cover i := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_iUnion] at hx ⊢
        obtain ⟨n, hn⟩ := hx
        change x ∈ ⋃ i : {i : ℕ // scale i = n}, disjointed cover i.1 at hn
        simp only [Set.mem_iUnion] at hn
        obtain ⟨i, hxi⟩ := hn
        exact ⟨i.1, hxi⟩
      · intro hx
        simp only [Set.mem_iUnion] at hx ⊢
        obtain ⟨i, hxi⟩ := hx
        refine ⟨scale i, ?_⟩
        change x ∈ ⋃ j : {j : ℕ // scale j = scale i}, disjointed cover j.1
        simp only [Set.mem_iUnion]
        exact ⟨⟨i, rfl⟩, hxi⟩
    _ = ⋃ i, cover i := iUnion_disjointed

/-- A finite nonempty dyadic layer gives an explicit finite open-ball cover
of its first-assigned union.  The factor four absorbs the factor-three
diameter increase from the measurable closed thickening and makes the final
ball inequality strict. -/
theorem exists_finite_centers_cover_disjointed_dyadic_group
    {X : Type*} [MetricSpace X] (cover : ℕ → Set X)
    (hdiam : ∀ i, Metric.ediam (cover i) ≤ 1)
    (n : ℕ)
    (hlayerFinite : (positiveDyadicCoverLayerIndices cover n).Finite)
    (hscale : ∀ i,
      dyadicENNRealScale (Metric.ediam (cover i)) = n →
      (positiveClosedDiameterCover cover i).Nonempty →
        Metric.ediam (cover i) ≤ ((2 : ENNReal)⁻¹) ^ n) :
    ∃ centers : Finset X,
      coversAtRadius
        (disjointedCoverScaleGroup
          (positiveClosedDiameterCover cover)
          (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n)
        (4 * ((((2 : ENNReal)⁻¹) ^ n).toReal)) centers ∧
      centers.card ≤ (positiveDyadicCoverLayerIndices cover n).ncard := by
  classical
  let I := {i : ℕ // i ∈ positiveDyadicCoverLayerIndices cover n}
  letI : Fintype I := hlayerFinite.fintype
  let center : I → X := fun i => Classical.choose i.property.2
  let centers : Finset X := Finset.univ.image center
  refine ⟨centers, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hxPositive : x ∈ positiveClosedDiameterCover cover i.1 :=
      disjointed_subset (positiveClosedDiameterCover cover) i.1 hxi
    have hiLayer : i.1 ∈ positiveDyadicCoverLayerIndices cover n :=
      ⟨i.property, ⟨x, hxPositive⟩⟩
    let j : I := ⟨i.1, hiLayer⟩
    have hcenterPositive :
        center j ∈ positiveClosedDiameterCover cover i.1 :=
      Classical.choose_spec j.property.2
    have hcenterMem : center j ∈ centers := by
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨center j, Set.mem_iUnion.mpr ⟨hcenterMem, ?_⟩⟩
    rw [Metric.mem_ball]
    have hdiamNe : Metric.ediam (cover i.1) ≠ 0 := by
      intro hzero
      simpa [positiveClosedDiameterCover, hzero] using hiLayer.2
    have hdiamTop : Metric.ediam (cover i.1) ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) (hdiam i.1)
    have hedPositive :
        Metric.ediam (positiveClosedDiameterCover cover i.1) ≤
          3 * (((2 : ENNReal)⁻¹) ^ n) := by
      rw [positiveClosedDiameterCover, if_pos hdiamNe]
      calc
        Metric.ediam (closedDiameterThickening cover i.1) ≤
            3 * Metric.ediam (cover i.1) :=
          ediam_closedDiameterThickening_le_three_mul cover i.1 hdiamTop
        _ ≤ 3 * (((2 : ENNReal)⁻¹) ^ n) := by
          gcongr
          exact hscale i.1 i.property hiLayer.2
    have hscaleTop : 3 * (((2 : ENNReal)⁻¹) ^ n) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (by norm_num)
    have hedPositiveTop :
        Metric.ediam (positiveClosedDiameterCover cover i.1) ≠ ⊤ :=
      ne_top_of_le_ne_top hscaleTop hedPositive
    have hqPos : 0 < (((2 : ENNReal)⁻¹) ^ n) := by
      exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
    have hqTop : (((2 : ENNReal)⁻¹) ^ n) ≠ ⊤ := by norm_num
    calc
      dist x (center j) ≤
          Metric.diam (positiveClosedDiameterCover cover i.1) :=
        Metric.dist_le_diam_of_mem' hedPositiveTop hxPositive hcenterPositive
      _ ≤ (3 * (((2 : ENNReal)⁻¹) ^ n)).toReal :=
        ENNReal.toReal_mono hscaleTop hedPositive
      _ = 3 * ((((2 : ENNReal)⁻¹) ^ n).toReal) := by
        rw [ENNReal.toReal_mul]
        norm_num
      _ < 4 * ((((2 : ENNReal)⁻¹) ^ n).toReal) := by
        have hqReal : 0 < ((((2 : ENNReal)⁻¹) ^ n).toReal) :=
          ENNReal.toReal_pos hqPos.ne' hqTop
        linarith
  · calc
      centers.card ≤ (Finset.univ : Finset I).card := by
        dsimp [centers]
        exact Finset.card_image_le
      _ = (positiveDyadicCoverLayerIndices cover n).ncard := by
        simp [I]

/-- Scale-grouped form of the Hausdorff-layer pigeonhole step.  The output is
an actual measurable union of first-assigned cover pieces bearing one common
scale label, and its probability mass beats the prescribed scale threshold. -/
theorem exists_disjointed_probability_cover_scale_group_above_threshold
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (cover : ℕ → Set X) (scale : ℕ → ℕ)
    (hcoverMeasurable : ∀ i, MeasurableSet (cover i))
    (hsupport : mu ((⋃ i, cover i)ᶜ) = 0)
    (threshold : ℕ → ENNReal)
    (hthreshold : (∑' n, threshold n) < 1) :
    ∃ n,
      threshold n < mu (disjointedCoverScaleGroup cover scale n) ∧
      MeasurableSet (disjointedCoverScaleGroup cover scale n) := by
  have hgroupMeasurable : ∀ n,
      MeasurableSet (disjointedCoverScaleGroup cover scale n) :=
    measurableSet_disjointedCoverScaleGroup cover scale hcoverMeasurable
  have hmass :
      (∑' n, mu (disjointedCoverScaleGroup cover scale n)) = 1 := by
    rw [← measure_iUnion
      (disjointedCoverScaleGroup_pairwise_disjoint cover scale)
      hgroupMeasurable]
    rw [iUnion_disjointedCoverScaleGroup]
    let U : Set X := ⋃ i, cover i
    have hU : MeasurableSet U := MeasurableSet.iUnion hcoverMeasurable
    calc
      mu U = mu U + mu Uᶜ := by rw [hsupport, add_zero]
      _ = mu (U ∪ Uᶜ) := (measure_union disjoint_compl_right hU.compl).symm
      _ = mu Set.univ := by rw [Set.union_compl_self]
      _ = 1 := measure_univ
  obtain ⟨n, hn⟩ :=
    exists_probability_cover_layer_above_threshold threshold
      (fun n => mu (disjointedCoverScaleGroup cover scale n))
      hmass hthreshold
  exact ⟨n, hn, hgroupMeasurable n⟩

/-- Complete measurable dyadic-layer selection for a fine Hausdorff cover.
Zero-diameter entries have first been replaced by the empty set.  The selected
first-occurrence scale group beats the prescribed summable threshold, and
every nonempty member assigned to that group has original diameter in the
same dyadic annulus. -/
theorem exists_positive_dyadic_cover_scale_group_above_threshold
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hsingleton : ∀ x, mu {x} = 0)
    (s : Set X) (hsupport : mu sᶜ = 0)
    (cover : ℕ → Set X) (hcover : s ⊆ ⋃ i, cover i)
    (hdiam : ∀ i, Metric.ediam (cover i) ≤ 1)
    (threshold : ℕ → ENNReal)
    (hthreshold : (∑' n, threshold n) < 1) :
    ∃ n,
      threshold n <
        mu (disjointedCoverScaleGroup
          (positiveClosedDiameterCover cover)
          (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n) ∧
      MeasurableSet
        (disjointedCoverScaleGroup
          (positiveClosedDiameterCover cover)
          (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n) ∧
      ∀ i,
        dyadicENNRealScale (Metric.ediam (cover i)) = n →
        (positiveClosedDiameterCover cover i).Nonempty →
          ((2 : ENNReal)⁻¹) ^ (n + 1) < Metric.ediam (cover i) ∧
          Metric.ediam (cover i) ≤ ((2 : ENNReal)⁻¹) ^ n := by
  let positiveCover : ℕ → Set X := positiveClosedDiameterCover cover
  let scale : ℕ → ℕ :=
    fun i => dyadicENNRealScale (Metric.ediam (cover i))
  have hpositiveMeasurable : ∀ i, MeasurableSet (positiveCover i) :=
    measurableSet_positiveClosedDiameterCover cover
  have hpositiveSupport : mu ((⋃ i, positiveCover i)ᶜ) = 0 := by
    exact measure_compl_iUnion_positiveClosedDiameterCover_eq_zero
      mu hsingleton s hsupport cover hcover
  obtain ⟨n, hmass, hgroupMeasurable⟩ :=
    exists_disjointed_probability_cover_scale_group_above_threshold
      mu positiveCover scale hpositiveMeasurable hpositiveSupport
        threshold hthreshold
  refine ⟨n, hmass, hgroupMeasurable, ?_⟩
  intro i hscale hnonempty
  have hdiamNe : Metric.ediam (cover i) ≠ 0 := by
    intro hzero
    simpa [positiveCover, positiveClosedDiameterCover, hzero] using hnonempty
  have hdiamPos : 0 < Metric.ediam (cover i) :=
    bot_lt_iff_ne_bot.mpr hdiamNe
  have hspec := dyadicENNRealScale_spec hdiamPos (hdiam i)
  change dyadicENNRealScale (Metric.ediam (cover i)) = n at hscale
  simpa [hscale] using hspec

/-- Power-threshold specialization of the preceding measurable layer
selection.  The selected layer has probability strictly larger than a fixed
positive constant times `2^(-theta n)`. -/
theorem exists_positive_dyadic_cover_scale_group_with_power_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (hsingleton : ∀ x, mu {x} = 0)
    (s : Set X) (hsupport : mu sᶜ = 0)
    (cover : ℕ → Set X) (hcover : s ⊆ ⋃ i, cover i)
    (hdiam : ∀ i, Metric.ediam (cover i) ≤ 1)
    {theta : ℝ} (htheta : 0 < theta) :
    ∃ n,
      dyadicMassThreshold theta n <
        mu (disjointedCoverScaleGroup
          (positiveClosedDiameterCover cover)
          (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n) ∧
      MeasurableSet
        (disjointedCoverScaleGroup
          (positiveClosedDiameterCover cover)
          (fun i => dyadicENNRealScale (Metric.ediam (cover i))) n) ∧
      ∀ i,
        dyadicENNRealScale (Metric.ediam (cover i)) = n →
        (positiveClosedDiameterCover cover i).Nonempty →
          ((2 : ENNReal)⁻¹) ^ (n + 1) < Metric.ediam (cover i) ∧
          Metric.ediam (cover i) ≤ ((2 : ENNReal)⁻¹) ^ n := by
  exact exists_positive_dyadic_cover_scale_group_above_threshold
    mu hsingleton s hsupport cover hcover hdiam
      (dyadicMassThreshold theta) (tsum_dyadicMassThreshold_lt_one htheta)

/-- Finite form of the active-direction truncation in the Hausdorff-layer
readback.  If `weight` is a probability distribution and `activity i` is a
number in `[0,1]`, then the indices whose activity is at least half of the
weighted mean retain at least half of that mean in probability weight. -/
theorem finite_active_direction_weight_lower_bound
    {ι : Type*} [Fintype ι]
    (weight activity : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (hactivityNonneg : ∀ i, 0 ≤ activity i)
    (hactivityOne : ∀ i, activity i ≤ 1) :
    let mass := ∑ i, weight i * activity i
    mass / 2 ≤
      ∑ i ∈ (Finset.univ.filter fun i => mass / 2 ≤ activity i),
        weight i := by
  classical
  dsimp
  let mass : ℝ := ∑ i, weight i * activity i
  let active : Finset ι :=
    Finset.univ.filter fun i => mass / 2 ≤ activity i
  have hmassNonneg : 0 ≤ mass := by
    dsimp [mass]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hweight i) (hactivityNonneg i)
  have hactiveTerm :
      ∑ i ∈ active, weight i * activity i ≤
        ∑ i ∈ active, weight i := by
    apply Finset.sum_le_sum
    intro i hi
    simpa using mul_le_of_le_one_right (hweight i) (hactivityOne i)
  have hinactiveTerm :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
          weight i * activity i ≤
        mass / 2 *
          ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
            weight i := by
    calc
      ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
          weight i * activity i ≤
          ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
            weight i * (mass / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (le_of_not_ge (Finset.mem_filter.mp hi).2) (hweight i)
      _ = mass / 2 *
          ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
            weight i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hinactiveWeight :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
          weight i ≤ 1 := by
    rw [← hweightSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro i hi hnot
      exact hweight i
  have hinactiveHalf :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
          weight i * activity i ≤ mass / 2 := by
    calc
      ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
          weight i * activity i ≤
          mass / 2 *
            ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
              weight i := hinactiveTerm
      _ ≤ mass / 2 * 1 :=
        mul_le_mul_of_nonneg_left hinactiveWeight (by positivity)
      _ = mass / 2 := by ring
  have hsplitActivity :
      mass =
        (∑ i ∈ active, weight i * activity i) +
          ∑ i ∈ Finset.univ.filter (fun i => ¬ mass / 2 ≤ activity i),
            weight i * activity i := by
    dsimp [mass]
    simpa [active] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => mass / 2 ≤ activity i)
        (fun i => weight i * activity i)).symm
  have hmassUpper :
      mass ≤ (∑ i ∈ active, weight i) + mass / 2 := by
    calc
      mass =
          (∑ i ∈ active, weight i * activity i) +
            ∑ i ∈ Finset.univ.filter
                (fun i => ¬ mass / 2 ≤ activity i),
              weight i * activity i := hsplitActivity
      _ ≤ (∑ i ∈ active, weight i) + mass / 2 :=
        add_le_add hactiveTerm hinactiveHalf
  change mass / 2 ≤ ∑ i ∈ active, weight i
  linarith

/-- If every direction cell has weight at most `cap`, a retained active
weight forces the corresponding lower bound on the number of active cells. -/
theorem finite_active_cell_cardinality_lower_bound
    {ι : Type*} (active : Finset ι) (weight : ι → ℝ)
    (cap retainedWeight : ℝ)
    (hweightCap : ∀ i ∈ active, weight i ≤ cap)
    (hretained : retainedWeight ≤ ∑ i ∈ active, weight i) :
    retainedWeight ≤ active.card * cap := by
  calc
    retainedWeight ≤ ∑ i ∈ active, weight i := hretained
    _ ≤ ∑ _i ∈ active, cap := by
      apply Finset.sum_le_sum
      intro i hi
      exact hweightCap i hi
    _ = active.card * cap := by simp

/-- Coefficient-generic conversion of an extended-real half-mass/cap estimate
into the real power lower bound consumed by carrier pruning.  The factor `16`
is exactly `2` from the half-mass truncation times `2^3` from the direction
cap at radius `2 * delta`. -/
theorem active_family_real_card_lower_bound_with_coefficient
    {ι : Type*} (active : Finset ι)
    {delta beta : ℝ} {lowerConstant mass cap : ENNReal}
    (hdelta : 0 < delta)
    (hlowerTop : lowerConstant ≠ ⊤)
    (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hmass : lowerConstant * (ENNReal.ofReal delta).rpow beta ≤ mass)
    (hcount : mass / 2 ≤
      (active.card : ENNReal) *
        (cap * (ENNReal.ofReal (2 * delta)) ^ 3)) :
    (lowerConstant.toReal / (16 * cap.toReal)) * delta ^ (-3 + beta) ≤
      (active.card : ℝ) := by
  let x : ENNReal := ENNReal.ofReal delta
  have hxZero : x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hxTop : x ≠ ⊤ := ENNReal.ofReal_ne_top
  have hleftTop : lowerConstant * x.rpow beta / 2 ≠ ⊤ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top hlowerTop
        (ENNReal.rpow_ne_top_of_ne_zero hxZero hxTop)) (by norm_num)
  have hrightTop :
      (active.card : ENNReal) *
          (cap * (ENNReal.ofReal (2 * delta)) ^ 3) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top hcapTop
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  have hscaled : lowerConstant * x.rpow beta / 2 ≤
      (active.card : ENNReal) *
        (cap * (ENNReal.ofReal (2 * delta)) ^ 3) := by
    exact (ENNReal.div_le_div_right hmass 2).trans hcount
  have hreal :=
    (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hscaled
  have hxReal : x.toReal = delta := by
    simpa [x] using (ENNReal.toReal_ofReal hdelta.le)
  have hreal' :
      lowerConstant.toReal * delta ^ beta / 2 ≤
        (active.card : ℝ) * (cap.toReal * (2 * delta) ^ 3) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      show (x.rpow beta).toReal = x.toReal ^ beta from
        (ENNReal.toReal_rpow x beta).symm,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow] at hreal
    norm_num at hreal
    rw [hxReal] at hreal
    exact hreal
  have hcapReal : 0 < cap.toReal := ENNReal.toReal_pos hcapZero hcapTop
  have hdeltaCube : 0 < delta ^ (3 : ℕ) := pow_pos hdelta 3
  have hmassReal :
      lowerConstant.toReal * delta ^ beta ≤
        (active.card : ℝ) * (16 * cap.toReal * delta ^ (3 : ℕ)) := by
    nlinarith [hreal']
  have hdenPos : 0 < 16 * cap.toReal * delta ^ (3 : ℕ) := by positivity
  calc
    (lowerConstant.toReal / (16 * cap.toReal)) * delta ^ (-3 + beta) =
        (lowerConstant.toReal * delta ^ beta) /
          (16 * cap.toReal * delta ^ (3 : ℕ)) := by
      rw [show -3 + beta = beta - 3 by ring, Real.rpow_sub hdelta]
      field_simp
      <;> ring_nf
      <;> exact congrArg (fun z : ℝ => lowerConstant.toReal * z)
        (Real.rpow_natCast delta 3).symm
    _ ≤ (active.card : ℝ) :=
      (div_le_iff₀ hdenPos).2 (by simpa [mul_assoc] using hmassReal)

/-- Unit-coefficient specialization retained for direct power lower bounds. -/
theorem active_family_real_card_lower_bound
    {ι : Type*} (active : Finset ι)
    {delta beta : ℝ} {mass cap : ENNReal}
    (hdelta : 0 < delta)
    (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hmass : (ENNReal.ofReal delta).rpow beta ≤ mass)
    (hcount : mass / 2 ≤
      (active.card : ENNReal) *
        (cap * (ENNReal.ofReal (2 * delta)) ^ 3)) :
    (1 / (16 * cap.toReal)) * delta ^ (-3 + beta) ≤
      (active.card : ℝ) := by
  simpa using
    (active_family_real_card_lower_bound_with_coefficient active hdelta
      (lowerConstant := (1 : ENNReal)) (by norm_num) hcapZero hcapTop
      (by simpa using hmass) hcount)

/-- The selected dyadic Hausdorff layer supplies the exact real cardinality
lower bound required by the packing-three pruning theorem, including the
positive summability prefactor rather than silently discarding it. -/
theorem dyadic_mass_threshold_active_family_real_card_lower_bound
    {ι : Type*} (theta : ℝ) (n : ℕ) (active : Finset ι)
    {mass cap : ENNReal}
    (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hmass : dyadicMassThreshold theta n ≤ mass)
    (hcount : mass / 2 ≤
      (active.card : ENNReal) *
        (cap * (ENNReal.ofReal
          (2 * ((((2 : ENNReal)⁻¹) ^ n).toReal))) ^ 3)) :
    ((((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹).toReal) /
        (16 * cap.toReal)) *
      ((((2 : ENNReal)⁻¹) ^ n).toReal) ^ (-3 + theta) ≤
        (active.card : ℝ) := by
  let qENN : ENNReal := ((2 : ENNReal)⁻¹) ^ n
  let q : ℝ := qENN.toReal
  let lowerConstant : ENNReal :=
    (1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹
  have hqZero : qENN ≠ 0 := by simp [qENN]
  have hqTop : qENN ≠ ⊤ := by simp [qENN]
  have hq : 0 < q := ENNReal.toReal_pos hqZero hqTop
  have hlowerTop : lowerConstant ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top (by norm_num)
        (tsub_le_self : 1 - dyadicMassRatio theta ≤ 1)
    · norm_num
  have hofRealQ : ENNReal.ofReal q = qENN := by
    exact ENNReal.ofReal_toReal hqTop
  apply active_family_real_card_lower_bound_with_coefficient
    active hq hlowerTop hcapZero hcapTop
  · change lowerConstant * (ENNReal.ofReal q).rpow theta ≤ mass
    calc
      lowerConstant * (ENNReal.ofReal q).rpow theta =
          dyadicMassThreshold theta n := by
        rw [hofRealQ]
        exact (dyadicMassThreshold_eq_prefactor_mul_scale_rpow theta n).symm
      _ ≤ mass := hmass
  · simpa only [q, qENN] using hcount

/-- The Hausdorff layer actually gives the stronger point loss `theta`.
For the common WZ bookkeeping we weaken it to `2 * theta`; this is valid at
every dyadic scale at most one and leaves the coefficient unchanged. -/
theorem dyadic_mass_threshold_active_family_real_card_lower_bound_double_loss
    {ι : Type*} (theta : ℝ) (n : ℕ) (active : Finset ι)
    {mass cap : ENNReal}
    (htheta : 0 < theta)
    (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hmass : dyadicMassThreshold theta n ≤ mass)
    (hcount : mass / 2 ≤
      (active.card : ENNReal) *
        (cap * (ENNReal.ofReal
          (2 * ((((2 : ENNReal)⁻¹) ^ n).toReal))) ^ 3)) :
    ((((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹).toReal) /
        (16 * cap.toReal)) *
      ((((2 : ENNReal)⁻¹) ^ n).toReal) ^ (-3 + 2 * theta) ≤
        (active.card : ℝ) := by
  let q : ℝ := (((2 : ENNReal)⁻¹) ^ n).toReal
  let pointConstant : ℝ :=
    (((1 - dyadicMassRatio theta) * (2 : ENNReal)⁻¹).toReal) /
      (16 * cap.toReal)
  have hqPos : 0 < q := by
    dsimp [q]
    exact ENNReal.toReal_pos (by simp) (by simp)
  have hqOne : q ≤ 1 := by
    dsimp [q]
    rw [ENNReal.toReal_pow]
    norm_num
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpointConstantNonneg : 0 ≤ pointConstant := by
    dsimp [pointConstant]
    positivity
  have hstrong : pointConstant * q ^ (-3 + theta) ≤
      (active.card : ℝ) := by
    simpa [pointConstant, q] using
      (dyadic_mass_threshold_active_family_real_card_lower_bound
        theta n active hcapZero hcapTop hmass hcount)
  calc
    pointConstant * q ^ (-3 + 2 * theta) ≤
        pointConstant * q ^ (-3 + theta) := by
      apply mul_le_mul_of_nonneg_left _ hpointConstantNonneg
      apply Real.rpow_le_rpow_of_exponent_ge hqPos hqOne
      linarith
    _ ≤ (active.card : ℝ) := hstrong

/-- On a small scale, the `delta^(2 theta)` shading produced by the selected
cover layer is at least the weaker `delta^eta` density required by the finite
Wang--Zakharov theorem. -/
theorem wz_shading_exponent_absorption {delta theta eta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 2 * theta ≤ eta) :
    delta ^ eta ≤ delta ^ (2 * theta) := by
  exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one heta

/-- The convex-Wolff loss `delta^(-2 theta)` is dominated by the common
`delta^(-eta)` allowance. -/
theorem wz_convex_wolff_exponent_absorption {delta theta eta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 2 * theta ≤ eta) :
    delta ^ (-(2 * theta)) ≤ delta ^ (- eta) := by
  apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
  linarith

/-- The almost-AD pruning loss `delta^(-3 theta)` is likewise dominated by
the common `delta^(-eta)` allowance. -/
theorem wz_ad_exponent_absorption {delta theta eta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 3 * theta ≤ eta) :
    delta ^ (-(3 * theta)) ≤ delta ^ (- eta) := by
  apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
  linarith

/-- The final Hausdorff-cover comparison has a strict exponent gap.  Once
the small scale is chosen so that the fixed upper constant times
`delta^(chi/2)` is below the fixed lower constant, the cover upper bound with
exponent `-4 + chi` is strictly smaller than the Wang--Zakharov lower bound
with exponent `-4 + chi/2`. -/
theorem wz_covering_exponent_separation
    {delta chi lowerConstant upperConstant : ℝ}
    (hdelta : 0 < delta)
    (hgap : upperConstant * delta ^ (chi / 2) < lowerConstant) :
    upperConstant * delta ^ (-4 + chi) <
      lowerConstant * delta ^ (-4 + chi / 2) := by
  have hpow : 0 < delta ^ (-4 + chi / 2) :=
    Real.rpow_pos_of_pos hdelta _
  calc
    upperConstant * delta ^ (-4 + chi) =
        (upperConstant * delta ^ (chi / 2)) *
          delta ^ (-4 + chi / 2) := by
      rw [show -4 + chi = chi / 2 + (-4 + chi / 2) by ring,
        Real.rpow_add hdelta]
      ring
    _ < lowerConstant * delta ^ (-4 + chi / 2) :=
      mul_lt_mul_of_pos_right hgap hpow

/-- The two covering-number estimates at the selected Hausdorff layer are
incompatible once the fixed constants have been absorbed into the exponent
gap.  This is the terminal contradiction in the cover-adapted readback. -/
theorem wz_covering_bounds_contradiction
    {delta chi lowerConstant upperConstant coveringCount : ℝ}
    (hdelta : 0 < delta)
    (hgap : upperConstant * delta ^ (chi / 2) < lowerConstant)
    (hlower : lowerConstant * delta ^ (-4 + chi / 2) ≤ coveringCount)
    (hupper : coveringCount ≤
      upperConstant * delta ^ (-4 + chi)) : False := by
  have hstrict := wz_covering_exponent_separation hdelta hgap
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- `ENNReal` version of the terminal exponent separation, matching the
codomain of `coveringNumber` and of the finite Wang--Zakharov interface. -/
theorem wz_covering_exponent_separation_ennreal
    {delta chi lowerConstant upperConstant : ℝ}
    (hdelta : 0 < delta)
    (hgap :
      ENNReal.ofReal upperConstant *
          (ENNReal.ofReal delta).rpow (chi / 2) <
        ENNReal.ofReal lowerConstant) :
    ENNReal.ofReal upperConstant *
        (ENNReal.ofReal delta).rpow (-4 + chi) <
      ENNReal.ofReal lowerConstant *
        (ENNReal.ofReal delta).rpow (-4 + chi / 2) := by
  let x : ENNReal := ENNReal.ofReal delta
  have hx0 : x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hxtop : x ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : x.rpow (-4 + chi / 2) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hdelta) hxtop)
  have hptop : x.rpow (-4 + chi / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 hxtop
  have hpower :
      x.rpow (-4 + chi) =
        x.rpow (chi / 2) * x.rpow (-4 + chi / 2) := by
    calc
      x.rpow (-4 + chi) =
          x.rpow (chi / 2 + (-4 + chi / 2)) := by
        congr 1
        ring
      _ = x.rpow (chi / 2) * x.rpow (-4 + chi / 2) :=
        ENNReal.rpow_add (chi / 2) (-4 + chi / 2) hx0 hxtop
  change
    ENNReal.ofReal upperConstant * x.rpow (-4 + chi) <
      ENNReal.ofReal lowerConstant * x.rpow (-4 + chi / 2)
  rw [hpower]
  simpa [mul_assoc] using ENNReal.mul_lt_mul_left hp0 hptop hgap

/-- The final lower and upper covering-number estimates are incompatible in
their native `ENNReal` codomain. -/
theorem wz_covering_bounds_contradiction_ennreal
    {delta chi lowerConstant upperConstant : ℝ}
    {coveringCount : ENNReal}
    (hdelta : 0 < delta)
    (hgap :
      ENNReal.ofReal upperConstant *
          (ENNReal.ofReal delta).rpow (chi / 2) <
        ENNReal.ofReal lowerConstant)
    (hlower :
      ENNReal.ofReal lowerConstant *
          (ENNReal.ofReal delta).rpow (-4 + chi / 2) ≤
        coveringCount)
    (hupper : coveringCount ≤
      ENNReal.ofReal upperConstant *
        (ENNReal.ofReal delta).rpow (-4 + chi)) : False := by
  have hstrict :=
    wz_covering_exponent_separation_ennreal hdelta hgap
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- Coefficient-generic form of the terminal exponent contradiction.  The
published WZ constant naturally appears as an arbitrary finite `ENNReal`
inverse, so no artificial conversion through a real coefficient is needed. -/
theorem wz_covering_bounds_contradiction_ennreal_coefficients
    {delta chi : ℝ} {lowerConstant upperConstant coveringCount : ENNReal}
    (hdelta : 0 < delta)
    (hgap : upperConstant *
          (ENNReal.ofReal delta).rpow (chi / 2) < lowerConstant)
    (hlower : lowerConstant *
          (ENNReal.ofReal delta).rpow (-4 + chi / 2) ≤ coveringCount)
    (hupper : coveringCount ≤
      upperConstant * (ENNReal.ofReal delta).rpow (-4 + chi)) : False := by
  let x : ENNReal := ENNReal.ofReal delta
  have hx0 : x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hxtop : x ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0 : x.rpow (-4 + chi / 2) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hdelta) hxtop)
  have hptop : x.rpow (-4 + chi / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 hxtop
  have hpower :
      x.rpow (-4 + chi) =
        x.rpow (chi / 2) * x.rpow (-4 + chi / 2) := by
    calc
      x.rpow (-4 + chi) =
          x.rpow (chi / 2 + (-4 + chi / 2)) := by
        congr 1
        ring
      _ = x.rpow (chi / 2) * x.rpow (-4 + chi / 2) :=
        ENNReal.rpow_add (chi / 2) (-4 + chi / 2) hx0 hxtop
  have hstrict :
      upperConstant * x.rpow (-4 + chi) <
        lowerConstant * x.rpow (-4 + chi / 2) := by
    rw [hpower]
    simpa [mul_assoc] using ENNReal.mul_lt_mul_left hp0 hptop hgap
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

/-- Read the published finite WZ estimate back to any physical target which
contains the union of the cubical shadings.  This is the exact monotonicity
step needed after a Hausdorff cover layer has produced its finite source. -/
theorem wang_zakharov_finite_readback_to_target
    (hWZ : HasWangZakharovFiniteEstimate) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta : ℝ, 0 < eta ∧
      ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
      ∃ deltaZero : ℝ, 0 < deltaZero ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (target : Set E4),
        D.thickness ≤ deltaZero →
        IsWangZakharovNativeFiniteInput D eta →
        (⋃ i, D.shading i) ⊆ target →
        A⁻¹ * (ENNReal.ofReal D.thickness).rpow (-4 + epsilon) ≤
          coveringNumber target D.thickness := by
  intro epsilon hepsilon
  obtain ⟨eta, heta, A, hA0, hAtop, deltaZero, hdeltaZero, hfinite⟩ :=
    hWZ epsilon hepsilon
  refine ⟨eta, heta, A, hA0, hAtop, deltaZero, hdeltaZero, ?_⟩
  intro n D target hdelta hinput htarget
  have hw : ∀ i, D.weight i = 1 := hinput.1.2.2.2.2.2.1
  have hsource : sourceUnion D ⊆ target := by
    rw [sourceUnion_eq_iUnion_shading_of_weights_one D hw]
    exact htarget
  exact (hfinite n D hdelta hinput).trans
    (coveringNumber_mono hsource D.thickness)

end StickyKakeya4
