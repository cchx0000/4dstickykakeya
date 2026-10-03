import Theorems.Thm_StickyKakeya4_finite_hausdorff_ball_cover
import Theorems.Thm_StickyKakeya4_actual_slope_source
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Actual Hausdorff slicing via summable finite ball-cover costs. The same
Lebesgue-a.e. slicing time works for every later radius/cost request.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace StickyKakeya4.CommonTimeSliceCover

variable (β : NNReal) (F : Finset ℕ) (c r : ℕ → ℝ)

def activeCost (t : ℝ) : ℝ≥0∞ :=
  ∑ i ∈ F, (Ioo (c i - r i) (c i + r i)).indicator
    (fun _ => ENNReal.ofReal (r i ^ (β : ℝ))) t

lemma measurable_activeCost : Measurable (activeCost β F c r) := by
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator measurableSet_Ioo

lemma lintegral_activeCost (hr : ∀ i, 0 < r i) :
    (∫⁻ t, activeCost β F c r t) =
      ENNReal.ofReal (2 * ∑ i ∈ F, r i ^ ((β : ℝ) + 1)) := by
  unfold activeCost
  rw [lintegral_finsetSum F (fun i _ => measurable_const.indicator measurableSet_Ioo)]
  simp only [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
  have hterm (i : ℕ) : ENNReal.ofReal (r i ^ (β : ℝ)) *
      ENNReal.ofReal (c i + r i - (c i - r i)) =
      ENNReal.ofReal (2 * r i ^ ((β : ℝ) + 1)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hr i).le _)]
    congr 1
    rw [Real.rpow_add (hr i), Real.rpow_one]
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (by norm_num) (Real.rpow_nonneg (hr i).le _))]
  congr 1
  rw [Finset.mul_sum]

lemma activeCost_eq (hr : ∀ i, 0 < r i) (t : ℝ) :
    activeCost β F c r t = ENNReal.ofReal
      (∑ i ∈ F.filter (fun i => t ∈ Ioo (c i - r i) (c i + r i)), r i ^ (β : ℝ)) := by
  classical
  rw [activeCost, ENNReal.ofReal_sum_of_nonneg]
  · simp only [Finset.sum_filter, Set.indicator_apply]
  · intro i hi
    exact Real.rpow_nonneg (hr i).le _

lemma norm_horizontalProjection_le (x : E4) :
    ‖horizontalProjection x‖ ≤ ‖x‖ := by
  have hsq : ‖horizontalProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [horizontalProjection, Fin.sum_univ_succ]
    positivity
  nlinarith [norm_nonneg (horizontalProjection x), norm_nonneg x]

/-- For almost every actual height, the spatial slice of a compact set of
dimension below `1 + β` has arbitrarily fine finite open-ball covers with
arbitrarily small total `β`-power radius cost. The same time works for all
scale and cost requests. -/
theorem ae_common_time_slice_cover
    (K : Set E4) (hK : IsCompact K) (β : NNReal)
    (hdim : dimH K < ((1 + β : NNReal) : ENNReal))
    : ∀ᵐ t : ℝ, ∀ rho epsilon : ℝ, 0 < rho → 0 < epsilon →
      ∃ F : Finset ℕ, ∃ center : ℕ → E3, ∃ radius : ℕ → ℝ,
        {x : E3 | ActualSlopeSource.heightPoint x t ∈ K} ⊆
          ⋃ i ∈ (F : Set ℕ), Metric.ball (center i) (radius i) ∧
        (∀ i, 0 < radius i ∧ radius i < rho) ∧
        (∑ i ∈ F, radius i ^ (β : ℝ)) < epsilon := by
  classical
  let delta : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hdpos (n : ℕ) : 0 < delta n := by dsimp [delta]; positivity
  have hdtend : Tendsto delta atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdsum : Summable delta :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hcovers (n : ℕ) :=
    exists_finite_radius_cost_ball_cover_of_compact_dimH_lt K hK hdim
      (hdpos n) (half_pos (hdpos n))
  choose F center radius hcover hradius hcost using hcovers
  let cost : ℕ → ℝ → ℝ≥0∞ := fun n =>
    activeCost β (F n) (fun i => center n i (Fin.last 3)) (radius n)
  have hmeas (n : ℕ) : Measurable (cost n) :=
    measurable_activeCost _ _ _ _
  have hint (n : ℕ) : (∫⁻ t, cost n t) ≤ ENNReal.ofReal (delta n) := by
    rw [show cost n = activeCost β (F n)
      (fun i => center n i (Fin.last 3)) (radius n) from rfl,
      lintegral_activeCost _ _ _ _ (fun i => (hradius n i).1)]
    apply ENNReal.ofReal_le_ofReal
    have hc : (∑ i ∈ F n, radius n i ^ ((β : ℝ) + 1)) < delta n / 2 := by
      simpa only [NNReal.coe_add, NNReal.coe_one, add_comm (1 : ℝ)] using hcost n
    linarith
  have hintsum : (∫⁻ t, ∑' n, cost n t) ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hmeas n).aemeasurable)]
    exact ne_top_of_le_ne_top hdsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hint)
  have hae : ∀ᵐ t : ℝ, ∑' n, cost n t < ⊤ :=
    ae_lt_top (Measurable.tsum hmeas) hintsum
  filter_upwards [hae] with t ht
  intro rho epsilon hrho hepsilon
  have hctend := ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne
  have hsmallr : ∀ᶠ n in atTop, delta n < rho :=
    hdtend.eventually (gt_mem_nhds hrho)
  have hsmallc : ∀ᶠ n in atTop, cost n t < ENNReal.ofReal epsilon :=
    hctend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hepsilon))
  obtain ⟨n, hnr, hnc⟩ := (hsmallr.and hsmallc).exists
  let A : Finset ℕ := (F n).filter
    (fun i => t ∈ Ioo (center n i (Fin.last 3) - radius n i)
      (center n i (Fin.last 3) + radius n i))
  refine ⟨A, fun i => horizontalProjection (center n i), radius n, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion.mp (hcover n hx) |>.imp
      fun i => Set.mem_iUnion.mp
    have hnorm := PiLp.norm_apply_le
      (ActualSlopeSource.heightPoint x t - center n i) (Fin.last 3)
    have hdist : ‖ActualSlopeSource.heightPoint x t - center n i‖ < radius n i := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hxi
    have hheight : |t - center n i (Fin.last 3)| < radius n i := by
      have hcoord : |t - center n i (Fin.last 3)| ≤
          ‖ActualSlopeSource.heightPoint x t - center n i‖ := by
        change |ActualSlopeSource.heightPoint x t (Fin.last 3) -
          center n i (Fin.last 3)| ≤ _ at hnorm
        rw [ActualSlopeSource.heightPoint_last] at hnorm
        exact hnorm
      exact hcoord.trans_lt hdist
    have hiA : i ∈ A := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      have habs := abs_lt.mp hheight
      constructor <;> linarith [habs.1, habs.2]
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiA, ?_⟩⟩
    have hp := norm_horizontalProjection_le
      (ActualSlopeSource.heightPoint x t - center n i)
    have hproj : horizontalProjection (ActualSlopeSource.heightPoint x t) = x := by
      ext j
      exact ActualSlopeSource.heightPoint_castSucc x t j
    rw [horizontalProjection_sub, hproj] at hp
    exact hp.trans_lt hdist
  · intro i
    exact ⟨(hradius n i).1, (hradius n i).2.trans hnr⟩
  · have heq : cost n t = ENNReal.ofReal (∑ i ∈ A, radius n i ^ (β : ℝ)) :=
      activeCost_eq _ _ _ _ (fun i => (hradius n i).1) t
    rw [heq] at hnc
    exact (ENNReal.ofReal_lt_ofReal_iff hepsilon).mp hnc

/-- A single good slicing time can be chosen in any nontrivial closed interval. -/
theorem exists_common_time_slice_cover
    (K : Set E4) (hK : IsCompact K) (β : NNReal)
    (hdim : dimH K < ((1 + β : NNReal) : ENNReal))
    {u v : ℝ} (huv : u < v) :
    ∃ t ∈ Icc u v, ∀ rho epsilon : ℝ, 0 < rho → 0 < epsilon →
      ∃ F : Finset ℕ, ∃ center : ℕ → E3, ∃ radius : ℕ → ℝ,
        {x : E3 | ActualSlopeSource.heightPoint x t ∈ K} ⊆
          ⋃ i ∈ (F : Set ℕ), Metric.ball (center i) (radius i) ∧
        (∀ i, 0 < radius i ∧ radius i < rho) ∧
        (∑ i ∈ F, radius i ^ (β : ℝ)) < epsilon := by
  have hJ : volume (Icc u v) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hJ
    (ae_restrict_of_ae (ae_common_time_slice_cover K hK β hdim))

end StickyKakeya4.CommonTimeSliceCover
