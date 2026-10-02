import Theorems.Thm_StickyKakeya4_finite_hausdorff_ball_cover
import Theorems.Thm_StickyKakeya4_original_residual_criterion

/-!
# Recurrent rooted heavy scales from the actual front dimension deficit

Finite actual-radius Hausdorff covers show that a measure carried by a compact
set of dimension below `q` has unbounded upper dyadic `q`-density almost
everywhere. This is a statement about one fixed measure, without selecting a
new source at each scale. The proof estimates outer measure directly, so no
measurability hypothesis on a set of good centers is needed.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section

namespace StickyKakeya4.RootedHeavyLimsup

/-- The concrete decreasing dyadic radii. -/
def radius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

@[simp] theorem radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

/-- Every sufficiently small ball fits inside a dyadic ball of less than
four times its radius, with the dyadic index beyond the requested cutoff. -/
theorem exists_dyadic_enclosure (N : ℕ) {r : ℝ} (hr : 0 < r)
    (hrN : r < radius N / 2) :
    ∃ n : ℕ, N ≤ n ∧ 2 * r ≤ radius n ∧ radius n < 4 * r := by
  have hbase := radius_pos N
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 2 * r / radius N by positivity)
    (show 2 * r / radius N ≤ 1 by apply (div_le_one hbase).2; linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have hlo := (lt_div_iff₀ hbase).mp hjlo
  have hhi := (div_le_iff₀ hbase).mp hjhi
  rw [pow_succ] at hlo
  refine ⟨N + j, Nat.le_add_right _ _, ?_, ?_⟩ <;>
    dsimp [radius] at * <;> rw [pow_add] <;> nlinarith

/-- Uniform dyadic upper growth on any subset of a dimension-deficient
compact carrier forces that subset to have outer measure zero. -/
theorem measure_zero_of_uniform_dyadic_growth
    {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X]
    (ν : Measure X) (K T : Set X) (hK : IsCompact K) (hTK : T ⊆ K)
    {q : ℝ≥0} (hdim : dimH K < (q : ℝ≥0∞))
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hgrowth : ∀ x ∈ T, ∀ n : ℕ, N ≤ n →
      ν (Metric.ball x (radius n)) ≤ ENNReal.ofReal (C * radius n ^ (q : ℝ))) :
    ν T = 0 := by
  classical
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  change ν T ≤ (0 : ℝ≥0∞) + (ε : ℝ≥0∞)
  rw [zero_add]
  have hεreal : 0 < (ε : ℝ) := hε
  rw [← ENNReal.ofReal_coe_nnreal]
  let D : ℝ := C * 4 ^ (q : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨m, c, r, hcover, hr, hcost⟩ :=
    exists_fin_radius_cost_ball_cover_of_compact_dimH_lt K hK hdim
      (div_pos (radius_pos N) (by norm_num : (0 : ℝ) < 2)) (div_pos hεreal hD)
  have hball (i : Fin m) : ν (T ∩ Metric.ball (c i) (r i)) ≤
      ENNReal.ofReal (D * r i ^ (q : ℝ)) := by
    by_cases hi : (T ∩ Metric.ball (c i) (r i)).Nonempty
    · obtain ⟨x, hxT, hxi⟩ := hi
      obtain ⟨n, hnN, hnr, hn4⟩ := exists_dyadic_enclosure N (hr i).1 (hr i).2
      have hsub : T ∩ Metric.ball (c i) (r i) ⊆ Metric.ball x (radius n) := by
        intro y hy
        have hyc : dist y (c i) < r i := hy.2
        have hxc : dist (c i) x < r i := by simpa [dist_comm] using hxi
        exact (dist_triangle y (c i) x).trans_lt ((add_lt_add hyc hxc).trans_le (by linarith))
      calc
        _ ≤ ν (Metric.ball x (radius n)) := measure_mono hsub
        _ ≤ ENNReal.ofReal (C * radius n ^ (q : ℝ)) := hgrowth x hxT n hnN
        _ ≤ ENNReal.ofReal (D * r i ^ (q : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hp := Real.rpow_le_rpow (radius_pos n).le hn4.le q.coe_nonneg
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (hr i).1.le] at hp
          have hmul := mul_le_mul_of_nonneg_left hp hC
          have hnon := Real.rpow_nonneg (hr i).1.le (q : ℝ)
          dsimp [D]
          nlinarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hi, measure_empty]
      exact bot_le
  have hsub : T ⊆ ⋃ i : Fin m, T ∩ Metric.ball (c i) (r i) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (hTK hx))
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  calc
    ν T ≤ ν (⋃ i : Fin m, T ∩ Metric.ball (c i) (r i)) := measure_mono hsub
    _ ≤ ∑ i : Fin m, ν (T ∩ Metric.ball (c i) (r i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin m, ENNReal.ofReal (D * r i ^ (q : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hball i)
    _ = ENNReal.ofReal (D * ∑ i : Fin m, r i ^ (q : ℝ)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hD.le
        (Real.rpow_nonneg (hr i).1.le _)), Finset.mul_sum]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [(lt_div_iff₀ hD).mp hcost]

/-- At almost every point of the same fixed measure, every coefficient is
exceeded at arbitrarily small dyadic radii. The exceptional set is independent
of both the coefficient and the starting index. -/
theorem ae_dyadic_heavy_of_dimH_lt
    {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X]
    (ν : Measure X) (K : Set X) (hK : IsCompact K) (hsupport : ν Kᶜ = 0)
    {q : ℝ≥0} (hdim : dimH K < (q : ℝ≥0∞)) :
    ∀ᵐ x ∂ν, ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ENNReal.ofReal (C * radius n ^ (q : ℝ)) < ν (Metric.ball x (radius n)) := by
  have hKae : ∀ᵐ x ∂ν, x ∈ K := mem_ae_iff.mpr hsupport
  have hcount (k N : ℕ) : ∀ᵐ x ∂ν, ∃ n : ℕ, N ≤ n ∧
      ENNReal.ofReal ((k : ℝ) * radius n ^ (q : ℝ)) <
        ν (Metric.ball x (radius n)) := by
    let T : Set X := {x | x ∈ K ∧ ∀ n : ℕ, N ≤ n →
      ν (Metric.ball x (radius n)) ≤ ENNReal.ofReal ((k : ℝ) * radius n ^ (q : ℝ))}
    have hT : ν T = 0 := measure_zero_of_uniform_dyadic_growth ν K T hK
      (fun _ hx => hx.1) hdim k (Nat.cast_nonneg k) N (fun _ hx => hx.2)
    have hTae : ∀ᵐ x ∂ν, x ∉ T := by
      rw [ae_iff]
      simpa using hT
    filter_upwards [hKae, hTae] with x hxK hxT
    by_contra h
    push Not at h
    exact hxT ⟨hxK, h⟩
  have hall : ∀ᵐ x ∂ν, ∀ k N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ENNReal.ofReal ((k : ℝ) * radius n ^ (q : ℝ)) <
        ν (Metric.ball x (radius n)) := by
    simpa only [ae_all_iff] using hcount
  filter_upwards [hall] with x hx
  intro C N
  obtain ⟨k, hk⟩ := exists_nat_gt C
  obtain ⟨n, hnN, hn⟩ := hx k N
  refine ⟨n, hnN, lt_of_le_of_lt ?_ hn⟩
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hk.le (Real.rpow_nonneg (radius_pos n).le _))

/-- The coefficient may equally be any finite extended nonnegative real. -/
theorem ae_dyadic_heavy_ennreal_of_dimH_lt
    {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X]
    (ν : Measure X) (K : Set X) (hK : IsCompact K) (hsupport : ν Kᶜ = 0)
    {q : ℝ≥0} (hdim : dimH K < (q : ℝ≥0∞)) :
    ∀ᵐ x ∂ν, ∀ C : ℝ≥0∞, C ≠ ∞ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (ENNReal.ofReal (radius n)) ^ (q : ℝ) < ν (Metric.ball x (radius n)) := by
  filter_upwards [ae_dyadic_heavy_of_dimH_lt ν K hK hsupport hdim] with x hx
  intro C hC N
  obtain ⟨n, hnN, hn⟩ := hx C.toReal N
  refine ⟨n, hnN, ?_⟩
  rwa [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC,
    ← ENNReal.ofReal_rpow_of_pos (radius_pos n)] at hn

/-- The actual source pushforward ball has the existing sharp time-fibre
upper bound. This keeps the open ball in the lower bound and only enlarges
its preimage to the closed collision event. -/
theorem sourceFrontMeasure_ball_le_rooted_mass
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (p : ℝ × E3) (u v A r : ℝ) (hr : 0 ≤ r)
    (hA : ∀ᵐ a ∂σ, ‖a‖ ≤ A) :
    OriginalResidualCriterion.sourceFrontMeasure σ b u v
      (Metric.ball (OriginalResidualCriterion.frontParam b p) r) ≤
      ENNReal.ofReal (2 * r) *
        σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * r} := by
  rw [OriginalResidualCriterion.sourceFrontMeasure,
    Measure.map_apply (OriginalResidualCriterion.measurable_frontParam b hb)
      Metric.isOpen_ball.measurableSet]
  calc
    _ ≤ ((volume.restrict (Icc u v)).prod σ)
        {p' : ℝ × E3 | ‖slopeSpacetimePoint b p - slopeSpacetimePoint b p'‖ ≤ r} := by
      apply measure_mono
      intro p' hp'
      have hd : dist (OriginalResidualCriterion.frontParam b p')
          (OriginalResidualCriterion.frontParam b p) < r := hp'
      have heq : OriginalResidualCriterion.frontParam b = slopeSpacetimePoint b := rfl
      rw [heq, dist_comm, dist_eq_norm] at hd
      exact hd.le
    _ ≤ _ := spacetime_source_row_mass_le σ b hb p.2 p.1 u v A r hr hA

/-- A genuine consequence of front dimension deficit on one fixed original
source: for product-almost every rooted trajectory and time, every finite
coefficient is exceeded at arbitrarily small dyadic scales. The transverse
radius is the same dyadic scale times the fixed slope factor `1+A`.

There is no Frostman, slicing, heavy-input, or positive-measure time-selection
hypothesis. All lower density information is derived from `dimH K < 1+β`.
-/
theorem ae_rooted_heavy_limsup_of_front_dimH_lt
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (u v A : ℝ) (hA : ∀ᵐ a ∂σ, ‖a‖ ≤ A)
    (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞)) :
    ∀ᵐ p ∂(volume.restrict (Icc u v)).prod σ,
      ∀ C : ℝ≥0∞, C ≠ ∞ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        C * (ENNReal.ofReal (radius n)) ^ (β : ℝ) <
          σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * radius n} := by
  have hcarry := OriginalResidualCriterion.sourceFrontMeasure_supported
    σ b hb u v K hK.measurableSet hsupport
  have hfront := ae_dyadic_heavy_ennreal_of_dimH_lt
    (OriginalResidualCriterion.sourceFrontMeasure σ b u v) K hK hcarry hdim
  have hsource := ae_of_ae_map
    (OriginalResidualCriterion.measurable_frontParam b hb).aemeasurable hfront
  filter_upwards [hsource] with p hp
  intro C hC N
  have h2C : (2 : ℝ≥0∞) * C ≠ ∞ := by finiteness
  obtain ⟨n, hnN, hn⟩ := hp (2 * C) h2C N
  refine ⟨n, hnN, ?_⟩
  have hr := radius_pos n
  have hupper := sourceFrontMeasure_ball_le_rooted_mass σ b hb p u v A
    (radius n) hr.le hA
  have hr0 : ENNReal.ofReal (radius n) ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have halgebra : ENNReal.ofReal (2 * radius n) *
      (C * (ENNReal.ofReal (radius n)) ^ (β : ℝ)) =
      (2 * C) * (ENNReal.ofReal (radius n)) ^ ((1 + β : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add, NNReal.coe_one,
      ENNReal.rpow_add _ _ hr0 ENNReal.ofReal_ne_top, ENNReal.rpow_one,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    ring
  by_contra h
  have hle := le_of_not_gt h
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal (2 * radius n))) hle
  rw [halgebra] at hmul
  exact (not_lt_of_ge (hupper.trans hmul)) hn

/-- Recurrent events on a positive measure space cannot have summable
masses. This uses the first Borel--Cantelli lemma and does not discard the
measure in the time variable. -/
theorem tsum_measure_eq_top_of_ae_recurrent
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (hμ : 0 < μ univ)
    (s : ℕ → Set X)
    (hrec : ∀ᵐ x ∂μ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ x ∈ s n) :
    (∑' n, μ (s n)) = ∞ := by
  by_contra hsum
  have hfinite := ae_eventually_notMem hsum
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [hrec, hfinite] with x hx hfin
    obtain ⟨N, hN⟩ := eventually_atTop.1 hfin
    obtain ⟨n, hnN, hn⟩ := hx N
    exact hN n hnN hn
  have hzero : μ univ = 0 := by simpa [ae_iff] using hfalse
  exact hμ.ne' hzero

/-- The masses of the actual rooted-heavy events have divergent sum for
every fixed finite coefficient. Both original source mass and Lebesgue time
mass are retained; the conclusion is stronger than selecting finitely many
heavy times. -/
theorem rooted_heavy_event_mass_tsum_eq_top
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (b : E3 → E3) (hb : Measurable b) (u v A : ℝ) (huv : u < v)
    (hA : ∀ᵐ a ∂σ, ‖a‖ ≤ A) (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞))
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    (∑' n, ((volume.restrict (Icc u v)).prod σ)
      {p : ℝ × E3 | C * (ENNReal.ofReal (radius n)) ^ (β : ℝ) <
        σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + A) * radius n}}) = ∞ := by
  have hmass : 0 < ((volume.restrict (Icc u v)).prod σ) univ := by
    rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)).ne' hσpos.ne'
  apply tsum_measure_eq_top_of_ae_recurrent _ hmass
  filter_upwards [ae_rooted_heavy_limsup_of_front_dimH_lt
    σ b hb u v A hA K hK hsupport β hdim] with p hp
  exact hp C hC

/-- Every strict sub-four dimension bound admits an exponent strictly
between zero and three whose one-higher exponent is still above the dimension. -/
theorem exists_rooted_exponent_of_dimH_lt_four
    {X : Type*} [MetricSpace X] (K : Set X)
    (hdim : dimH K < (4 : ℝ≥0∞)) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 3 ∧ dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞) := by
  have htop : dimH K ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hdim.le
  have hd : (dimH K).toReal < 4 := by
    simpa using (ENNReal.toReal_lt_toReal htop (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).2 hdim
  let m : ℝ := max 1 (dimH K).toReal
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmd : (dimH K).toReal ≤ m := le_max_right _ _
  have hm4 : m < 4 := max_lt (by norm_num) hd
  let β : ℝ≥0 := ⟨(m + 2) / 2, by linarith⟩
  have hβpos : 0 < β := by change 0 < (m + 2) / 2; linarith
  have hβ3 : β < 3 := by change (m + 2) / 2 < 3; linarith
  refine ⟨β, hβpos, hβ3, ?_⟩
  apply (ENNReal.toReal_lt_toReal htop ENNReal.coe_ne_top).1
  simp only [ENNReal.coe_toReal, NNReal.coe_add, NNReal.coe_one]
  change (dimH K).toReal < 1 + (m + 2) / 2
  linarith

/-- Original-data endpoint. A strict dimension deficit yields one actual
positive bounded-density slope source, one common interval of length `3/8`,
and one exponent `0 < β < 3`, with the full rooted heavy-scale recurrence
for product-almost every source/time pair and divergent heavy-event masses. The source is constructed once
from the original compact sticky datum, before any scale is chosen. -/
theorem sticky_datum_exists_actual_rooted_heavy_limsup
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 3 ∧
      dimH (unitFront ambient) < ((1 + β : ℝ≥0) : ℝ≥0∞) ∧
      ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
        IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
        v - u = 3 / 8 ∧ (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
        (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
          ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
        (∀ᵐ p ∂(volume.restrict (Icc u v)).prod σ,
          ∀ C : ℝ≥0∞, C ≠ ∞ → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
            C * (ENNReal.ofReal (radius n)) ^ (β : ℝ) <
              σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ 2 * radius n}) ∧
        ∀ C : ℝ≥0∞, C ≠ ∞ →
          (∑' n, ((volume.restrict (Icc u v)).prod σ)
            {p : ℝ × E3 | C * (ENNReal.ofReal (radius n)) ^ (β : ℝ) <
              σ {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ 2 * radius n}}) = ∞ := by
  obtain ⟨β, hβpos, hβ3, hdimβ⟩ :=
    exists_rooted_exponent_of_dimH_lt_four (unitFront ambient) hdim
  obtain ⟨σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport⟩ :=
    ActualSlopeSource.compact_full_direction_actual_slope_source
      ambient hsticky.1 hsticky.2.1 hsticky.2.2.1
  let : IsFiniteMeasure σ := hfinite
  refine ⟨β, hβpos, hβ3, hdimβ, σ, b, u, v, hfinite, hpos, hvol,
    hb, huv, hunit, hsupport, ?_, ?_⟩
  · simpa only [one_add_one_eq_two] using ae_rooted_heavy_limsup_of_front_dimH_lt
      σ b hb u v 1 hunit (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hsticky.1)
      hsupport β hdimβ
  · intro C hC
    simpa only [one_add_one_eq_two] using rooted_heavy_event_mass_tsum_eq_top
      σ hpos b hb u v 1 (by linarith) hunit (unitFront ambient)
      (StickyKakeya4.IsCompact.unitFront hsticky.1) hsupport β hdimβ C hC

end StickyKakeya4.RootedHeavyLimsup
