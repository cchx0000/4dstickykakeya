import Theorems.Thm_StickyKakeya4_rooted_heavy_limsup
import Theorems.Thm_StickyKakeya4_disjoint_positive_exhaustion

/-!
Actual heavy physical bushes with a coefficient fixed before restricting the
source. This is a source-only consequence of front dimension deficit; it
does not improve an inherited edge error or assert direction-cap contraction.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section
namespace StickyKakeya4.WholeParentHeavyBush

open RootedHeavyLimsup

def bush (b : E3 → E3) (t : ℝ) (y : E3) (r : ℝ) : Set E3 :=
  {a | ‖b a + t • a - y‖ ≤ r}

theorem measurableSet_bush (b : E3 → E3) (hb : Measurable b)
    (t : ℝ) (y : E3) (r : ℝ) : MeasurableSet (bush b t y r) := by
  apply measurableSet_le _ measurable_const
  fun_prop

/-- The coefficient is arbitrary and fixed; it is not divided by the mass
of this source. The witness time remains in the actual marked slab. -/
theorem exists_heavy_bush_at_arbitrarily_fine_scale
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℕ) :
    ∃ (t : ℝ) (y : E3) (n : ℕ), t ∈ Icc u v ∧ N ≤ n ∧
      C * (ENNReal.ofReal (2 * radius n)) ^ (β : ℝ) <
        σ (bush b t y (2 * radius n)) := by
  have hmass : 0 < ((volume.restrict (Icc u v)).prod σ) univ := by
    rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)).ne' hσpos.ne'
  have hrec := ae_rooted_heavy_limsup_of_front_dimH_lt
    σ b hb u v 1 hunit K hK hsupport β hdim
  have htime : ∀ᵐ p : ℝ × E3 ∂(volume.restrict (Icc u v)).prod σ,
      p.1 ∈ Icc u v := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  obtain ⟨p, _, hp, ht⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass.ne'
    (by simpa only [Measure.restrict_univ] using hrec.and htime)
  have hcoef : C * (2 : ℝ≥0∞) ^ (β : ℝ) ≠ ∞ := by finiteness
  obtain ⟨n, hn, hh⟩ := hp (C * (2 : ℝ≥0∞) ^ (β : ℝ)) hcoef N
  refine ⟨p.1, b p.2 + p.1 • p.2, n, ht, hn, ?_⟩
  have hset : {a' | ‖(b p.2 - b a') + p.1 • (p.2 - a')‖ ≤ (1 + 1) * radius n} =
      bush b p.1 (b p.2 + p.1 • p.2) (2 * radius n) := by
    ext a'
    have he : (b p.2 - b a') + p.1 • (p.2 - a') =
        -(b a' + p.1 • a' - (b p.2 + p.1 • p.2)) := by module
    simp only [bush, mem_ofPred_eq, he, norm_neg, one_add_one_eq_two]
  rw [hset] at hh
  have hpow : (ENNReal.ofReal (2 * radius n)) ^ (β : ℝ) =
      (2 : ℝ≥0∞) ^ (β : ℝ) * (ENNReal.ofReal (radius n)) ^ (β : ℝ) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ β.coe_nonneg]
    norm_num
  simpa only [hpow, mul_assoc] using hh

/-- Every positive measurable remainder supplies a genuine set cut with the
same fixed coefficient and dyadic cutoff. The output's own source mass
retains the quantitative lower bound. -/
theorem positive_remainder_contains_fixed_coefficient_bush
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℕ)
    (S : Set E3) (hS : MeasurableSet S) (hSpos : σ S ≠ 0) :
    ∃ H : Set E3, H ⊆ S ∧ MeasurableSet H ∧ σ H ≠ 0 ∧
      ∃ (t : ℝ) (y : E3) (n : ℕ), t ∈ Icc u v ∧ N ≤ n ∧
        H ⊆ bush b t y (2 * radius n) ∧
        C * (ENNReal.ofReal (2 * radius n)) ^ (β : ℝ) < σ H := by
  have hpos : 0 < (σ.restrict S) univ := by
    simpa using (bot_lt_iff_ne_bot.mpr hSpos)
  obtain ⟨t, y, n, ht, hn, hheavy⟩ := exists_heavy_bush_at_arbitrarily_fine_scale
    (σ.restrict S) hpos b hb u v huv (ae_restrict_of_ae hunit) K hK
    (ae_restrict_of_ae hsupport) β hdim C hC N
  have hm := measurableSet_bush b hb t y (2 * radius n)
  rw [Measure.restrict_apply hm] at hheavy
  refine ⟨bush b t y (2 * radius n) ∩ S, inter_subset_right, hm.inter hS,
    ne_of_gt (lt_of_le_of_lt bot_le hheavy), t, y, n, ht, hn, inter_subset_left, hheavy⟩

/-- Quantitative eligibility is retained on each whole output set. The
coefficient and scale cutoff are fixed before any remainder is selected. -/
def HeavyPiece (σ : Measure E3) (b : E3 → E3) (u v : ℝ)
    (β : ℝ≥0) (C : ℝ≥0∞) (N : ℕ) (H : Set E3) : Prop :=
  ∃ (t : ℝ) (y : E3) (n : ℕ), t ∈ Icc u v ∧ N ≤ n ∧
    H ⊆ bush b t y (2 * radius n) ∧
    C * (ENNReal.ofReal (2 * radius n)) ^ (β : ℝ) < σ H

theorem exists_disjoint_heavy_bush_exhaustion
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℕ) :
    ∃ D : Set (Set E3),
      (∀ H ∈ D, MeasurableSet H ∧ HeavyPiece σ b u v β C N H ∧ σ H ≠ 0) ∧
      D.Countable ∧ D.PairwiseDisjoint id ∧ σ (⋃₀ D)ᶜ = 0 := by
  apply DisjointPositiveExhaustion.exists_countable_disjoint_positive_exhaustion
    σ (HeavyPiece σ b u v β C N)
  intro S hS hpos
  obtain ⟨H, hHS, hHm, hHpos, hH⟩ := positive_remainder_contains_fixed_coefficient_bush
    σ b hb u v huv hunit K hK hsupport β hdim C hC N S hS hpos
  exact ⟨H, hHS, hHm, hH, hHpos⟩

/-- A finite, source-disjoint family retains any threshold below the original
parent mass, with the same coefficient on every output. No cardinality or
uniform per-round retained fraction is asserted. -/
theorem exists_finite_heavy_bush_retention
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1) (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℕ)
    (target : ℝ≥0∞) (htarget : target < σ univ) :
    ∃ D : Set (Set E3),
      (∀ H ∈ D, MeasurableSet H ∧ HeavyPiece σ b u v β C N H ∧ σ H ≠ 0) ∧
      D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  apply DisjointPositiveExhaustion.exists_finite_disjoint_positive_retention
    σ (HeavyPiece σ b u v β C N) _ target htarget
  intro S hS hpos
  obtain ⟨H, hHS, hHm, hHpos, hH⟩ := positive_remainder_contains_fixed_coefficient_bush
    σ b hb u v huv hunit K hK hsupport β hdim C hC N S hS hpos
  exact ⟨H, hHS, hHm, hH, hHpos⟩

/-- From only the original sticky datum and strict front dimension deficit,
choose one fixed actual source. Every coefficient A, cutoff N, and retention
threshold below its mass then has a finite disjoint family with piece mass
greater than A times the ORIGINAL parent mass times the radius power. -/
theorem sticky_deficit_exists_whole_parent_heavy_bush_families
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 3 ∧
      ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
        IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
        v - u = 3 / 8 ∧ (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
        (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
          ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
        ∀ A : ℝ≥0∞, A ≠ ∞ → ∀ N : ℕ,
          ∀ target : ℝ≥0∞, target < σ univ →
          ∃ D : Set (Set E3),
            (∀ H ∈ D, MeasurableSet H ∧
              HeavyPiece σ b u v β (A * σ univ) N H ∧ σ H ≠ 0) ∧
            D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  obtain ⟨β, hβpos, hβ3, hdimβ⟩ :=
    exists_rooted_exponent_of_dimH_lt_four (unitFront ambient) hdim
  obtain ⟨σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport⟩ :=
    ActualSlopeSource.compact_full_direction_actual_slope_source
      ambient hsticky.1 hsticky.2.1 hsticky.2.2.1
  let : IsFiniteMeasure σ := hfinite
  refine ⟨β, hβpos, hβ3, σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport, ?_⟩
  intro A hA N target htarget
  exact exists_finite_heavy_bush_retention σ b hb u v (by linarith) hunit
    (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hsticky.1) hsupport β hdimβ
    (A * σ univ) (by finiteness) N target htarget

end StickyKakeya4.WholeParentHeavyBush
