import Theorems.Thm_StickyKakeya4_common_time_slice_cover
import Theorems.Thm_StickyKakeya4_whole_parent_heavy_bush

/-!
One common actual time is chosen before every coefficient, radius cutoff,
and retained-mass target. Compact-front slicing discharges the local cover
premise, and whole-set exhaustion keeps each quantitative mass bound intact.
No direction-cap contraction is asserted.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section

namespace StickyKakeya4.FixedTimeHeavyFamilies

open WholeParentHeavyBush

/-- The finite slice-cover property at one fixed time. -/
def SliceCoverProperty (K : Set E4) (β : ℝ≥0) (t : ℝ) : Prop :=
  ∀ rho epsilon : ℝ, 0 < rho → 0 < epsilon →
    ∃ F : Finset ℕ, ∃ center : ℕ → E3, ∃ radius : ℕ → ℝ,
      {x : E3 | ActualSlopeSource.heightPoint x t ∈ K} ⊆
        ⋃ i ∈ (F : Set ℕ), Metric.ball (center i) (radius i) ∧
      (∀ i, 0 < radius i ∧ radius i < rho) ∧
      (∑ i ∈ F, radius i ^ (β : ℝ)) < epsilon

/-- A sufficiently cheap finite slice cover yields a heavy genuine bush at
that same time, for any finite coefficient fixed before the cover. -/
theorem exists_heavy_bush_of_slice_cover
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ)
    (b : E3 → E3) (K : Set E4) (β : ℝ≥0) (t : ℝ)
    (hsupport : ∀ᵐ a ∂σ, ActualSlopeSource.heightPoint (b a + t • a) t ∈ K)
    (hcover : SliceCoverProperty K β t)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (rho : ℝ) (hrho : 0 < rho) :
    ∃ (y : E3) (R : ℝ), 0 < R ∧ R < rho ∧
      C * (ENNReal.ofReal R) ^ (β : ℝ) < σ (bush b t y R) := by
  classical
  have hmpos : 0 < (σ univ).toReal :=
    ENNReal.toReal_pos hσpos.ne' (measure_ne_top _ _)
  have hcpos : 0 < C.toReal + 1 := by positivity
  obtain ⟨F, center, radius, hcov, hr, hcost⟩ :=
    hcover rho ((σ univ).toReal / (C.toReal + 1)) hrho (div_pos hmpos hcpos)
  by_contra hnone
  push Not at hnone
  have hbound (i : ℕ) : σ (bush b t (center i) (radius i)) ≤
      C * (ENNReal.ofReal (radius i)) ^ (β : ℝ) :=
    hnone (center i) (radius i) (hr i).1 (hr i).2
  have hmass : σ univ ≤ ∑ i ∈ F, σ (bush b t (center i) (radius i)) := by
    calc
      σ univ ≤ σ (⋃ i ∈ (F : Set ℕ), bush b t (center i) (radius i)) := by
        apply measure_mono_ae
        filter_upwards [hsupport] with a ha
        intro _
        obtain ⟨i, hi, hia⟩ := Set.mem_iUnion.mp (hcov ha) |>.imp
          fun i => Set.mem_iUnion.mp
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
        exact (show ‖b a + t • a - center i‖ < radius i from hia).le
      _ ≤ ∑ i ∈ F, σ (bush b t (center i) (radius i)) :=
        measure_biUnion_finset_le F _
  have hsum_nonneg : 0 ≤ ∑ i ∈ F, radius i ^ (β : ℝ) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hr i).1.le _)
  have hreal : C.toReal * (∑ i ∈ F, radius i ^ (β : ℝ)) < (σ univ).toReal := by
    have hmul := (lt_div_iff₀ hcpos).mp hcost
    nlinarith
  have hsum_eq : (∑ i ∈ F, C * (ENNReal.ofReal (radius i)) ^ (β : ℝ)) =
      ENNReal.ofReal (C.toReal * (∑ i ∈ F, radius i ^ (β : ℝ))) := by
    rw [← Finset.mul_sum, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hC,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hr i).1.le _)]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_rpow_of_pos (hr i).1)
  have hlt : (∑ i ∈ F, σ (bush b t (center i) (radius i))) < σ univ := by
    calc
      _ ≤ ∑ i ∈ F, C * (ENNReal.ofReal (radius i)) ^ (β : ℝ) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = ENNReal.ofReal (C.toReal * (∑ i ∈ F, radius i ^ (β : ℝ))) := hsum_eq
      _ < ENNReal.ofReal (σ univ).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hmpos).mpr hreal
      _ = σ univ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  exact (not_lt_of_ge hmass) hlt

/-- Eligibility at the fixed time includes the output's own mass bound. -/
def HeavyPiece (σ : Measure E3) (b : E3 → E3) (β : ℝ≥0)
    (t : ℝ) (C : ℝ≥0∞) (rho : ℝ) (H : Set E3) : Prop :=
  ∃ (y : E3) (R : ℝ), 0 < R ∧ R < rho ∧ H ⊆ bush b t y R ∧
    C * (ENNReal.ofReal R) ^ (β : ℝ) < σ H

/-- Every positive measurable remainder supplies a whole eligible set at the
same fixed time, with the coefficient unchanged by restriction. -/
theorem positive_remainder_contains_fixed_time_heavy_piece
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (K : Set E4) (β : ℝ≥0) (t : ℝ)
    (hsupport : ∀ᵐ a ∂σ, ActualSlopeSource.heightPoint (b a + t • a) t ∈ K)
    (hcover : SliceCoverProperty K β t)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (rho : ℝ) (hrho : 0 < rho)
    (S : Set E3) (hS : MeasurableSet S) (hSpos : σ S ≠ 0) :
    ∃ H : Set E3, H ⊆ S ∧ MeasurableSet H ∧
      HeavyPiece σ b β t C rho H ∧ σ H ≠ 0 := by
  have hpos : 0 < (σ.restrict S) univ := by
    simpa using (bot_lt_iff_ne_bot.mpr hSpos)
  obtain ⟨y, R, hRpos, hRrho, hheavy⟩ := exists_heavy_bush_of_slice_cover
    (σ.restrict S) hpos b K β t (ae_restrict_of_ae hsupport) hcover C hC rho hrho
  have hm := measurableSet_bush b hb t y R
  rw [Measure.restrict_apply hm] at hheavy
  exact ⟨bush b t y R ∩ S, inter_subset_right, hm.inter hS,
    ⟨y, R, hRpos, hRrho, inter_subset_left, hheavy⟩,
    ne_of_gt (lt_of_le_of_lt bot_le hheavy)⟩

/-- Countably many source-disjoint whole heavy pieces exhaust the source at
one fixed good slicing time. -/
theorem exists_disjoint_fixed_time_heavy_exhaustion
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (K : Set E4) (β : ℝ≥0) (t : ℝ)
    (hsupport : ∀ᵐ a ∂σ, ActualSlopeSource.heightPoint (b a + t • a) t ∈ K)
    (hcover : SliceCoverProperty K β t)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (rho : ℝ) (hrho : 0 < rho) :
    ∃ D : Set (Set E3),
      (∀ H ∈ D, MeasurableSet H ∧ HeavyPiece σ b β t C rho H ∧ σ H ≠ 0) ∧
      D.Countable ∧ D.PairwiseDisjoint id ∧ σ (⋃₀ D)ᶜ = 0 := by
  exact DisjointPositiveExhaustion.exists_countable_disjoint_positive_exhaustion
    σ (HeavyPiece σ b β t C rho)
    (positive_remainder_contains_fixed_time_heavy_piece
      σ b hb K β t hsupport hcover C hC rho hrho)

/-- Finite retention uses whole heavy sets, not arbitrary disjointifications. -/
theorem exists_finite_fixed_time_heavy_retention
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (K : Set E4) (β : ℝ≥0) (t : ℝ)
    (hsupport : ∀ᵐ a ∂σ, ActualSlopeSource.heightPoint (b a + t • a) t ∈ K)
    (hcover : SliceCoverProperty K β t)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (rho : ℝ) (hrho : 0 < rho)
    (target : ℝ≥0∞) (htarget : target < σ univ) :
    ∃ D : Set (Set E3),
      (∀ H ∈ D, MeasurableSet H ∧ HeavyPiece σ b β t C rho H ∧ σ H ≠ 0) ∧
      D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  exact DisjointPositiveExhaustion.exists_finite_disjoint_positive_retention
    σ (HeavyPiece σ b β t C rho)
    (positive_remainder_contains_fixed_time_heavy_piece
      σ b hb K β t hsupport hcover C hC rho hrho) target htarget

/-- For Lebesgue-almost every time in the actual support slab, the same time
works for every finite parent-mass coefficient, upper radius, and target. The
slice-cover premise is discharged by the compact-set Hausdorff slicing theorem. -/
theorem ae_fixed_time_heavy_families
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ)
    (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞)) :
    ∀ᵐ t ∂volume.restrict (Icc u v), ∀ A : ℝ≥0∞, A ≠ ∞ →
      ∀ rho : ℝ, 0 < rho → ∀ target : ℝ≥0∞, target < σ univ →
        ∃ D : Set (Set E3),
          (∀ H ∈ D, MeasurableSet H ∧
            HeavyPiece σ b β t (A * σ univ) rho H ∧ σ H ≠ 0) ∧
          D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  have hgood : ∀ᵐ t : ℝ, SliceCoverProperty K β t :=
    CommonTimeSliceCover.ae_common_time_slice_cover K hK β hdim
  filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem measurableSet_Icc]
    with t hcover ht
  intro A hA rho hrho target htarget
  exact exists_finite_fixed_time_heavy_retention σ b hb K β t
    (hsupport.mono (fun a ha => ha t ht)) hcover
    (A * σ univ) (by finiteness) rho hrho target htarget

/-- One time is chosen in the nontrivial actual support slab before all
coefficient, radius, and retention requests. -/
theorem exists_fixed_time_heavy_families
    (σ : Measure E3) [IsFiniteMeasure σ]
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v)
    (K : Set E4) (hK : IsCompact K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K)
    (β : ℝ≥0) (hdim : dimH K < ((1 + β : ℝ≥0) : ℝ≥0∞)) :
    ∃ t ∈ Icc u v, ∀ A : ℝ≥0∞, A ≠ ∞ →
      ∀ rho : ℝ, 0 < rho → ∀ target : ℝ≥0∞, target < σ univ →
        ∃ D : Set (Set E3),
          (∀ H ∈ D, MeasurableSet H ∧
            HeavyPiece σ b β t (A * σ univ) rho H ∧ σ H ≠ 0) ∧
          D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  have hJ : volume (Icc u v) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv))
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hJ
    (ae_fixed_time_heavy_families σ b hb u v K hK hsupport β hdim)

/-- From only the original sticky datum and strict front dimension deficit,
choose one actual source and a SINGLE time before all finite coefficients,
radius cutoffs, and mass-retention targets. Each whole retained set lies in a
genuine physical bush at that time and is heavy against the ORIGINAL parent
mass. No direction-cap contraction or final dimension closure is asserted. -/
theorem sticky_deficit_exists_common_time_whole_parent_heavy_bush_families
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (hdim : dimH (unitFront ambient) < (4 : ℝ≥0∞)) :
    ∃ β : ℝ≥0, 0 < β ∧ β < 3 ∧
      ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
        IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
        v - u = 3 / 8 ∧ (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
        (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
          ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
        ∃ t ∈ Icc u v, ∀ A : ℝ≥0∞, A ≠ ∞ →
          ∀ rho : ℝ, 0 < rho → ∀ target : ℝ≥0∞, target < σ univ →
            ∃ D : Set (Set E3),
              (∀ H ∈ D, MeasurableSet H ∧
                HeavyPiece σ b β t (A * σ univ) rho H ∧ σ H ≠ 0) ∧
              D.Finite ∧ D.PairwiseDisjoint id ∧ target < σ (⋃₀ D) := by
  obtain ⟨β, hβpos, hβ3, hdimβ⟩ :=
    RootedHeavyLimsup.exists_rooted_exponent_of_dimH_lt_four (unitFront ambient) hdim
  obtain ⟨σ, b, u, v, hfinite, hpos, hvol, hb, huv, hunit, hsupport⟩ :=
    ActualSlopeSource.compact_full_direction_actual_slope_source
      ambient hsticky.1 hsticky.2.1 hsticky.2.2.1
  let : IsFiniteMeasure σ := hfinite
  refine ⟨β, hβpos, hβ3, σ, b, u, v, hfinite, hpos, hvol, hb, huv,
    hunit, hsupport, ?_⟩
  exact exists_fixed_time_heavy_families σ b hb u v (by linarith)
    (unitFront ambient) (StickyKakeya4.IsCompact.unitFront hsticky.1) hsupport β hdimβ

end StickyKakeya4.FixedTimeHeavyFamilies
