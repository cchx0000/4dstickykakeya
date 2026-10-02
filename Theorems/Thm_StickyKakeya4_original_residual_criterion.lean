import Theorems.Thm_StickyKakeya4_actual_slope_source
import Theorems.Thm_StickyKakeya4_energy_dimension
import Theorems.Thm_StickyKakeya4_residual_sublevel_power
import Theorems.Thm_StickyKakeya4_spacetime_collision_energy

/-!
# The original residual criterion on a genuinely supported front measure

This module connects the actual positive slope source to its physical
four-dimensional pushforward. Source mass and literal front support are
retained; no ambient closure or assumed Frostman probability is substituted.
The geometric residual power estimate remains a separate obligation.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section
namespace StickyKakeya4.OriginalResidualCriterion

/-- The source point at physical fourth-coordinate `s`. -/
def frontParam (b : E3 → E3) (p : ℝ × E3) : E4 :=
  ActualSlopeSource.heightPoint (b p.2 + p.1 • p.2) p.1

theorem measurable_frontParam (b : E3 → E3) (hb : Measurable b) :
    Measurable (frontParam b) := by
  unfold frontParam ActualSlopeSource.heightPoint
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> fun_prop

/-- The actual time/source pushforward, before any bounded-potential restriction. -/
def sourceFrontMeasure (σ : Measure E3) (b : E3 → E3) (u v : ℝ) : Measure E4 :=
  ((volume.restrict (Icc u v)).prod σ).map (frontParam b)

instance sourceFrontMeasure_isFinite
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (u v : ℝ) :
    IsFiniteMeasure (sourceFrontMeasure σ b u v) := by
  unfold sourceFrontMeasure
  infer_instance

/-- The pushforward has precisely time-length times source mass. -/
theorem sourceFrontMeasure_univ
    (σ : Measure E3) [SFinite σ] (b : E3 → E3) (hb : Measurable b) (u v : ℝ) :
    sourceFrontMeasure σ b u v univ = ENNReal.ofReal (v - u) * σ univ := by
  rw [sourceFrontMeasure, Measure.map_apply (measurable_frontParam b hb) MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Real.volume_Icc]

/-- A positive interval and positive slope source cannot disappear under the
physical parametrization, even when that parametrization is not injective. -/
theorem sourceFrontMeasure_ne_zero
    (σ : Measure E3) [SFinite σ] (hσ : 0 < σ univ)
    (b : E3 → E3) (hb : Measurable b) (u v : ℝ) (huv : u < v) :
    sourceFrontMeasure σ b u v ≠ 0 := by
  intro hz
  have hm := sourceFrontMeasure_univ σ b hb u v
  simp only [hz, Measure.coe_zero, Pi.zero_apply] at hm
  exact (mul_ne_zero (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)).ne' hσ.ne') hm.symm

/-- The uniform-in-height support supplied by the actual source construction
passes to the spacetime measure without taking any closure. -/
theorem sourceFrontMeasure_supported
    (σ : Measure E3) [SFinite σ] (b : E3 → E3) (hb : Measurable b)
    (u v : ℝ) (K : Set E4) (hK : MeasurableSet K)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ K) :
    sourceFrontMeasure σ b u v Kᶜ = 0 := by
  have hmeas : MeasurableSet {p : ℝ × E3 | frontParam b p ∈ K} :=
    hK.preimage (measurable_frontParam b hb)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc u v)).prod σ, frontParam b p ∈ K := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hsupport.mono (fun a ha => ha s hs)
  rw [sourceFrontMeasure, Measure.map_apply (measurable_frontParam b hb) hK.compl]
  exact mem_ae_iff.mp hae

/-- The literal codimension-two residual hypothesis from original Definition
6.26/Theorem 6.27. This is not asserted for a sticky datum by definition. -/
def HasResidualPowerBounds (σ : Measure E3) (b : E3 → E3) (u v : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 2 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) (Icc u v) ρ ≤
          C * (ENNReal.ofReal ρ) ^ (2 - η)

/-- Residual power control gains two transverse powers and one collision-time
power, then one additional spacetime power. This is finite energy of the
actual physical front measure, with the singular diagonal retained. -/
theorem sourceFrontMeasure_finite_energy
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d η t : ℝ) (hd : 0 < d) (hη : 0 ≤ η) (hη3 : η < 3)
    (ht : 0 < t) (htt : t < 4 - η)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hres : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) (Icc (u - d) (v + d)) ρ ≤
          C * (ENNReal.ofReal ρ) ^ (2 - η)) :
    (∫⁻ x, EnergyDimension.inverseDistancePotential
      (sourceFrontMeasure σ b u v) t x ∂sourceFrontMeasure σ b u v) < ∞ := by
  let K : ℝ≥0∞ := 2 * C + ENNReal.ofReal (v - u) *
    (ENNReal.ofReal (Real.pi * 4 / 3) * σ univ) *
      (ENNReal.ofReal d)⁻¹ ^ 3
  have hd0 : ENNReal.ofReal d ≠ 0 := by simp [hd.not_ge]
  have hK : K ≠ ∞ := by dsimp [K]; finiteness
  have hsub : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      (∫⁻ s in Icc u v, (σ.prod σ)
        {p : E3 × E3 | ‖(b p.1 - b p.2) + s • (p.1 - p.2)‖ ≤ ρ}) ≤
          ENNReal.ofReal (K.toReal * ρ ^ (3 - η)) := by
    intro ρ hρ hρone
    have hbound := averaged_slope_collision_mass_le_power σ 1 C
      (by simpa using hσ) b hb u v d η ρ hd hη hρ hρone.le (hres ρ hρ hρone)
    calc
      _ ≤ K * ENNReal.ofReal ρ ^ (3 - η) := by simpa [K] using hbound
      _ = ENNReal.ofReal (K.toReal * ρ ^ (3 - η)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_rpow_of_pos hρ]
  exact finite_spacetime_front_energy_of_averaged_sublevel_power σ b hb
    u v 1 K.toReal (3 - η) t (by norm_num) hslopes ENNReal.toReal_nonneg
      (by linarith) ht (by linarith) hsub

/-- Source-faithful analytic closure: residual control on the enlarged window
produces Frostman probabilities on the original front, not on its closure. -/
theorem front_frostman_of_residual_power
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d : ℝ) (huv : u < v) (hd : 0 < d)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hres : HasResidualPowerBounds σ b (u - d) (v + d)) :
    HasFrontFrostmanMeasures ambient := by
  apply EnergyDimension.hasFrontFrostmanMeasures_of_supported_finite_energies
  intro ε hε hε4
  let η : ℝ := min (ε / 2) 1
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hη2 : η < 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨C, hC, hpower⟩ := hres η hηpos hη2
  refine ⟨sourceFrontMeasure σ b u v, inferInstance,
    sourceFrontMeasure_ne_zero σ hσpos b hb u v huv,
    sourceFrontMeasure_supported σ b hb u v _ (StickyKakeya4.IsCompact.unitFront hcompact).measurableSet hsupport, ?_⟩
  exact sourceFrontMeasure_finite_energy σ hσ b hb hslopes u v d η (4 - ε)
    hd hηpos.le (by linarith) (by linarith) (by linarith) C hC hpower

/-- The original four-dimensional conclusion follows from the residual power
bound for one actual positive supported source. The missing geometric theorem
is precisely the construction of that residual bound, not this analytic step. -/
theorem front_dimH_eq_four_of_residual_power
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσpos : 0 < σ univ) (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v d : ℝ) (huv : u < v) (hd : 0 < d)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hres : HasResidualPowerBounds σ b (u - d) (v + d)) :
    dimH (unitFront ambient) = 4 := by
  apply le_antisymm
  · calc
      dimH (unitFront ambient) ≤ dimH (Set.univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · exact dimH_ge_four_of_front_frostman_measures ambient
      (front_frostman_of_residual_power ambient hcompact σ hσpos hσ b hb hslopes
        u v d huv hd hsupport hres)

/-- Construct the actual source from the original datum and reduce its
four-dimensional conclusion to the literal residual estimate on that source.
The interval used for energy lies strictly inside the constructed marked slab.
Packing dimension is deliberately absent here: using it to prove the residual
bound is the outstanding geometric part of the original argument. -/
theorem compact_full_direction_residual_reduction
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (hvalid : ∀ line ∈ ambient, IsValidLine line) (hfull : FullDirection ambient) :
    ∃ (σ : Measure E3) (b : E3 → E3) (u v : ℝ),
      IsFiniteMeasure σ ∧ 0 < σ univ ∧ σ ≤ volume ∧ Measurable b ∧
      v - u = 3 / 8 ∧ (∀ᵐ a ∂σ, ‖a‖ ≤ 1) ∧
      (∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
        ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient) ∧
      (HasResidualPowerBounds σ b u v → dimH (unitFront ambient) = 4) := by
  obtain ⟨σ, b, u, v, hfinite, hpos, hdom, hb, hlength, hslopes, hsupport⟩ :=
    ActualSlopeSource.compact_full_direction_actual_slope_source
      ambient hcompact hvalid hfull
  let : IsFiniteMeasure σ := hfinite
  refine ⟨σ, b, u, v, hfinite, hpos, hdom, hb, hlength, hslopes, hsupport, ?_⟩
  intro hres
  apply front_dimH_eq_four_of_residual_power ambient hcompact σ hpos hdom b hb hslopes
    (u + 1 / 16) (v - 1 / 16) (1 / 16) (by linarith) (by norm_num)
  · filter_upwards [hsupport] with a ha
    intro s hs
    exact ha s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · convert hres using 1 <;> ring

end StickyKakeya4.OriginalResidualCriterion
