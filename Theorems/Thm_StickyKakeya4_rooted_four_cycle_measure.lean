import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Bipartite four-cycles rooted at the inherited old edge

The root endpoints are not resampled. Only the two remaining vertices are
fresh. The Cauchy--Schwarz bound gives genuine positive cycle witnesses;
nondegeneracy, physical time witnesses, and any quantitative paid alternative
are separate geometric obligations.
-/

open MeasureTheory Set Function
open scoped ENNReal
noncomputable section
namespace StickyKakeya4.RootedFourCycle

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Squared Cauchy--Schwarz for a probability law, including infinite values. -/
theorem sq_lintegral_le_lintegral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ ∫⁻ x, f x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2) hf.aemeasurable
    (measurable_const.aemeasurable : AEMeasurable (fun _ : X => (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, lintegral_const,
    measure_univ, ENNReal.rpow_two] at h
  simp only [one_pow, ENNReal.one_rpow, mul_one] at h
  have hs := pow_le_pow_left' h 2
  have hroot : ((∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
      ∫⁻ x, f x ^ 2 ∂μ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hroot] at hs
  exact hs

/-- The common-neighbor density of two left vertices. -/
def codegree (ν : Measure Y) (h : X × Y → ℝ≥0∞) (p : X × X) : ℝ≥0∞ :=
  ∫⁻ y, h (p.1, y) * h (p.2, y) ∂ν

theorem measurable_codegree (ν : Measure Y) [SFinite ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) : Measurable (codegree ν h) := by
  have hm : Measurable (fun p : (X × X) × Y => h (p.1.1, p.2) * h (p.1.2, p.2)) := by
    fun_prop
  exact hm.lintegral_prod_right'

/-- Tonelli identifies the mean codegree with the squared right degrees. -/
theorem lintegral_codegree_eq_degree_square
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ p, codegree ν h p ∂μ.prod μ) =
      ∫⁻ y, (∫⁻ x, h (x, y) ∂μ) ^ 2 ∂ν := by
  have hm : Measurable (fun p : (X × X) × Y => h (p.1.1, p.2) * h (p.1.2, p.2)) := by
    fun_prop
  unfold codegree
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro y
  have hfy : Measurable (fun x : X => h (x, y)) :=
    hh.comp (measurable_id.prodMk measurable_const)
  simpa only [pow_two] using
    (lintegral_prod_mul (μ := μ) (ν := μ) hfy.aemeasurable hfy.aemeasurable)

/-- The common-neighbor formulation of the actual bipartite C4 mass. -/
def cycleMass (μ : Measure X) (ν : Measure Y) (h : X × Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, codegree ν h p ^ 2 ∂μ.prod μ

/-- The bipartite C4 density is at least the fourth power of edge density.
No symmetry of a leftover old-edge subkernel is required. -/
theorem edge_mass_pow_four_le_cycleMass
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ p, h p ∂μ.prod ν) ^ 4 ≤ cycleMass μ ν h := by
  have hdegree := sq_lintegral_le_lintegral_sq ν
    (fun y => ∫⁻ x, h (x, y) ∂μ) hh.lintegral_prod_left'
  rw [← lintegral_prod_symm h hh.aemeasurable,
    ← lintegral_codegree_eq_degree_square μ ν h hh] at hdegree
  have hcodegree := sq_lintegral_le_lintegral_sq (μ.prod μ)
    (codegree ν h) (measurable_codegree ν h hh)
  calc
    _ = ((∫⁻ p, h p ∂μ.prod ν) ^ 2) ^ 2 := by rw [← pow_mul]
    _ ≤ (∫⁻ p, codegree ν h p ∂μ.prod μ) ^ 2 := pow_le_pow_left' hdegree 2
    _ ≤ _ := hcodegree

/-- Success density for the two fresh vertices, keeping the root edge fixed. -/
def rootSuccess (μ : Measure X) (ν : Measure Y) (h : X × Y → ℝ≥0∞)
    (p : X × Y) : ℝ≥0∞ :=
  ∫⁻ q : X × Y, h (q.1, p.2) * h (q.1, q.2) * h (p.1, q.2) ∂μ.prod ν

/-- Density of successful rooted four-cycles on the inherited edge space. -/
def rootedDensity (μ : Measure X) (ν : Measure Y) (h : X × Y → ℝ≥0∞)
    (p : X × Y) : ℝ≥0∞ := h p * rootSuccess μ ν h p

theorem measurable_rootSuccess (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (h : X × Y → ℝ≥0∞) (hh : Measurable h) :
    Measurable (rootSuccess μ ν h) := by
  have hm : Measurable (fun z : (X × Y) × (X × Y) =>
      h (z.2.1, z.1.2) * h (z.2.1, z.2.2) * h (z.1.1, z.2.2)) := by fun_prop
  exact hm.lintegral_prod_right'

theorem measurable_rootedDensity (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (h : X × Y → ℝ≥0∞) (hh : Measurable h) :
    Measurable (rootedDensity μ ν h) := hh.mul (measurable_rootSuccess μ ν h hh)

theorem rootSuccess_le_one (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hbound : ∀ p, h p ≤ 1) (p : X × Y) :
    rootSuccess μ ν h p ≤ 1 := by
  calc
    _ ≤ ∫⁻ _q : X × Y, (1 : ℝ≥0∞) ∂μ.prod ν := by
      apply lintegral_mono
      intro q
      calc
        _ ≤ (1 : ℝ≥0∞) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' (hbound (q.1, p.2)) (hbound (q.1, q.2)))
            (hbound (p.1, q.2))
        _ = 1 := by simp
    _ = 1 := by simp

/-- Rooting counts no old edge more than its original density. -/
theorem rootedDensity_le_old (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hbound : ∀ p, h p ≤ 1) (p : X × Y) :
    rootedDensity μ ν h p ≤ h p := by
  simpa only [rootedDensity, mul_one] using mul_le_mul_right (rootSuccess_le_one μ ν h hbound p) (h p)

/-- The rooted cycle marginal is a genuine submeasure of the inherited edge
measure, before any success conditioning. -/
theorem rooted_measure_le_old (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hbound : ∀ p, h p ≤ 1) :
    (μ.prod ν).withDensity (rootedDensity μ ν h) ≤ (μ.prod ν).withDensity h :=
  withDensity_mono (Filter.Eventually.of_forall (rootedDensity_le_old μ ν h hbound))

/-- Expanding the codegree square samples just the two right vertices. -/
theorem codegree_sq_eq_four_edge_integral
    (ν : Measure Y) [SFinite ν] (h : X × Y → ℝ≥0∞) (hh : Measurable h) (x z : X) :
    codegree ν h (x, z) ^ 2 =
      ∫⁻ y, ∫⁻ w, h (x, y) * h (z, y) * h (z, w) * h (x, w) ∂ν ∂ν := by
  have hf : Measurable (fun y => h (x, y) * h (z, y)) := by fun_prop
  rw [codegree, pow_two, ← lintegral_lintegral_mul hf.aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro w
  ring

/-- The counted C4 mass is exactly the mass of its rooted-old-edge marginal. -/
theorem cycleMass_eq_lintegral_rootedDensity
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1) :
    cycleMass μ ν h = ∫⁻ p, rootedDensity μ ν h p ∂μ.prod ν := by
  rw [cycleMass, lintegral_prod _ ((measurable_codegree ν h hh).pow_const 2).aemeasurable,
    lintegral_prod _ (measurable_rootedDensity μ ν h hh).aemeasurable]
  apply lintegral_congr
  intro x
  calc
    _ = ∫⁻ z, ∫⁻ y, ∫⁻ w,
        h (x, y) * h (z, y) * h (z, w) * h (x, w) ∂ν ∂ν ∂μ := by
      apply lintegral_congr
      intro z
      exact codegree_sq_eq_four_edge_integral ν h hh x z
    _ = ∫⁻ y, ∫⁻ z, ∫⁻ w,
        h (x, y) * h (z, y) * h (z, w) * h (x, w) ∂ν ∂μ ∂ν := by
      have hm : Measurable (fun p : (X × Y) × Y =>
          h (x, p.1.2) * h (p.1.1, p.1.2) * h (p.1.1, p.2) * h (x, p.2)) := by fun_prop
      exact lintegral_lintegral_swap hm.lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      have hc : h (x, y) ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (hbound (x, y))
      unfold rootedDensity rootSuccess
      rw [lintegral_prod _ (by fun_prop)]
      rw [← lintegral_const_mul' _ _ hc]
      apply lintegral_congr
      intro z
      rw [← lintegral_const_mul' _ _ hc]
      apply lintegral_congr
      intro w
      ring

/-- A positive old edge graph has a genuine positive rooted-cycle submeasure,
with its fourth-power lower bound explicit rather than hidden in a certificate. -/
theorem rooted_measure_mass_ge_edge_mass_pow_four
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1) :
    ((μ.prod ν).withDensity h univ) ^ 4 ≤
      (μ.prod ν).withDensity (rootedDensity μ ν h) univ := by
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← cycleMass_eq_lintegral_rootedDensity μ ν h hh hbound]
  exact edge_mass_pow_four_le_cycleMass μ ν h hh

theorem rootSuccess_mono (μ : Measure X) (ν : Measure Y)
    (f g : X × Y → ℝ≥0∞) (hfg : ∀ p, f p ≤ g p) (p : X × Y) :
    rootSuccess μ ν f p ≤ rootSuccess μ ν g p := by
  apply lintegral_mono
  intro q
  exact mul_le_mul' (mul_le_mul' (hfg (q.1, p.2)) (hfg (q.1, q.2)))
    (hfg (p.1, q.2))

/-- Almost every inherited edge has positive genuine C4 witness density.
The zero-success subgraph would otherwise have positive edge mass but zero
C4 mass, contradicting the same bipartite Cauchy--Schwarz bound. -/
theorem ae_rootSuccess_pos
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1) :
    ∀ᵐ p ∂(μ.prod ν).withDensity h, 0 < rootSuccess μ ν h p := by
  let bad : Set (X × Y) := {p | rootSuccess μ ν h p = 0}
  have hbad : MeasurableSet bad :=
    measurableSet_eq_fun (measurable_rootSuccess μ ν h hh) measurable_const
  let k : X × Y → ℝ≥0∞ := bad.indicator h
  have hk : Measurable k := hh.indicator hbad
  have hkle : ∀ p, k p ≤ h p := by
    intro p
    by_cases hp : p ∈ bad <;> simp [k, hp]
  have hkbound : ∀ p, k p ≤ 1 := fun p => (hkle p).trans (hbound p)
  have hrootzero : ∀ p, rootedDensity μ ν k p = 0 := by
    intro p
    by_cases hp : p ∈ bad
    · have hsuccess : rootSuccess μ ν k p = 0 :=
        le_antisymm ((rootSuccess_mono μ ν k h hkle p).trans_eq hp) bot_le
      simp [rootedDensity, hsuccess]
    · have hkzero : k p = 0 := by simp [k, hp]
      simp [rootedDensity, hkzero]
  have hrootmass : (μ.prod ν).withDensity (rootedDensity μ ν k) univ = 0 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    simp_rw [hrootzero]
    simp
  have hpow := rooted_measure_mass_ge_edge_mass_pow_four μ ν k hk hkbound
  rw [hrootmass] at hpow
  have hmass : (μ.prod ν).withDensity k univ = 0 := by
    by_contra hn
    have hp : 0 < ((μ.prod ν).withDensity k univ) ^ 4 :=
      pos_iff_ne_zero.mpr (pow_ne_zero 4 hn)
    exact (not_le_of_gt hp) hpow
  have hnull : (μ.prod ν).withDensity h bad = 0 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
    change (∫⁻ p, bad.indicator h p ∂μ.prod ν) = 0 at hmass
    rw [lintegral_indicator hbad] at hmass
    rw [withDensity_apply _ hbad]
    exact hmass
  have hne : ∀ᵐ p ∂(μ.prod ν).withDensity h, rootSuccess μ ν h p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  exact hne.mono (fun p hp => pos_iff_ne_zero.mpr hp)

end StickyKakeya4.RootedFourCycle
