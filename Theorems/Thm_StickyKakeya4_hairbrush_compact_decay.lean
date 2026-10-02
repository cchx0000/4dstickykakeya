import Theorems.Thm_StickyKakeya4_positive_bush_frostman
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact-reference decay for variable-time line hairbrushes

The actual contact time may vary with the source. Compactness of its allowed
window makes the existential contact relation closed. Exact row nullity then
implies uniform qualitative decay over a compact reference family.

The geometric exact-null input is separate from these measure/compactness
lemmas; no power rate is asserted.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

namespace StickyKakeya4.HairbrushCompactDecay

abbrev Phase := E3 × E3

def windowRelation (I : Set ℝ) (r : ℝ) : Set (Phase × Phase) :=
  {p | ∃ t ∈ I, ‖(p.1.2 - p.2.2) + t • (p.1.1 - p.2.1)‖ ≤ r}

def hairbrush (b : E3 → E3) (I : Set ℝ) (z : Phase) (r : ℝ) : Set E3 :=
  {a | ∃ t ∈ I, ‖(b a - z.2) + t • (a - z.1)‖ ≤ r}

theorem isClosed_windowRelation (I : Set ℝ) (hI : IsCompact I) (r : ℝ) :
    IsClosed (windowRelation I r) := by
  let : CompactSpace I := isCompact_iff_compactSpace.mp hI
  let E : Set ((Phase × Phase) × I) :=
    {p | ‖(p.1.1.2 - p.1.2.2) + (p.2 : ℝ) • (p.1.1.1 - p.1.2.1)‖ ≤ r}
  have hE : IsClosed E := isClosed_le (by fun_prop) continuous_const
  have him : Prod.fst '' E = windowRelation I r := by
    ext p
    constructor
    · rintro ⟨⟨p', t⟩, hp, rfl⟩
      exact ⟨t, t.property, hp⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨(p, ⟨t, ht⟩), hp, rfl⟩
  rw [← him]
  exact isClosedMap_fst_of_compactSpace E hE

set_option maxHeartbeats 800000 in
theorem measurableSet_hairbrush (b : E3 → E3) (hb : Measurable b)
    (I : Set ℝ) (hI : IsCompact I) (z : Phase) (r : ℝ) :
    MeasurableSet (hairbrush b I z r) := by
  have hpair : Measurable (fun a : E3 => (a, b a)) := measurable_id.prodMk hb
  have hf : Measurable (fun a : E3 => ((a, b a), z)) := hpair.prodMk measurable_const
  change MeasurableSet ((fun a : E3 => ((a, b a), z)) ⁻¹' windowRelation I r)
  exact (isClosed_windowRelation I hI r).measurableSet.preimage hf

theorem hairbrush_mono (b : E3 → E3) (I : Set ℝ) (z : Phase)
    {r s : ℝ} (hrs : r ≤ s) : hairbrush b I z r ⊆ hairbrush b I z s := by
  rintro a ⟨t, ht, h⟩
  exact ⟨t, ht, h.trans hrs⟩

/-- The contact time is compactly selected only to prove a set identity;
there is no change to the source or its inherited reference. -/
theorem iInter_hairbrush_eq_exact (b : E3 → E3) (I : Set ℝ)
    (hI : IsCompact I) (hIne : I.Nonempty) (z : Phase) :
    (⋂ r > (0 : ℝ), hairbrush b I z r) = hairbrush b I z 0 := by
  ext a
  simp only [Set.mem_iInter]
  constructor
  · intro ha
    obtain ⟨t, ht, hmin⟩ := hI.exists_isMinOn hIne
      (show ContinuousOn (fun s : ℝ => ‖(b a - z.2) + s • (a - z.1)‖) I by
        fun_prop)
    refine ⟨t, ht, ?_⟩
    by_contra hnot
    have hpos : 0 < ‖(b a - z.2) + t • (a - z.1)‖ := lt_of_not_ge hnot
    obtain ⟨s, hs, hnear⟩ := ha (‖(b a - z.2) + t • (a - z.1)‖ / 2)
      (by positivity)
    have hlow := hmin hs
    change ‖(b a - z.2) + t • (a - z.1)‖ ≤
      ‖(b a - z.2) + s • (a - z.1)‖ at hlow
    linarith
  · intro ha r hr
    exact hairbrush_mono b I z hr.le ha

/-- Moving the reference changes every allowed-time residual by the same
source-independent error. -/
theorem hairbrush_reference_shift (b : E3 → E3) (I : Set ℝ)
    (T : ℝ) (hT : ∀ t ∈ I, |t| ≤ T) (z w : Phase) (r : ℝ) :
    hairbrush b I z r ⊆
      hairbrush b I w (r + ‖z.2 - w.2‖ + T * ‖z.1 - w.1‖) := by
  rintro a ⟨t, ht, hnear⟩
  refine ⟨t, ht, ?_⟩
  have heq : (b a - w.2) + t • (a - w.1) =
      ((b a - z.2) + t • (a - z.1)) + (z.2 - w.2) + t • (z.1 - w.1) := by
    module
  rw [heq]
  calc
    _ ≤ ‖(b a - z.2) + t • (a - z.1)‖ + ‖z.2 - w.2‖ +
        ‖t • (z.1 - w.1)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ r + ‖z.2 - w.2‖ + T * ‖z.1 - w.1‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact hT t ht

theorem exact_mass_ge_of_convergent_hairbrushes
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (I : Set ℝ) (hI : IsCompact I) (hIne : I.Nonempty)
    (T : ℝ) (hT : ∀ t ∈ I, |t| ≤ T)
    (z : ℕ → Phase) (z₀ : Phase) (hz : Tendsto z atTop (𝓝 z₀))
    (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) (p : ENNReal)
    (hmass : ∀ n, p ≤ σ (hairbrush b I (z n) (R n))) :
    p ≤ σ (hairbrush b I z₀ 0) := by
  have herr : Tendsto (fun n => R n + ‖(z n).2 - z₀.2‖ +
      T * ‖(z n).1 - z₀.1‖) atTop (𝓝 0) := by
    have hfst : Tendsto (fun n => ‖(z n).1 - z₀.1‖) atTop (𝓝 0) := by
      simpa using (((continuous_fst.tendsto z₀).comp hz).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z₀.1) atTop (𝓝 z₀.1))).norm
    have hsnd : Tendsto (fun n => ‖(z n).2 - z₀.2‖) atTop (𝓝 0) := by
      simpa using (((continuous_snd.tendsto z₀).comp hz).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z₀.2) atTop (𝓝 z₀.2))).norm
    simpa using (hR.add hsnd).add (tendsto_const_nhds.mul hfst)
  have hbound (r : ℝ) (hr : 0 < r) : p ≤ σ (hairbrush b I z₀ r) := by
    obtain ⟨n, hn⟩ := ((tendsto_order.mp herr).2 r hr).exists
    exact (hmass n).trans (measure_mono ((hairbrush_reference_shift b I T hT
      (z n) z₀ (R n)).trans (hairbrush_mono b I z₀ hn.le)))
  have hlim := tendsto_measure_biInter_gt (μ := σ) (a := (0 : ℝ))
    (s := fun r => hairbrush b I z₀ r)
    (fun r _ => (measurableSet_hairbrush b hb I hI z₀ r).nullMeasurableSet)
    (fun i j _ hij => hairbrush_mono b I z₀ hij)
    ⟨1, by norm_num, measure_ne_top σ _⟩
  rw [iInter_hairbrush_eq_exact b I hI hIne z₀] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound r hr

/-- Pointwise exact nullity gives a uniform qualitative modulus on any
compact reference family. It supplies no rate in the threshold `p`. -/
theorem uniform_small_hairbrush_mass_of_exact_null
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (I : Set ℝ) (hI : IsCompact I) (hIne : I.Nonempty)
    (T : ℝ) (hT : ∀ t ∈ I, |t| ≤ T)
    (Z : Set Phase) (hZ : IsCompact Z)
    (hzero : ∀ z ∈ Z, σ (hairbrush b I z 0) = 0)
    (p : ENNReal) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Z, σ (hairbrush b I z r) < p := by
  classical
  by_contra hfail
  push Not at hfail
  have hex : ∀ n : ℕ, ∃ z ∈ Z,
      p ≤ σ (hairbrush b I z (1 / ((n : ℝ) + 1))) := by
    intro n
    exact hfail _ (by positivity)
  choose z hz hmass using hex
  obtain ⟨z₀, hz₀, φ, hφ, hlim⟩ := hZ.tendsto_subseq hz
  have hpos := exact_mass_ge_of_convergent_hairbrushes σ b hb I hI hIne T hT
    (z ∘ φ) z₀ hlim (fun n => 1 / ((φ n : ℝ) + 1))
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop) p
    (fun n => hmass (φ n))
  rw [hzero z₀ hz₀] at hpos
  exact hp.not_ge hpos

end StickyKakeya4.HairbrushCompactDecay
