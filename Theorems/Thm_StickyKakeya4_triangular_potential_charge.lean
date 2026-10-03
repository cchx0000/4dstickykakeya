import Theorems.Thm_StickyKakeya4_triangular_potential_escape
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Direct heavy-root charge for the unchanged original source law

A symmetric-ball argument compares the heavy-root set with the mass excluded
by a bounded-potential cut. The cutoff is only a proof device: the conclusion
concerns the original unmodified source/time event. The Borel triangular
caller derives the uniform potential input separately.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

noncomputable section
namespace StickyKakeya4.TriangularPotentialCharge

open TriangularPotentialEscape EnergyDimension

theorem bad_common_cut_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P₁ P₂ P₃ : X → ℝ≥0∞)
    (h₁ : Measurable P₁) (h₂ : Measurable P₂) (h₃ : Measurable P₃)
    (N : ℝ≥0∞) (hN₀ : N ≠ 0) (hNtop : N ≠ ⊤) :
    μ {x | P₁ x ≤ N ∧ P₂ x ≤ N ∧ P₃ x ≤ N}ᶜ ≤
      (∫⁻ x, P₁ x + P₂ x + P₃ x ∂μ) / N := by
  have hsub : {x | P₁ x ≤ N ∧ P₂ x ≤ N ∧ P₃ x ≤ N}ᶜ ⊆
      {x | N ≤ P₁ x + P₂ x + P₃ x} := by
    intro x hx
    by_contra hn
    have hh : P₁ x + P₂ x + P₃ x ≤ N := (lt_of_not_ge hn).le
    apply hx
    refine ⟨?_, ?_, ?_⟩
    · exact (le_self_add.trans le_self_add).trans hh
    · exact (le_add_self.trans le_self_add).trans hh
    · exact le_add_self.trans hh
  refine (measure_mono hsub).trans ?_
  have h := meas_ge_le_lintegral_div (μ := μ) ((h₁.add h₂).add h₃).aemeasurable hN₀ hNtop
  exact h

theorem measurable_ball_mass
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (μ : Measure X) [SFinite μ] (r : ℝ) :
    Measurable (fun x => μ (Metric.ball x r)) := by
  have hE : MeasurableSet {p : X × X | dist p.2 p.1 < r} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hE

theorem ball_mass_integral_swap
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν η : Measure X) [SFinite ν] [SFinite η] (r : ℝ) :
    (∫⁻ x, η (Metric.ball x r) ∂ν) = ∫⁻ y, ν (Metric.ball y r) ∂η := by
  let E : Set (X × X) := {p | dist p.2 p.1 < r}
  have hE : MeasurableSet E := measurableSet_lt (by fun_prop) measurable_const
  calc
    (∫⁻ x, η (Metric.ball x r) ∂ν) = (ν.prod η) E := (Measure.prod_apply hE).symm
    _ = ∫⁻ y, ν ((fun x => (x, y)) ⁻¹' E) ∂η := Measure.prod_apply_symm hE
    _ = ∫⁻ y, ν (Metric.ball y r) ∂η := by
      apply lintegral_congr
      intro y
      congr 1
      ext x
      simp only [E, mem_preimage, mem_ofPred_eq, Metric.mem_ball, dist_comm]

theorem measurable_original_root_ball_mass
    {T X Y : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ : Measure X) [SFinite μ] (g : T × X → Y) (hg : Measurable g) (r : ℝ) :
    Measurable (fun p : T × X =>
      (μ.map (fun a => g (p.1, a))) (Metric.ball (g p) r)) := by
  let E : Set ((T × X) × X) := {q | dist (g (q.1.1, q.2)) (g q.1) < r}
  have hE : MeasurableSet E := measurableSet_lt (by fun_prop) measurable_const
  have h := measurable_measure_prodMk_left (ν := μ) hE
  convert h using 1
  funext p
  have hgp : Measurable (fun a => g (p.1, a)) := by fun_prop
  rw [Measure.map_apply hgp Metric.isOpen_ball.measurableSet]
  rfl

theorem original_heavy_event_measure_eq
    {T X Y : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (τ : Measure T) (μ : Measure X) [SFinite μ]
    (g : T × X → Y) (hg : Measurable g) (r : ℝ) (B : ℝ≥0∞) :
    (τ.prod μ) {p | B < (μ.map (fun a => g (p.1, a))) (Metric.ball (g p) r)} =
      ∫⁻ t, μ {a | B < (μ.map (fun a' => g (t, a'))) (Metric.ball (g (t, a)) r)} ∂τ := by
  rw [Measure.prod_apply
    (measurableSet_lt measurable_const (measurable_original_root_ball_mass μ g hg r))]
  rfl

theorem heavy_root_measure_le_twice_bad
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (ν η : Measure X) [SFinite ν] [SFinite η]
    (r : ℝ) (c B : ℝ≥0∞) (hc₀ : c ≠ 0) (hctop : c ≠ ⊤)
    (hthreshold : 2 * c ≤ B) (hgood : ∀ x, ν (Metric.ball x r) ≤ c) :
    (ν + η) {x | B < (ν + η) (Metric.ball x r)} ≤ 2 * η univ := by
  let E : Set X := {x | B < (ν + η) (Metric.ball x r)}
  have hsub : E ⊆ {x | c ≤ η (Metric.ball x r)} := by
    intro x hx
    by_contra hn
    have hη : η (Metric.ball x r) ≤ c := (lt_of_not_ge hn).le
    have hsum : (ν + η) (Metric.ball x r) ≤ B := by
      rw [Measure.add_apply]
      exact (add_le_add (hgood x) hη).trans (by simpa only [two_mul] using hthreshold)
    exact (not_lt_of_ge hsum) hx
  have hinter : (∫⁻ x, η (Metric.ball x r) ∂ν) ≤ c * η univ := by
    rw [ball_mass_integral_swap]
    exact (lintegral_mono hgood).trans_eq (lintegral_const c)
  have hν : ν E ≤ η univ := by
    calc
      ν E ≤ ν {x | c ≤ η (Metric.ball x r)} := measure_mono hsub
      _ ≤ (∫⁻ x, η (Metric.ball x r) ∂ν) / c :=
        meas_ge_le_lintegral_div (measurable_ball_mass η r).aemeasurable hc₀ hctop
      _ ≤ (c * η univ) / c := ENNReal.div_le_div_right hinter c
      _ = η univ := by rw [mul_comm c, ENNReal.mul_div_cancel_right hc₀ hctop]
  calc
    (ν + η) E = ν E + η E := Measure.add_apply _ _ _
    _ ≤ η univ + η univ := add_le_add hν (measure_mono (subset_univ E))
    _ = 2 * η univ := (two_mul _).symm

theorem original_heavy_root_measure_le_twice_bad
    {X Y : Type*} [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (G : Set X) (hG : MeasurableSet G) (g : X → Y) (hg : Measurable g)
    (r : ℝ) (c B : ℝ≥0∞) (hc₀ : c ≠ 0) (hctop : c ≠ ⊤)
    (hthreshold : 2 * c ≤ B)
    (hgood : ∀ y, ((μ.restrict G).map g) (Metric.ball y r) ≤ c) :
    μ {x | B < (μ.map g) (Metric.ball (g x) r)} ≤ 2 * μ Gᶜ := by
  let ν := (μ.restrict G).map g
  let η := (μ.restrict Gᶜ).map g
  have hsplit : ν + η = μ.map g := by
    rw [show ν + η = (μ.restrict G).map g + (μ.restrict Gᶜ).map g by rfl,
      ← Measure.map_add _ _ hg, Measure.restrict_add_restrict_compl hG]
  have hE : MeasurableSet {y | B < (μ.map g) (Metric.ball y r)} :=
    measurableSet_lt measurable_const (measurable_ball_mass _ _)
  have h := heavy_root_measure_le_twice_bad ν η r c B hc₀ hctop hthreshold hgood
  rw [hsplit] at h
  rw [Measure.map_apply hg hE] at h
  simpa only [η, Measure.map_apply hg MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, preimage_ofPred_eq] using h

def spatialPoint (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ) (p : ℝ × Source) : E3 :=
  WithLp.toLp 2 ![g₁ (p.1, p.2.1.1), g₂ (p.1, p.2.1), g₃ p]

theorem measurable_spatialPoint
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (h₁ : Measurable g₁) (h₂ : Measurable g₂) (h₃ : Measurable g₃) :
    Measurable (spatialPoint g₁ g₂ g₃) := by
  unfold spatialPoint
  apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> fun_prop

theorem spatial_coordinate_mem_ball {x y : E3} {r : ℝ}
    (h : x ∈ Metric.ball y r) (i : Fin 3) : x i ∈ Metric.ball (y i) r := by
  have hn : ‖x - y‖ < r := by simpa [dist_eq_norm] using h
  have hh := (PiLp.norm_apply_le (x - y) i).trans_lt hn
  simpa [Metric.mem_ball, dist_eq_norm, PiLp.sub_apply] using hh

theorem good_spatial_ball_bound
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (σ : Measure Source) (D : ℝ≥0∞)
    (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (t : ℝ) (x : E3) (r : ℝ) (hr : 0 < r) :
    ((σ.restrict (Prod.mk t ⁻¹' potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N)).map
      (fun a => spatialPoint g₁ g₂ g₃ (t, a))) (Metric.ball x r) ≤
      D * ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3 := by
  have hg : Measurable (fun a => spatialPoint g₁ g₂ g₃ (t, a)) :=
    (measurable_spatialPoint _ _ _ hg₁ hg₂ hg₃).comp measurable_prodMk_left
  rw [Measure.map_apply hg Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (Metric.isOpen_ball.measurableSet.preimage hg)]
  refine (hdom _).trans ?_
  rw [Measure.smul_apply]
  change D * _ ≤ D * _
  apply mul_le_mul_right
  refine (measure_mono ?_).trans
    (triangular_box_bound μ₁ μ₂ μ₃ g₁ g₂ g₃ hg₁ hg₂ hg₃ s hs N
      hP₁ hP₂ hP₃ t (x 0) (x 1) (x 2) r hr)
  intro a ha
  refine ⟨ha.2, ?_, ?_, ?_⟩
  · simpa [spatialPoint] using spatial_coordinate_mem_ball ha.1 0
  · simpa [spatialPoint] using spatial_coordinate_mem_ball ha.1 1
  · simpa [spatialPoint] using spatial_coordinate_mem_ball ha.1 2

theorem triangular_original_heavy_root_charge
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (τ : Measure ℝ) (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hDtop : D ≠ ⊤)
    (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞) (hN₀ : N ≠ 0) (hNtop : N ≠ ⊤)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (H : ℝ≥0∞)
    (hH : (∫⁻ p, potential₁ μ₁ g₁ s (p.1, p.2.1.1) +
      potential₂ μ₂ g₂ s (p.1, p.2.1) + potential₃ μ₃ g₃ s p ∂τ.prod σ) ≤ H)
    (r : ℝ) (hr : 0 < r) (B : ℝ≥0∞)
    (hthreshold : 2 * (D * ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3) ≤ B) :
    (∫⁻ t, σ {a | B < (σ.map (fun a' => spatialPoint g₁ g₂ g₃ (t, a')))
      (Metric.ball (spatialPoint g₁ g₂ g₃ (t, a)) r)} ∂τ) ≤ 2 * (H / N) := by
  let G := potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N
  let c := D * ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3
  have hG : MeasurableSet G := measurableSet_potentialCut _ _ _ _ _ _ _ _ hP₁ hP₂ hP₃
  have hc₀ : c ≠ 0 := by
    have hDpos : 0 < D := pos_iff_ne_zero.mpr hD₀
    have hNpos : 0 < N := pos_iff_ne_zero.mpr hN₀
    apply ne_of_gt
    dsimp [c]
    positivity
  have hctop : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top hDtop (ENNReal.pow_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hNtop (ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num)))
        (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)))
  have hpoint (t : ℝ) : σ {a | B < (σ.map (fun a' => spatialPoint g₁ g₂ g₃ (t, a')))
      (Metric.ball (spatialPoint g₁ g₂ g₃ (t, a)) r)} ≤ 2 * σ (Prod.mk t ⁻¹' G)ᶜ := by
    apply original_heavy_root_measure_le_twice_bad σ _
      (hG.preimage measurable_prodMk_left) _
      ((measurable_spatialPoint _ _ _ hg₁ hg₂ hg₃).comp measurable_prodMk_left)
      r c B hc₀ hctop hthreshold
    intro x
    exact good_spatial_ball_bound μ₁ μ₂ μ₃ σ D hdom g₁ g₂ g₃ hg₁ hg₂ hg₃
      s hs N hP₁ hP₂ hP₃ t x r hr
  have hbad : (τ.prod σ) Gᶜ ≤ H / N := by
    refine (bad_common_cut_le (τ.prod σ)
      (fun p => potential₁ μ₁ g₁ s (p.1, p.2.1.1))
      (fun p => potential₂ μ₂ g₂ s (p.1, p.2.1)) (potential₃ μ₃ g₃ s)
      (hP₁.comp (by fun_prop)) (hP₂.comp (by fun_prop)) hP₃ N hN₀ hNtop).trans ?_
    exact ENNReal.div_le_div_right hH N
  calc
    _ ≤ ∫⁻ t, 2 * σ (Prod.mk t ⁻¹' G)ᶜ ∂τ := lintegral_mono hpoint
    _ = 2 * (τ.prod σ) Gᶜ := by
      simp only [← preimage_compl]
      rw [lintegral_const_mul _ (measurable_measure_prodMk_left hG.compl),
        Measure.prod_apply hG.compl]
    _ ≤ 2 * (H / N) := mul_le_mul_right hbad _

end StickyKakeya4.TriangularPotentialCharge
