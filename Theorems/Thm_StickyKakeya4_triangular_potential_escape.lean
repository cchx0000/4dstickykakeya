import Theorems.Thm_StickyKakeya4_energy_dimension

/-!
# Actual triangular-source Frostman measures from scalar potential cuts

All cuts are restrictions of the original source/time law. A fixed product
reference supplies only an upper bound; no independence is imposed on the
actual source. The scalar Borel caller discharges the finite-potential inputs.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section
namespace StickyKakeya4.TriangularPotentialEscape

open EnergyDimension

theorem exists_common_potential_cut
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (hμ : μ ≠ 0)
    (P₁ P₂ P₃ : X → ℝ≥0∞)
    (_h₁ : Measurable P₁) (_h₂ : Measurable P₂) (_h₃ : Measurable P₃)
    (hf₁ : ∀ᵐ x ∂μ, P₁ x < ⊤) (hf₂ : ∀ᵐ x ∂μ, P₂ x < ⊤)
    (hf₃ : ∀ᵐ x ∂μ, P₃ x < ⊤) :
    ∃ N : ℕ, μ {x | P₁ x ≤ N ∧ P₂ x ≤ N ∧ P₃ x ≤ N} ≠ 0 := by
  let G : ℕ → Set X := fun n => {x | P₁ x ≤ n ∧ P₂ x ≤ n ∧ P₃ x ≤ n}
  have hfull : ∀ᵐ x ∂μ, x ∈ ⋃ n, G n := by
    filter_upwards [hf₁, hf₂, hf₃] with x hx₁ hx₂ hx₃
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_nat_gt hx₁.ne
    obtain ⟨n₂, hn₂⟩ := ENNReal.exists_nat_gt hx₂.ne
    obtain ⟨n₃, hn₃⟩ := ENNReal.exists_nat_gt hx₃.ne
    refine mem_iUnion.mpr ⟨max n₁ (max n₂ n₃), ?_⟩
    change P₁ x ≤ _ ∧ P₂ x ≤ _ ∧ P₃ x ≤ _
    exact ⟨hn₁.le.trans (by exact_mod_cast le_max_left n₁ (max n₂ n₃)),
      hn₂.le.trans (by exact_mod_cast (le_max_left n₂ n₃).trans (le_max_right n₁ (max n₂ n₃))),
      hn₃.le.trans (by exact_mod_cast (le_max_right n₂ n₃).trans (le_max_right n₁ (max n₂ n₃)))⟩
  have hu : μ (⋃ n, G n) ≠ 0 := by
    intro hz
    have hc : μ (⋃ n, G n)ᶜ = 0 := mem_ae_iff.mp hfull
    have hall := measure_union_null hz hc
    rw [union_compl_self] at hall
    exact hμ (Measure.measure_univ_eq_zero.mp hall)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hu
  exact ⟨n, hn.ne'⟩

theorem scalar_source_cut_ball
    (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞) (c r : ℝ) (hr : 0 < r) :
    μ {a | inverseDistancePotential (μ.map g) s (g a) ≤ N ∧
      g a ∈ Metric.ball c r} ≤
      (N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s := by
  let H : Set ℝ := {y | inverseDistancePotential (μ.map g) s y ≤ N}
  have hH : MeasurableSet H :=
    measurableSet_le (measurable_inverseDistancePotential _ _) measurable_const
  have heq : μ {a | inverseDistancePotential (μ.map g) s (g a) ≤ N ∧
      g a ∈ Metric.ball c r} = ((μ.map g).restrict H) (Metric.ball c r) := by
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet,
      Measure.map_apply hg (Metric.isOpen_ball.measurableSet.inter hH)]
    congr 1
    ext a
    simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, H]
    tauto
  rw [heq]
  exact restrict_ball_growth_of_bounded_potential _ s hs H hH N
    (fun _ hy => hy) c r hr

theorem prod_event_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (E : Set (X × Y)) (hE : MeasurableSet E)
    (A : Set X) (hA : MeasurableSet A) (C : ℝ≥0∞)
    (hsub : E ⊆ Prod.fst ⁻¹' A)
    (hsec : ∀ x, ν (Prod.mk x ⁻¹' E) ≤ C) :
    μ.prod ν E ≤ C * μ A := by
  rw [Measure.prod_apply hE]
  calc
    (∫⁻ x, ν (Prod.mk x ⁻¹' E) ∂μ) ≤ ∫⁻ x, A.indicator (fun _ => C) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simpa [hx] using hsec x
      · have hz : Prod.mk x ⁻¹' E = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx (hsub hy)
        simp [hz, hx]
    _ = C * μ A := by rw [lintegral_indicator hA]; simp

abbrev Source := (ℝ × ℝ) × ℝ

def potential₁ (μ : Measure ℝ) (g : ℝ × ℝ → ℝ) (s : ℝ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  inverseDistancePotential (μ.map (fun a => g (p.1, a))) s (g p)

def potential₂ (μ : Measure ℝ) (g : ℝ × (ℝ × ℝ) → ℝ) (s : ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ≥0∞ :=
  inverseDistancePotential (μ.map (fun a => g (p.1, (p.2.1, a)))) s (g p)

def potential₃ (μ : Measure ℝ) (g : ℝ × Source → ℝ) (s : ℝ)
    (p : ℝ × Source) : ℝ≥0∞ :=
  inverseDistancePotential (μ.map (fun a => g (p.1, (p.2.1, a)))) s (g p)

def potentialCut (μ₁ μ₂ μ₃ : Measure ℝ)
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ) (s : ℝ) (N : ℝ≥0∞) : Set (ℝ × Source) :=
  {p | potential₁ μ₁ g₁ s (p.1, p.2.1.1) ≤ N ∧
    potential₂ μ₂ g₂ s (p.1, p.2.1) ≤ N ∧ potential₃ μ₃ g₃ s p ≤ N}

theorem measurableSet_potentialCut
    (μ₁ μ₂ μ₃ : Measure ℝ)
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ) (s : ℝ) (N : ℝ≥0∞)
    (h₁ : Measurable (potential₁ μ₁ g₁ s))
    (h₂ : Measurable (potential₂ μ₂ g₂ s))
    (h₃ : Measurable (potential₃ μ₃ g₃ s)) :
    MeasurableSet (potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N) := by
  apply (measurableSet_le (h₁.comp (by fun_prop)) measurable_const).inter
  exact (measurableSet_le (h₂.comp (by fun_prop)) measurable_const).inter
    (measurableSet_le h₃ measurable_const)

theorem triangular_box_bound
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (t c₁ c₂ c₃ r : ℝ) (hr : 0 < r) :
    ((μ₁.prod μ₂).prod μ₃)
      {a | (t, a) ∈ potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N ∧
        g₁ (t, a.1.1) ∈ Metric.ball c₁ r ∧
        g₂ (t, a.1) ∈ Metric.ball c₂ r ∧ g₃ (t, a) ∈ Metric.ball c₃ r} ≤
      ((N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s) ^ 3 := by
  let C := (N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s
  let A₁ : Set ℝ := {a | potential₁ μ₁ g₁ s (t, a) ≤ N ∧
    g₁ (t, a) ∈ Metric.ball c₁ r}
  let A₂ : Set (ℝ × ℝ) := {a | a.1 ∈ A₁ ∧
    potential₂ μ₂ g₂ s (t, a) ≤ N ∧ g₂ (t, a) ∈ Metric.ball c₂ r}
  let A₃ : Set Source := {a | a.1 ∈ A₂ ∧
    potential₃ μ₃ g₃ s (t, a) ≤ N ∧ g₃ (t, a) ∈ Metric.ball c₃ r}
  have hA₁ : MeasurableSet A₁ :=
    (measurableSet_le (hP₁.comp (by fun_prop)) measurable_const).inter
      (Metric.isOpen_ball.measurableSet.preimage (hg₁.comp (by fun_prop)))
  have hA₂ : MeasurableSet A₂ :=
    (hA₁.preimage measurable_fst).inter
      ((measurableSet_le (hP₂.comp (by fun_prop)) measurable_const).inter
        (Metric.isOpen_ball.measurableSet.preimage (hg₂.comp (by fun_prop))))
  have hA₃ : MeasurableSet A₃ :=
    (hA₂.preimage measurable_fst).inter
      ((measurableSet_le (hP₃.comp (by fun_prop)) measurable_const).inter
        (Metric.isOpen_ball.measurableSet.preimage (hg₃.comp (by fun_prop))))
  have hbound₁ : μ₁ A₁ ≤ C :=
    scalar_source_cut_ball μ₁ (fun a => g₁ (t, a)) (by fun_prop) s hs N c₁ r hr
  have hbound₂ : (μ₁.prod μ₂) A₂ ≤ C * C := by
    refine (prod_event_le μ₁ μ₂ A₂ hA₂ A₁ hA₁ C
      (fun _ h => h.1) ?_).trans (mul_le_mul_right hbound₁ C)
    intro a₁
    calc
      μ₂ (Prod.mk a₁ ⁻¹' A₂) ≤ μ₂ {a₂ |
          potential₂ μ₂ g₂ s (t, (a₁, a₂)) ≤ N ∧
          g₂ (t, (a₁, a₂)) ∈ Metric.ball c₂ r} :=
        measure_mono (fun _ h => h.2)
      _ ≤ C := scalar_source_cut_ball μ₂ (fun a₂ => g₂ (t, (a₁, a₂)))
        (by fun_prop) s hs N c₂ r hr
  have hbound₃ : ((μ₁.prod μ₂).prod μ₃) A₃ ≤ C * (C * C) := by
    refine (prod_event_le (μ₁.prod μ₂) μ₃ A₃ hA₃ A₂ hA₂ C
      (fun _ h => h.1) ?_).trans (mul_le_mul_right hbound₂ C)
    intro a₁₂
    calc
      μ₃ (Prod.mk a₁₂ ⁻¹' A₃) ≤ μ₃ {a₃ |
          potential₃ μ₃ g₃ s (t, (a₁₂, a₃)) ≤ N ∧
          g₃ (t, (a₁₂, a₃)) ∈ Metric.ball c₃ r} :=
        measure_mono (fun _ h => h.2)
      _ ≤ C := scalar_source_cut_ball μ₃ (fun a₃ => g₃ (t, (a₁₂, a₃)))
        (by fun_prop) s hs N c₃ r hr
  convert hbound₃ using 1
  · congr 1
    ext a
    simp only [A₃, A₂, A₁, potentialCut, mem_ofPred_eq]
    tauto
  · simp only [C, pow_succ, pow_zero, one_mul]
    ac_rfl

def point (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ) (p : ℝ × Source) : E4 :=
  WithLp.toLp 2 ![g₁ (p.1, p.2.1.1), g₂ (p.1, p.2.1), g₃ p, p.1]

theorem measurable_point
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (h₁ : Measurable g₁) (h₂ : Measurable g₂) (h₃ : Measurable g₃) :
    Measurable (point g₁ g₂ g₃) := by
  unfold point
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> fun_prop

theorem coordinate_mem_ball {x y : E4} {r : ℝ}
    (h : x ∈ Metric.ball y r) (i : Fin 4) : x i ∈ Metric.ball (y i) r := by
  have hn : ‖x - y‖ < r := by simpa [dist_eq_norm] using h
  have hh := (PiLp.norm_apply_le (x - y) i).trans_lt hn
  simpa [Metric.mem_ball, dist_eq_norm, PiLp.sub_apply] using hh

theorem cut_map_ball_bound
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (τ : Measure ℝ) (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃)) (hτ : τ ≤ volume)
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (x : E4) (r : ℝ) (hr : 0 < r) :
    (((τ.prod σ).restrict (potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N)).map
      (point g₁ g₂ g₃)) (Metric.ball x r) ≤
      (D * (N * (2 : ℝ≥0∞) ^ s) ^ 3 * 2) * ENNReal.ofReal r ^ (1 + 3 * s) := by
  let G := potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N
  let F := point g₁ g₂ g₃
  let E : Set (ℝ × Source) := F ⁻¹' Metric.ball x r ∩ G
  let C := (N * (2 : ℝ≥0∞) ^ s) * ENNReal.ofReal r ^ s
  have hG : MeasurableSet G := measurableSet_potentialCut _ _ _ _ _ _ _ _ hP₁ hP₂ hP₃
  have hF : Measurable F := measurable_point _ _ _ hg₁ hg₂ hg₃
  have hE : MeasurableSet E := (Metric.isOpen_ball.measurableSet.preimage hF).inter hG
  have hsub : E ⊆ Prod.fst ⁻¹' Metric.ball (x 3) r := by
    intro p hp
    have hh := coordinate_mem_ball hp.1 3
    simpa [F, point] using hh
  have hsec : ∀ t, σ (Prod.mk t ⁻¹' E) ≤ D * C ^ 3 := by
    intro t
    have href : ((μ₁.prod μ₂).prod μ₃) (Prod.mk t ⁻¹' E) ≤ C ^ 3 := by
      refine (measure_mono ?_).trans
        (triangular_box_bound μ₁ μ₂ μ₃ g₁ g₂ g₃ hg₁ hg₂ hg₃ s hs N
          hP₁ hP₂ hP₃ t (x 0) (x 1) (x 2) r hr)
      intro a ha
      refine ⟨ha.2, ?_, ?_, ?_⟩
      · simpa [F, point] using coordinate_mem_ball ha.1 0
      · simpa [F, point] using coordinate_mem_ball ha.1 1
      · simpa [F, point] using coordinate_mem_ball ha.1 2
    calc
      σ (Prod.mk t ⁻¹' E) ≤ (D • ((μ₁.prod μ₂).prod μ₃)) (Prod.mk t ⁻¹' E) :=
        hdom _
      _ = D * ((μ₁.prod μ₂).prod μ₃) (Prod.mk t ⁻¹' E) := by simp only [Measure.smul_apply, smul_eq_mul]
      _ ≤ D * C ^ 3 := mul_le_mul_right href D
  have hbound : (τ.prod σ) E ≤ (D * C ^ 3) * ENNReal.ofReal (2 * r) := by
    refine (prod_event_le τ σ E hE (Metric.ball (x 3) r)
      Metric.isOpen_ball.measurableSet (D * C ^ 3) hsub hsec).trans ?_
    apply mul_le_mul_right
    simpa only [Real.volume_ball] using hτ (Metric.ball (x 3) r)
  rw [Measure.map_apply hF Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (Metric.isOpen_ball.measurableSet.preimage hF)]
  calc
    (τ.prod σ) E ≤ (D * C ^ 3) * ENNReal.ofReal (2 * r) := hbound
    _ = (D * (N * (2 : ℝ≥0∞) ^ s) ^ 3 * 2) *
        ENNReal.ofReal r ^ (1 + 3 * s) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hp : (ENNReal.ofReal r ^ s) ^ (3 : ℕ) = ENNReal.ofReal r ^ (3 * s) := by
        rw [mul_comm (3 : ℝ) s, ENNReal.rpow_mul]
        norm_num
      rw [ENNReal.rpow_add_of_nonneg 1 (3 * s) (by norm_num) (by positivity),
        ENNReal.rpow_one]
      dsimp [C]
      rw [mul_pow, hp]
      rw [ENNReal.ofReal_ofNat]
      simp only [mul_assoc, mul_left_comm, mul_comm]

theorem normalize_supported_ball_bound
    (μ : Measure E4) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (S : Set E4) (hsupport : μ Sᶜ = 0)
    (q : ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ C * ENNReal.ofReal r ^ q) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Sᶜ = 0 ∧
      ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ K * ENNReal.ofReal r ^ q := by
  let m : FiniteMeasure E4 := ⟨μ, inferInstance⟩
  have hm : m ≠ 0 := by
    intro hz
    exact hμ (congrArg (fun q : FiniteMeasure E4 => (q : Measure E4)) hz)
  let ν : Measure E4 := (m.normalize : Measure E4)
  let K : ℝ≥0∞ := (↑m.mass⁻¹ : ℝ≥0∞) * C
  refine ⟨ν, by dsimp [ν]; infer_instance, ?_, K,
    ENNReal.mul_ne_top ENNReal.coe_ne_top hC, ?_⟩
  · rw [show ν = (m.normalize : Measure E4) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ℝ≥0∞) * μ Sᶜ = 0
    rw [hsupport, mul_zero]
  · intro x r hr
    rw [show ν = (m.normalize : Measure E4) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ℝ≥0∞) * μ (Metric.ball x r) ≤ K * ENNReal.ofReal r ^ q
    exact (mul_le_mul_right (hball x r hr) (↑m.mass⁻¹ : ℝ≥0∞)).trans_eq (by
      dsimp [K]
      rw [mul_assoc])

theorem exists_actual_supported_frostman
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (τ : Measure ℝ) (σ : Measure Source) [IsFiniteMeasure τ] [IsFiniteMeasure σ]
    (hsource : τ.prod σ ≠ 0)
    (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃)) (hτ : τ ≤ volume)
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (s : ℝ) (hs : 0 < s)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (hf₁ : ∀ᵐ p ∂τ.prod σ, potential₁ μ₁ g₁ s (p.1, p.2.1.1) < ⊤)
    (hf₂ : ∀ᵐ p ∂τ.prod σ, potential₂ μ₂ g₂ s (p.1, p.2.1) < ⊤)
    (hf₃ : ∀ᵐ p ∂τ.prod σ, potential₃ μ₃ g₃ s p < ⊤)
    (S : Set E4) (hsupport : ((τ.prod σ).map (point g₁ g₂ g₃)) Sᶜ = 0) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Sᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C * ENNReal.ofReal r ^ (1 + 3 * s) := by
  obtain ⟨N, hN⟩ := exists_common_potential_cut (τ.prod σ) hsource
    (fun p => potential₁ μ₁ g₁ s (p.1, p.2.1.1))
    (fun p => potential₂ μ₂ g₂ s (p.1, p.2.1))
    (potential₃ μ₃ g₃ s) (hP₁.comp (by fun_prop)) (hP₂.comp (by fun_prop))
    hP₃ hf₁ hf₂ hf₃
  let G := potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N
  let F := point g₁ g₂ g₃
  let ν₀ := ((τ.prod σ).restrict G).map F
  have hF : Measurable F := measurable_point _ _ _ hg₁ hg₂ hg₃
  have hnz : ν₀ ≠ 0 := by
    apply (Measure.map_ne_zero_iff hF.aemeasurable).mpr
    intro hz
    exact hN (Measure.restrict_eq_zero.mp hz)
  have hsν : ν₀ Sᶜ = 0 :=
    le_antisymm ((Measure.map_mono Measure.restrict_le_self hF Sᶜ).trans_eq hsupport) bot_le
  let C : ℝ≥0∞ := D * ((N : ℝ≥0∞) * (2 : ℝ≥0∞) ^ s) ^ 3 * 2
  have hC : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top hD
      exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num)))
    · norm_num
  apply normalize_supported_ball_bound ν₀ hnz S hsν (1 + 3 * s) C hC
  intro x r hr
  exact cut_map_ball_bound μ₁ μ₂ μ₃ τ σ D hdom hτ g₁ g₂ g₃ hg₁ hg₂ hg₃
    s hs N hP₁ hP₂ hP₃ x r hr

end StickyKakeya4.TriangularPotentialEscape
