import Theorems.Thm_StickyKakeya4_triangular_borel_front_escape
import Theorems.Thm_StickyKakeya4_rational_feedback_time_window
import Theorems.Thm_StickyKakeya4_time_changed_scalar_energy
import Theorems.Thm_StickyKakeya4_rank_one_native_potentials

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology Matrix.Norms.Operator
noncomputable section
namespace StickyKakeya4.RankOneBorelFrontEscape
open ScalarProjection TriangularPotentialEscape EnergyDimension

/-- The cut is measured through the literal point map. Only a fixed-time spatial
normalization enters the ball estimate; no regularity in time of that normalization
is required. -/
theorem original_cut_map_ball_bound
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (σ : Measure Source) [IsFiniteMeasure σ]
    (D : ℝ≥0∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (a b : ℝ) (B : ℝ) (hB : 0 < B)
    (g₁ : ℝ × ℝ → ℝ) (g₂ : ℝ × (ℝ × ℝ) → ℝ)
    (g₃ : ℝ × Source → ℝ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hg₃ : Measurable g₃)
    (F : ℝ × Source → E4) (hF : Measurable F)
    (hheight : ∀ p, F p 3 = p.1)
    (center : ℝ → E4 → Fin 3 → ℝ)
    (hgeom : ∀ t ∈ Icc a b, ∀ z x r, 0 < r → F (t,z) ∈ Metric.ball x r →
      g₁ (t,z.1.1) ∈ Metric.ball (center t x 0) (B*r) ∧
      g₂ (t,z.1) ∈ Metric.ball (center t x 1) (B*r) ∧
      g₃ (t,z) ∈ Metric.ball (center t x 2) (B*r))
    (s : ℝ) (hs : 0 < s) (N : ℝ≥0∞)
    (hP₁ : Measurable (potential₁ μ₁ g₁ s))
    (hP₂ : Measurable (potential₂ μ₂ g₂ s))
    (hP₃ : Measurable (potential₃ μ₃ g₃ s))
    (x : E4) (r : ℝ) (hr : 0 < r) :
    ((((volume.restrict (Icc a b)).prod σ).restrict
      (potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N)).map F) (Metric.ball x r) ≤
      (D * (N * (2 : ℝ≥0∞)^s)^3 * ENNReal.ofReal B^(3*s) * 2) *
        ENNReal.ofReal r^(1+3*s) := by
  let G := potentialCut μ₁ μ₂ μ₃ g₁ g₂ g₃ s N
  let H := G ∩ (Icc a b ×ˢ (univ : Set Source))
  let E : Set (ℝ × Source) := F ⁻¹' Metric.ball x r ∩ H
  let C := (N * (2 : ℝ≥0∞)^s) * ENNReal.ofReal (B*r)^s
  have hG : MeasurableSet G := measurableSet_potentialCut _ _ _ _ _ _ _ _ hP₁ hP₂ hP₃
  have hH : MeasurableSet H := hG.inter (measurableSet_Icc.prod MeasurableSet.univ)
  have hE : MeasurableSet E := (Metric.isOpen_ball.measurableSet.preimage hF).inter hH
  have hsub : E ⊆ Prod.fst ⁻¹' Metric.ball (x 3) r := by
    intro p hp
    simpa only [hheight, mem_preimage] using coordinate_mem_ball hp.1 3
  have hsec : ∀ t, σ (Prod.mk t ⁻¹' E) ≤ D*C^3 := by
    intro t
    have href : ((μ₁.prod μ₂).prod μ₃) (Prod.mk t ⁻¹' E) ≤ C^3 := by
      refine (measure_mono ?_).trans
        (triangular_box_bound μ₁ μ₂ μ₃ g₁ g₂ g₃ hg₁ hg₂ hg₃ s hs N
          hP₁ hP₂ hP₃ t (center t x 0) (center t x 1) (center t x 2)
          (B*r) (mul_pos hB hr))
      intro z hz
      exact ⟨hz.2.1, hgeom t hz.2.2.1 z x r hr hz.1⟩
    exact (hdom _).trans (by simpa only [Measure.smul_apply, smul_eq_mul] using
      (mul_le_mul_right href D))
  have hbound : (volume.prod σ) E ≤ (D*C^3)*ENNReal.ofReal (2*r) := by
    simpa only [Real.volume_ball] using prod_event_le volume σ E hE
      (Metric.ball (x 3) r) Metric.isOpen_ball.measurableSet (D*C^3) hsub hsec
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict hG,
    Measure.map_apply hF Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (Metric.isOpen_ball.measurableSet.preimage hF)]
  calc
    (volume.prod σ) E ≤ (D*C^3)*ENNReal.ofReal (2*r) := hbound
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hp (z : ℝ≥0∞) : (z^s)^(3:ℕ) = z^(3*s) := by
        rw [mul_comm (3:ℝ) s, ENNReal.rpow_mul]
        norm_num
      rw [ENNReal.rpow_add_of_nonneg 1 (3*s) (by norm_num) (by positivity),
        ENNReal.rpow_one]
      dsimp [C]
      rw [mul_pow, hp, ENNReal.ofReal_mul hB.le, ENNReal.mul_rpow_of_nonneg _ _
        (show 0 ≤ 3*s by positivity), ENNReal.ofReal_ofNat]
      simp only [mul_assoc, mul_left_comm, mul_comm]

abbrev Vector := Fin 3 → ℝ
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

def sourceVector (z : Source) : Vector := ![z.1.1,z.1.2,z.2]
def spatial (L : Matrix3) (u c : Vector) (f : ℝ → ℝ)
    (p : ℝ × Source) : Vector := c + L.mulVec (sourceVector p.2) +
      (f p.2.1.1) • u + p.1 • sourceVector p.2

def actualPoint (L : Matrix3) (u c : Vector) (f : ℝ → ℝ)
    (p : ℝ × Source) : E4 := WithLp.toLp 2
      ![spatial L u c f p 0, spatial L u c f p 1, spatial L u c f p 2, p.1]

def feedbackVector (L : Matrix3) (u : Vector) (t : ℝ) : Vector :=
  (L + t • 1)⁻¹.mulVec u

def normal₁ (L : Matrix3) (u : Vector) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 + feedbackVector L u p.1 0 * f p.2

def normal₂ (L : Matrix3) (u : Vector) (f : ℝ → ℝ)
    (p : ℝ × (ℝ × ℝ)) : ℝ := p.2.2 + feedbackVector L u p.1 1 * f p.2.1

def normal₃ (L : Matrix3) (u : Vector) (f : ℝ → ℝ)
    (p : ℝ × Source) : ℝ := p.2.2 + feedbackVector L u p.1 2 * f p.2.1.1


theorem measurable_feedbackVector (L : Matrix3) (u : Vector) :
    Measurable (feedbackVector L u) := by
  apply measurable_pi_lambda
  intro i
  have he : (fun t => feedbackVector L u t i) = fun t =>
      (RankOneFeedbackPolynomials.numerator L u (Pi.single i 1)).eval t /
        (RankOneFeedbackPolynomials.denominator L).eval t := by
    funext t
    simpa only [feedbackVector, single_dotProduct, one_mul] using
      RankOneFeedbackPolynomials.inverse_feedback L u (Pi.single i 1) t
  rw [he]
  exact (RankOneFeedbackPolynomials.numerator L u (Pi.single i 1)).continuous.measurable.div
    (RankOneFeedbackPolynomials.denominator L).continuous.measurable

theorem measurable_actualPoint (L : Matrix3) (u c : Vector) (f : ℝ → ℝ)
    (hf : Measurable f) : Measurable (actualPoint L u c f) := by
  have hz (j : Fin 3) : Measurable (fun p : ℝ × Source => sourceVector p.2 j) := by
    fin_cases j <;> dsimp [sourceVector] <;> fun_prop
  have hsp (j : Fin 3) : Measurable (fun p => spatial L u c f p j) := by
    simp only [spatial, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    fun_prop
  unfold actualPoint
  apply (WithLp.measurable_toLp 2 (Fin 4 → ℝ)).comp
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact hsp 0
  · exact hsp 1
  · exact hsp 2
  · exact measurable_fst

theorem measurable_normals (L : Matrix3) (u : Vector) (f : ℝ → ℝ)
    (hf : Measurable f) : Measurable (normal₁ L u f) ∧
      Measurable (normal₂ L u f) ∧ Measurable (normal₃ L u f) := by
  have hw := measurable_feedbackVector L u
  unfold normal₁ normal₂ normal₃
  constructor
  · fun_prop
  constructor <;> fun_prop

theorem normalized_spatial (L : Matrix3) (u c : Vector) (f : ℝ → ℝ)
    (t : ℝ) (z : Source) (hdet : (L + t • (1 : Matrix3)).det ≠ 0) :
    (L + t • (1 : Matrix3))⁻¹.mulVec (spatial L u c f (t,z) - c) =
      sourceVector z + f z.1.1 • feedbackVector L u t := by
  have he : spatial L u c f (t,z) - c =
      (L+t • (1:Matrix3)).mulVec (sourceVector z) + f z.1.1 • u := by
    simp only [spatial, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    abel
  rw [he, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  rfl

def outputCenter (L : Matrix3) (c : Vector) (t : ℝ) (x : E4) : Vector :=
  (L+t • (1:Matrix3))⁻¹.mulVec (![x 0,x 1,x 2]-c)

theorem normalization_coordinate_ball (L : Matrix3) (u c : Vector)
    (f : ℝ → ℝ) (t : ℝ) (z : Source) (x : E4) (r B : ℝ)
    (hB : 0 < B) (hdet : (L+t • (1:Matrix3)).det ≠ 0)
    (hbound : ‖(L+t • (1:Matrix3))⁻¹‖ ≤ B)
    (hball : actualPoint L u c f (t,z) ∈ Metric.ball x r) :
    normal₁ L u f (t,z.1.1) ∈ Metric.ball (outputCenter L c t x 0) (B*r) ∧
    normal₂ L u f (t,z.1) ∈ Metric.ball (outputCenter L c t x 1) (B*r) ∧
    normal₃ L u f (t,z) ∈ Metric.ball (outputCenter L c t x 2) (B*r) := by
  let y : Vector := ![x 0,x 1,x 2]
  have hsp : ‖spatial L u c f (t,z)-y‖ < r := by
    apply (pi_norm_lt_iff (by exact Metric.pos_of_mem_ball hball)).2
    intro i
    have he (j : Fin 3) : spatial L u c f (t,z) j =
        actualPoint L u c f (t,z) j.castSucc := by fin_cases j <;> rfl
    have hy (j : Fin 3) : y j = x j.castSucc := by fin_cases j <;> rfl
    rw [Pi.sub_apply, he, hy]
    simpa only [Metric.mem_ball, dist_eq_norm] using coordinate_mem_ball hball i.castSucc

  have hnorm : ‖(L+t • (1:Matrix3))⁻¹.mulVec (spatial L u c f (t,z)-y)‖ < B*r :=
    (Matrix.linfty_opNorm_mulVec _ _).trans_lt
      ((mul_le_mul_of_nonneg_right hbound (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hsp hB))
  have he : (L+t • (1:Matrix3))⁻¹.mulVec (spatial L u c f (t,z)-y) =
      sourceVector z + f z.1.1 • feedbackVector L u t - outputCenter L c t x := by
    rw [← normalized_spatial L u c f t z hdet]
    dsimp [outputCenter]
    rw [← Matrix.mulVec_sub]
    congr 1
    dsimp [y]
    abel
  rw [he] at hnorm
  have hi (i : Fin 3) := (norm_le_pi_norm
    (sourceVector z + f z.1.1 • feedbackVector L u t - outputCenter L c t x) i).trans_lt hnorm
  constructor
  · have hh := hi 0
    change |z.1.1 + f z.1.1 * feedbackVector L u t 0 - outputCenter L c t x 0| < B*r at hh
    simpa only [normal₁, Metric.mem_ball, Real.dist_eq, mul_comm] using hh
  constructor
  · have hh := hi 1
    change |z.1.2 + f z.1.1 * feedbackVector L u t 1 - outputCenter L c t x 1| < B*r at hh
    simpa only [normal₂, Metric.mem_ball, Real.dist_eq, mul_comm] using hh
  · have hh := hi 2
    change |z.2 + f z.1.1 * feedbackVector L u t 2 - outputCenter L c t x 2| < B*r at hh
    simpa only [normal₃, Metric.mem_ball, Real.dist_eq, mul_comm] using hh


/-- Nonsingularity and first-coordinate potential finiteness are both obtained
inside the specified original time interval. -/
theorem exists_actual_native_window
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ) (hD : 0 ≤ D) (hμ : μ ≤ ENNReal.ofReal D • volume)
    (L : Matrix3) (u : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (lo hi : ℝ) (hlohi : lo < hi) (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ a b B : ℝ, lo < a ∧ a < b ∧ b < hi ∧ 0 < B ∧
      (∀ t ∈ Icc a b, (L+t • (1:Matrix3)).det ≠ 0) ∧
      (∀ t ∈ Icc a b, ‖(L+t • (1:Matrix3))⁻¹‖ ≤ B) ∧
      (∀ᵐ p ∂(volume.restrict (Icc a b)).prod μ,
        potential₁ μ (normal₁ L u f) s p < ∞) := by
  have hk : Measurable (fun t => feedbackVector L u t 0) :=
    (measurable_pi_apply 0).comp (measurable_feedbackVector L u)
  have he (t : ℝ) : RationalFeedbackTimeWindow.feedbackScalar L u (Pi.single 0 1) t =
      feedbackVector L u t 0 := by
    simp only [RationalFeedbackTimeWindow.feedbackScalar, single_dotProduct,
      one_mul, feedbackVector]
  rcases RationalFeedbackTimeWindow.actual_feedback_zero_or_time_window
    L u (Pi.single 0 1) hlohi with hzero | hwin
  · obtain ⟨a,b,δ,B,hla,hab,hbh,hδ,hB,hdet,hbound⟩ :=
      RationalFeedbackTimeWindow.exists_matrix_time_window L hlohi
    refine ⟨a,b,B,hla,hab,hbh,hB,?_,hbound,?_⟩
    · intro t ht
      exact abs_pos.mp (hδ.trans_le (hdet t ht))
    · exact RankOneNativePotentials.ae_finite_zero_feedback_potential₁ μ D hD hμ
        f (fun t => feedbackVector L u t 0) hf hk a b
        (fun t _ => (he t).symm.trans (hzero t)) s hs hs1
  · obtain ⟨a,b,δ,kmin,kmax,c,C,B,hla,hab,hbh,hδ,hmin,_hmax,hc,_hC,hB,
      hbounds,_hcont,_hmeas,hco,_hLip,hbound⟩ := hwin
    refine ⟨a,b,B,hla,hab,hbh,hB,?_,hbound,?_⟩
    · intro t ht
      exact abs_pos.mp (hδ.trans_le (hbounds t ht).1)
    · apply RankOneNativePotentials.ae_finite_feedback_potential₁ μ D hD hμ
        f (fun t => feedbackVector L u t 0) hf hk a b c hc
        (fun t ht => ?_) (fun t ht v hv => ?_) s hs hs1
      · rw [← he]
        exact abs_pos.mp (hmin.trans_le (hbounds t ht).2.1)
      · simpa only [he] using hco v hv t ht

/-- Actual fronts with intercept c+Lx+u f(x₁), for arbitrary matrix L, vectors c,u,
and Borel scalar f, carry every 1+3s Frostman exponent. No time-window or
potential-finiteness certificate is assumed. -/
theorem exists_rank_one_borel_supported_frostman
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (actualPoint L u c f)) Kᶜ = 0)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C * ENNReal.ofReal r^(1+3*s) := by
  obtain ⟨a,b,B,hla,hab,hbh,hB,hdet,hbound,ha₁⟩ :=
    exists_actual_native_window μ₁ D₁ hD₁ hμ₁ L u f hf lo hi hlohi s hs hs1
  let τ : Measure ℝ := volume.restrict (Icc a b)
  let ρ : Measure Source := (μ₁.prod μ₂).prod μ₃
  have hw := measurable_feedbackVector L u
  obtain ⟨hg₁,hg₂,hg₃⟩ := measurable_normals L u f hf
  have hP₁ : Measurable (potential₁ μ₁ (normal₁ L u f) s) :=
    RankOneNativePotentials.measurable_potential₁ μ₁ _ hg₁ s
  have hP₂ : Measurable (potential₂ μ₂ (normal₂ L u f) s) :=
    RankOneNativePotentials.measurable_nativeOwnPotential μ₂ _ hg₂ s
  have hP₃ : Measurable (potential₃ μ₃ (normal₃ L u f) s) :=
    RankOneNativePotentials.measurable_nativeOwnPotential μ₃ _ hg₃ s
  have ha₂ : ∀ᵐ p ∂τ.prod (μ₁.prod μ₂), potential₂ μ₂ (normal₂ L u f) s p < ∞ :=
    RankOneNativePotentials.ae_finite_translated_nativeOwnPotential τ μ₁ μ₂ D₂ hD₂ hμ₂
      (fun p : ℝ × ℝ => feedbackVector L u p.1 1 * f p.2) (by fun_prop) s hs hs1
  have ha₃ : ∀ᵐ p ∂τ.prod ρ, potential₃ μ₃ (normal₃ L u f) s p < ∞ :=
    RankOneNativePotentials.ae_finite_translated_nativeOwnPotential τ (μ₁.prod μ₂) μ₃ D₃ hD₃ hμ₃
      (fun p : ℝ × (ℝ × ℝ) => feedbackVector L u p.1 2 * f p.2.1) (by fun_prop) s hs hs1
  have hr₁ : ∀ᵐ p ∂τ.prod ρ, potential₁ μ₁ (normal₁ L u f) s (p.1,p.2.1.1) < ∞ :=
    TriangularBorelFrontEscape.ae_finite_lift_right τ (μ₁.prod μ₂) μ₃
      (fun p => potential₁ μ₁ (normal₁ L u f) s (p.1,p.2.1)) (hP₁.comp (by fun_prop))
      (TriangularBorelFrontEscape.ae_finite_lift_right τ μ₁ μ₂ _ hP₁ ha₁)
  have hr₂ : ∀ᵐ p ∂τ.prod ρ, potential₂ μ₂ (normal₂ L u f) s (p.1,p.2.1) < ∞ :=
    TriangularBorelFrontEscape.ae_finite_lift_right τ (μ₁.prod μ₂) μ₃ _ hP₂ ha₂
  have hac : τ.prod σ ≪ τ.prod ρ :=
    Measure.AbsolutelyContinuous.rfl.prod (Measure.absolutelyContinuous_of_le_smul hdom)
  have hτu : τ univ ≠ 0 := by
    simp [τ, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le.mpr hab]
  have hσu : σ univ ≠ 0 := fun hz => hσ (Measure.measure_univ_eq_zero.mp hz)
  have hsource : τ.prod σ ≠ 0 := by
    intro hz
    have hh : (τ.prod σ) (univ ×ˢ univ) ≠ 0 := by
      rw [Measure.prod_prod]
      exact mul_ne_zero hτu hσu
    simp [hz] at hh
  obtain ⟨N,hN⟩ := exists_common_potential_cut (τ.prod σ) hsource
    (fun p => potential₁ μ₁ (normal₁ L u f) s (p.1,p.2.1.1))
    (fun p => potential₂ μ₂ (normal₂ L u f) s (p.1,p.2.1))
    (potential₃ μ₃ (normal₃ L u f) s) (hP₁.comp (by fun_prop))
    (hP₂.comp (by fun_prop)) hP₃ (hac.ae_le hr₁) (hac.ae_le hr₂) (hac.ae_le ha₃)
  let G := potentialCut μ₁ μ₂ μ₃ (normal₁ L u f) (normal₂ L u f) (normal₃ L u f) s N
  let F := actualPoint L u c f
  let ν₀ := ((τ.prod σ).restrict G).map F
  have hF : Measurable F := measurable_actualPoint L u c f hf
  have hnz : ν₀ ≠ 0 := by
    apply (Measure.map_ne_zero_iff hF.aemeasurable).mpr
    intro hz
    exact hN (Measure.restrict_eq_zero.mp hz)
  have htime : τ ≤ volume.restrict (Icc lo hi) :=
    Measure.restrict_mono_set volume (Icc_subset_Icc hla.le hbh.le)
  have hsν : ν₀ Kᶜ = 0 := by
    apply le_antisymm _ bot_le
    exact ((Measure.map_mono Measure.restrict_le_self hF Kᶜ).trans
      (Measure.map_mono (Measure.prod_mono htime le_rfl) hF Kᶜ)).trans_eq hsupport
  let C : ℝ≥0∞ := D * ((N:ℝ≥0∞)*(2:ℝ≥0∞)^s)^3 * ENNReal.ofReal B^(3*s)*2
  have hC : C ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top hD
        exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.rpow_ne_top_of_nonneg hs.le (by norm_num)))
      · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    · norm_num
  apply normalize_supported_ball_bound ν₀ hnz K hsν (1+3*s) C hC
  intro x r hr
  exact original_cut_map_ball_bound μ₁ μ₂ μ₃ σ D hdom a b B hB
    (normal₁ L u f) (normal₂ L u f) (normal₃ L u f) hg₁ hg₂ hg₃ F hF
    (fun _ => rfl) (outputCenter L c)
    (fun t ht z x r _ hball => normalization_coordinate_ball L u c f t z x r B
      hB (hdet t ht) (hbound t ht) hball) s hs N hP₁ hP₂ hP₃ x r hr

/-- The literal original front of c+Lx+u f(x₁) has Hausdorff dimension four.
The matrix may have arbitrary cyclic linear coupling, and u may be zero. -/
theorem rank_one_borel_front_dimH_eq_four
    (μ₁ μ₂ μ₃ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃]
    (D₁ D₂ D₃ : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (hμ₁ : μ₁ ≤ ENNReal.ofReal D₁ • volume)
    (hμ₂ : μ₂ ≤ ENNReal.ofReal D₂ • volume)
    (hμ₃ : μ₃ ≤ ENNReal.ofReal D₃ • volume)
    (σ : Measure Source) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    (D : ℝ≥0∞) (hD : D ≠ ∞) (hdom : σ ≤ D • ((μ₁.prod μ₂).prod μ₃))
    (lo hi : ℝ) (hlohi : lo < hi)
    (L : Matrix3) (u c : Vector) (f : ℝ → ℝ) (hf : Measurable f)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc lo hi)).prod σ).map
      (actualPoint L u c f)) Kᶜ = 0) : dimH K = 4 := by
  apply TriangularBorelFrontEscape.dimH_eq_four_of_triangular_frostman K
  intro s hs hs1
  exact exists_rank_one_borel_supported_frostman μ₁ μ₂ μ₃ D₁ D₂ D₃
    hD₁ hD₂ hD₃ hμ₁ hμ₂ hμ₃ σ hσ D hD hdom lo hi hlohi L u c f hf
    K hsupport s hs hs1

end StickyKakeya4.RankOneBorelFrontEscape
