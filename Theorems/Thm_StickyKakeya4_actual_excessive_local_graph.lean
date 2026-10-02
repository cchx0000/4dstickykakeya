import Theorems.Thm_StickyKakeya4_actual_residual_phase_localization
import Theorems.Thm_StickyKakeya4_angular_residual_excess
import Theorems.Thm_StickyKakeya4_residual_affine_rescaling
import Theorems.Thm_StickyKakeya4_local_seed_absorption
import Theorems.Thm_StickyKakeya4_front_affine_dimension_transport
import Theorems.Thm_StickyKakeya4_source_chart_carrier_lipschitz

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

noncomputable section

namespace StickyKakeya4.ActualExcessiveLocalGraph

open ActualSlopeSource PositiveCellRegularization PackingReferenceSource
open ActualResidualPhaseLocalization ResidualPhaseLocalization ActualShellGraph
open AngularResidualShell AngularResidualExcess ResidualAffineRescaling NoFrostmanResidualExcess

/-- The actual affine slope normalization is a measurable equivalence. -/
def normalizedSlopeEquiv (a₀ : E3) (τ : ℝ) (hτ : τ ≠ 0) : E3 ≃ᵐ E3 where
  toFun := normalizedSlope a₀ τ
  invFun := physicalSlope a₀ τ
  left_inv := fun a => physicalSlope_normalizedSlope a₀ a τ hτ
  right_inv := fun x => normalizedSlope_physicalSlope a₀ x τ hτ
  measurable_toFun := measurable_normalizedSlope a₀ τ
  measurable_invFun := by
    change Measurable (physicalSlope a₀ τ)
    unfold physicalSlope
    fun_prop

/-- Every dominated restriction of the literal shell graph has the same
physical shell, residual, and closest-time support after normalization. No
symmetry is asserted: a first-hit assigned graph is directed. -/
theorem normalized_directed_shell_support
    (σ μ : Measure E3) (B : Set E3) (hB : MeasurableSet B)
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (ρ τ : ℝ) (hτ : 0 < τ) (Γ : Measure (E3 × E3))
    (hΓ : Γ ≤ graphMeasure σ (shellGraphWeight B b J ρ τ)) (a₀ : E3) :
    ∀ᵐ p ∂normalizedDirectedGraph μ Γ a₀ τ,
      1 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 ∧
      ‖collisionResidual (p.1 - p.2)
        (normalizedIntercept b a₀ τ p.1 - normalizedIntercept b a₀ τ p.2)‖ ≤ ρ / τ ∧
      collisionTime (p.1 - p.2)
        (normalizedIntercept b a₀ τ p.1 - normalizedIntercept b a₀ τ p.2) ∈ J := by
  have hsupport : ∀ᵐ p ∂graphMeasure σ (shellGraphWeight B b J ρ τ),
      p.1 ∈ B ∧ p.2 ∈ B ∧ τ < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 * τ ∧
        ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ ρ ∧
        collisionTime (p.1 - p.2) (b p.1 - b p.2) ∈ J := by
    apply (ae_withDensity_iff (measurable_shellGraphWeight B hB b hb J hJ ρ τ)).mpr
    exact ae_of_all _ fun p hp => shellGraphWeight_ne_zero_support B b J ρ τ p hp
  have horiginal := hsupport.filter_mono (ae_mono hΓ)
  apply Measure.ae_smul_measure
  have hemb : MeasurableEmbedding
      (Prod.map (normalizedSlope a₀ τ) (normalizedSlope a₀ τ)) :=
    ((normalizedSlopeEquiv a₀ τ hτ.ne').prodCongr
      (normalizedSlopeEquiv a₀ τ hτ.ne')).measurableEmbedding
  apply hemb.ae_map_iff.mpr
  filter_upwards [horiginal] with p hp
  obtain ⟨hlo, hhi⟩ := (normalized_shell_iff a₀ p.1 p.2 τ hτ).mpr ⟨hp.2.2.1, hp.2.2.2.1⟩
  obtain ⟨hres, htime⟩ := (normalized_residual_time_iff b a₀ p.1 p.2 τ ρ hτ J).mpr hp.2.2.2.2
  exact ⟨hlo, hhi, hres, htime⟩

/-- For each fixed affine normalization, the actual source front is supported
on that affine image of the original front. This is not a weak-limit support
transfer across moving normalizations. -/
theorem normalized_source_front_support
    (μ : Measure E3) (b : E3 → E3) (a₀ : E3) (τ : ℝ) (hτ : 0 < τ)
    (u v : ℝ) (front : Set E4)
    (hsupport : ∀ᵐ a ∂μ, ∀ s ∈ Icc u v, heightPoint (b a + s • a) s ∈ front) :
    ∀ᵐ a ∂normalizedSource μ a₀ τ, ∀ s ∈ Icc u v,
      heightPoint (normalizedIntercept b a₀ τ a + s • a) s ∈
        frontAffineEquiv4 a₀ (b a₀) τ hτ.ne' '' front := by
  apply Measure.ae_smul_measure
  apply (normalizedSlopeEquiv a₀ τ hτ.ne').measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hsupport] with a ha
  intro s hs
  exact (normalized_frontPoint_mem_image_iff b a₀ a τ s hτ.ne' front).mpr (ha s hs)

/-- The literal shell content remains finite on an actual finite
slope-volume-dominated source, independently of the collision radius. -/
theorem angularShellContent_ne_top
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (J : Set ℝ) (ρ lo hi : ℝ) :
    angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
      (fun p => b p.1 - b p.2) J ρ lo hi ≠ ⊤ := by
  have hle : angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
      (fun p => b p.1 - b p.2) J ρ lo hi ≤
      weightedResidualContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  exact ne_top_of_le_ne_top
    (NoFrostmanWeightedResidualDecay.finite_inverse_secant_integral σ hσ).ne
    (hle.trans (weightedResidualContent_le_inverse_secant_integral σ b J ρ))

/-- A strict dimension deficit produces arbitrarily fine excessive directed
physical graphs, without any excessive-graph or normalized-density premise.

The residual exponent is chosen first, then the regularization slack
`ζ = η²/64`, then one fixed positive original source. Every subsequent graph
is a genuine first-hit restriction of its literal angular residual graph.
Normalization uses one actual source point and transports both endpoints by
the same affine map. One fixed finite chart bound controls both normalized
slopes and intercepts at every later radius. No graph symmetry or moving-limit support transfer is
asserted. -/
theorem sticky_deficit_exists_excessive_directed_seed
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (hdim : dimH (unitFront ambient) < (4 : ENNReal)) :
    ∃ η : ℝ, 0 < η ∧ η < 2 ∧
      ∃ (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
        (hvalid : ∀ line ∈ selector, IsValidLine line)
        (hselector : IsDirectionSelector selector), selector ⊆ ambient ∧
        ∃ (k : ℤ) (B : Set E3), MeasurableSet B ∧
          B ⊆ sourceSet selector hmeas hvalid hselector k ∧
          0 < (volume : Measure E3) B ∧ IsFiniteMeasure ((volume : Measure E3).restrict B) ∧
          ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε →
            let σ := (volume : Measure E3).restrict B
            let b := intercept selector hmeas hvalid hselector
            ∃ (ρ τ : ℝ) (hτ : 0 < τ) (a₀ : E3) (D : Set E3) (Γ : Measure (E3 × E3)),
              0 < ρ ∧ ρ < 1 ∧ τ ≤ 2 ∧ 0 < ρ / τ ∧ ρ / τ < ε ∧
              MeasurableSet D ∧ a₀ ∈ B ∧ a₀ ∈ D ∧ 0 < (σ D).toReal ∧
              Γ ≤ graphMeasure σ (shellGraphWeight B b
                (Icc (((k : ℝ) / 8 - 1 / 8) - 1) (((k : ℝ) / 8 + 1 / 4) + 1)) ρ τ) ∧
              Γ ≤ (σ.restrict D).prod (σ.restrict D) ∧
              let μ := normalizedSource (σ.restrict D) a₀ τ
              let G := normalizedDirectedGraph (σ.restrict D) Γ a₀ τ
              let b' := normalizedIntercept b a₀ τ
              IsProbabilityMeasure μ ∧ Measurable b' ∧ G ≤ μ.prod μ ∧
              (ρ / τ) ^ (2 - η / 4) ≤ (G Set.univ).toReal ∧
              μ ≤ ENNReal.ofReal ((ρ / τ) ^ (-η / 8)) • (volume : Measure E3) ∧
              (∀ᵐ a ∂μ, ‖a‖ ≤ A ∧ ‖b' a‖ ≤ A) ∧
              (∀ᵐ p ∂G, 1 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 ∧
                ‖collisionResidual (p.1 - p.2) (b' p.1 - b' p.2)‖ ≤ ρ / τ ∧
                collisionTime (p.1 - p.2) (b' p.1 - b' p.2) ∈
                  Icc (((k : ℝ) / 8 - 1 / 8) - 1) (((k : ℝ) / 8 + 1 / 4) + 1)) ∧
              (∀ᵐ a ∂μ, ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
                heightPoint (b' a + s • a) s ∈
                  frontAffineEquiv4 a₀ (b a₀) τ hτ.ne' '' unitFront ambient) ∧
              dimH (frontAffineEquiv4 a₀ (b a₀) τ hτ.ne' '' unitFront ambient) < 4 := by
  obtain ⟨η, t, hη, hη2, ht, htt, hdimt⟩ :=
    exists_residual_exponent_gap_of_dimH_lt_four (unitFront ambient) hdim
  let ζ : ℝ := η ^ 2 / 64
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, carrier, c, nets,
      hB, hBsource, hBpos, hfinite, _hcarrier, _hcompact, _hBsupport, hc, hc1,
      _hnetcarrier, _hnetsep, _hnetcover, hfront, hlocal⟩ :=
    sticky_datum_exists_uniform_actual_shell_localization ambient hsticky ζ hζ
  let σ : Measure E3 := (volume : Measure E3).restrict B
  let : IsFiniteMeasure σ := hfinite
  let b := intercept selector hmeas hvalid hselector
  let f := slopeCarrierMap selector hmeas hvalid hselector
  let u : ℝ := (k : ℝ) / 8 - 1 / 8
  let v : ℝ := (k : ℝ) / 8 + 1 / 4
  let J : Set ℝ := Icc (u - 1) (v + 1)
  let S : ℝ := |u - 1| + |v + 1|
  have hS : 0 ≤ S := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hJS : ∀ s ∈ J, |s| ≤ S := by
    intro s hs
    apply abs_le.mpr
    have hleft := neg_abs_le (u - 1)
    have hright := le_abs_self (v + 1)
    constructor <;> dsimp [S] <;> linarith [hs.1, hs.2, abs_nonneg (u - 1), abs_nonneg (v + 1)]
  obtain ⟨L, C, hL, hC, K, hlocal⟩ := hlocal S hS
  have hσpos : 0 < σ Set.univ := by simpa only [σ, Measure.restrict_apply_univ] using hBpos
  have hσ : σ ≤ volume := Measure.restrict_le_self
  have hb : Measurable b := measurable_intercept selector hmeas hvalid hselector
  have hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem hB] with a ha
    exact (show ‖a‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right]
      using (hBsource ha).1).le
  have hfrontσ : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v, heightPoint (b a + s • a) s ∈ unitFront ambient := by
    filter_upwards [ae_restrict_mem hB] with a ha
    exact hfront a ha
  have huv : u < v := by dsimp [u, v]; linarith
  have hexcess : ∀ ρ₀ : ℝ, 0 < ρ₀ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < min ρ₀ 1 ∧
      (ENNReal.ofReal ρ) ^ (2 - η) < weightedResidualContent (σ.prod σ)
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J ρ := by
    intro ρ₀ hρ₀
    simpa only [one_mul] using arbitrarily_fine_residual_excess_of_dimH_lt
      ambient hsticky.1 σ hσpos hσ b hb hunit u v 1 η t huv (by norm_num)
      hη hη2 ht htt hfrontσ hdimt 1 (by norm_num) ρ₀ hρ₀
  let H : ℝ := C * (K : ℝ) * (σ Set.univ).toReal
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) ENNReal.toReal_nonneg
  have hH1 : 0 < H + 1 := by linarith
  let F : ℝ := 2 ^ (3 + ζ) / c.toReal
  have hcReal : 0 < c.toReal :=
    ENNReal.toReal_pos hc.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨R, hR0, hR⟩ := compact_offset_bound ambient hsticky.1
  let A : ℝ := (16 + 12 * R) * (L + 2)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨η, hη, hη2, selector, hmeas, hvalid, hselector, hsubset, k, B,
    hB, hBsource, hBpos, hfinite, A, hA, ?_⟩
  intro ε hε
  obtain ⟨ε₀, hε₀, hε₀ε, habsorb⟩ := LocalSeedAbsorption.exists_local_seed_threshold
    hη hH1 hF hε
  obtain ⟨ρ, τ, hρ, hρsmall, hτ, hcut, hτ2, hr, _hrpow, hrsmall, hshell, htax⟩ :=
    arbitrarily_fine_shell_excess_of_full_excess σ hσ b hb hunit J measurableSet_Icc
      η hη (by linarith) hexcess 1 ε₀ (by norm_num) hε₀
  have hρ1 : ρ < 1 := hρsmall.trans_le (min_le_right _ _)
  have hρτ : ρ ≤ τ := (scaled_radius_le_rpow ρ τ η hρ hρ1.le hη hcut).2.2
  let Z := angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
    (fun p => b p.1 - b p.2) J ρ τ (2 * τ)
  have hZpos : 0 < Z :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hρ) ENNReal.ofReal_ne_top).trans hshell
  have hZtop : Z ≠ ⊤ := angularShellContent_ne_top σ hσ b J ρ τ (2 * τ)
  have hshellReal : ρ ^ (2 - η / 2) < Z.toReal := by
    have h := (ENNReal.toReal_lt_toReal
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hρ).ne' ENNReal.ofReal_ne_top)
      hZtop).mpr hshell
    simpa only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hρ.le] using h
  obtain ⟨j, hδτ, _hτδ, hloc, _hmass, _hupper, _hlower, i, himass, hdensity, hcost, _hball⟩ :=
    hlocal J measurableSet_Icc hJS ρ τ hτ hτ2 hρτ hZpos
  let D := phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i
  let Γ := assignedGraph (graphMeasure σ (shellGraphWeight B b J ρ τ))
    (phaseCover f (indexedCenters (nets j)) (dyadicRadius j)) i
  have hD : MeasurableSet D := hloc.blocks_measurable i
  have hDpos : 0 < (σ D).toReal := himass
  have hHpos : 0 < H := by
    have hd := hloc.positive_square_mass.trans_le hloc.square_mass_budget
    have hprod : 0 < H * dyadicRadius j ^ (3 : ℕ) := by
      simpa only [H, mul_assoc, mul_left_comm, mul_comm] using hd
    exact (mul_pos_iff_of_pos_right (pow_pos (dyadicRadius_pos j) 3)).mp hprod
  have hdensity' : Z.toReal / ((H + 1) * τ ^ (2 : ℕ)) ≤
      (Γ Set.univ).toReal / (σ D).toReal ^ 2 := by
    apply (div_le_div_of_nonneg_left ENNReal.toReal_nonneg
      (mul_pos hHpos (pow_pos hτ 2))
      (mul_le_mul_of_nonneg_right (show H ≤ H + 1 by linarith) (by positivity))).trans
    exact hdensity
  have htax' : τ ^ (-ζ) ≤ (ρ / τ) ^ (-(4 * ζ / η)) := by
    simpa only [neg_mul, neg_div] using htax ζ hζ.le
  obtain ⟨hmassSeed, hcostSeed⟩ := habsorb ρ τ Z.toReal
    ((Γ Set.univ).toReal / (σ D).toReal ^ 2) (τ ^ (3 : ℕ) / (σ D).toReal) ζ
    hρ hτ hτ2 hrsmall.le hshellReal hdensity' rfl htax' hcost
  have hDposENN : 0 < σ D := (ENNReal.toReal_pos_iff.mp hDpos).1
  have hvol : 0 < (volume : Measure E3) (D ∩ B) := by
    simpa only [σ, Measure.restrict_apply hD] using hDposENN
  obtain ⟨a₀, ha₀D, ha₀B⟩ := nonempty_of_measure_ne_zero hvol.ne'
  let μ : Measure E3 := σ.restrict D
  have hμpos : 0 < μ Set.univ := by simpa only [μ, Measure.restrict_apply_univ] using hDposENN
  have hμ : μ ≤ volume := Measure.restrict_le_self.trans hσ
  have hΓdom : Γ ≤ μ.prod μ := by
    rw [show μ = σ.restrict D from rfl, Measure.prod_restrict]
    exact hloc.block_domination i
  have hΓshell : Γ ≤ graphMeasure σ (shellGraphWeight B b J ρ τ) := Measure.restrict_le_self
  have hfrontμ : ∀ᵐ a ∂μ, ∀ s ∈ Icc u v, heightPoint (b a + s • a) s ∈ unitFront ambient :=
    hfrontσ.filter_mono (ae_mono Measure.restrict_le_self)
  have hbounded : ∀ᵐ a ∂normalizedSource μ a₀ τ,
      ‖a‖ ≤ A ∧ ‖normalizedIntercept b a₀ τ a‖ ≤ A := by
    apply Measure.ae_smul_measure
    apply (normalizedSlopeEquiv a₀ τ hτ.ne').measurableEmbedding.ae_map_iff.mpr
    have hμB : ∀ᵐ a ∂μ, a ∈ B :=
      (ae_restrict_mem hB).filter_mono (ae_mono Measure.restrict_le_self)
    filter_upwards [hμB, ae_restrict_mem hD] with a haB haD
    have haunit : ‖a‖ ≤ 1 := (show ‖a‖ < 1 by
      simpa only [Metric.mem_ball, dist_zero_right] using (hBsource haB).1).le
    have ha₀unit : ‖a₀‖ ≤ 1 := (show ‖a₀‖ < 1 by
      simpa only [Metric.mem_ball, dist_zero_right] using (hBsource ha₀B).1).le
    obtain ⟨hslope, hintercept⟩ := actual_source_chart_dist_le_carrier
      selector hmeas hvalid hselector a a₀ haunit ha₀unit R
      (hR _ (hsubset (slopeLine_mem selector hmeas hvalid hselector a₀)))
    have haDist : dist (f a) (indexedCenters (nets j) i) < (L + 2) * dyadicRadius j := by
      exact haD
    have ha₀Dist : dist (indexedCenters (nets j) i) (f a₀) < (L + 2) * dyadicRadius j := by
      simpa only [D, phaseBlock, Set.mem_preimage, Metric.mem_ball, dist_comm] using ha₀D
    have hphase : dist (f a) (f a₀) ≤ 2 * (L + 2) * τ := by
      calc
        dist (f a) (f a₀) ≤ dist (f a) (indexedCenters (nets j) i) +
            dist (indexedCenters (nets j) i) (f a₀) := dist_triangle _ _ _
        _ ≤ (L + 2) * dyadicRadius j + (L + 2) * dyadicRadius j :=
          add_le_add haDist.le ha₀Dist.le
        _ = 2 * (L + 2) * dyadicRadius j := by ring
        _ ≤ 2 * (L + 2) * τ := mul_le_mul_of_nonneg_left hδτ (by positivity)
    have hα : ‖a - a₀‖ ≤ A * τ := by
      calc
        ‖a - a₀‖ ≤ 6 * dist (f a) (f a₀) := hslope
        _ ≤ 6 * (2 * (L + 2) * τ) := mul_le_mul_of_nonneg_left hphase (by norm_num)
        _ = 12 * (L + 2) * τ := by ring
        _ ≤ A * τ := by
          apply mul_le_mul_of_nonneg_right _ hτ.le
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hβ : ‖b a - b a₀‖ ≤ A * τ := by
      calc
        ‖b a - b a₀‖ ≤ (2 + 6 * R) * dist (f a) (f a₀) := hintercept
        _ ≤ (2 + 6 * R) * (2 * (L + 2) * τ) :=
          mul_le_mul_of_nonneg_left hphase (by positivity)
        _ = (4 + 12 * R) * (L + 2) * τ := by ring
        _ ≤ A * τ := by
          apply mul_le_mul_of_nonneg_right _ hτ.le
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    constructor
    · change ‖τ⁻¹ • (a - a₀)‖ ≤ A
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      calc
        τ⁻¹ * ‖a - a₀‖ ≤ τ⁻¹ * (A * τ) :=
          mul_le_mul_of_nonneg_left hα (inv_nonneg.mpr hτ.le)
        _ = A := by field_simp
    · change ‖τ⁻¹ • (b (physicalSlope a₀ τ (normalizedSlope a₀ τ a)) - b a₀)‖ ≤ A
      rw [physicalSlope_normalizedSlope a₀ a τ hτ.ne', norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      calc
        τ⁻¹ * ‖b a - b a₀‖ ≤ τ⁻¹ * (A * τ) :=
          mul_le_mul_of_nonneg_left hβ (inv_nonneg.mpr hτ.le)
        _ = A := by field_simp
  refine ⟨ρ, τ, hτ, a₀, D, Γ, hρ, hρ1, hτ2, hr, hrsmall.trans_le hε₀ε,
    hD, ha₀B, ha₀D, hDpos, hΓshell, hΓdom,
    normalizedSource_isProbability μ hμpos a₀ τ,
    measurable_normalizedIntercept b hb a₀ τ,
    normalizedDirectedGraph_le_product μ Γ hΓdom a₀ τ, ?_, ?_, hbounded,
    normalized_directed_shell_support σ μ B hB b hb J measurableSet_Icc ρ τ hτ Γ hΓshell a₀,
    normalized_source_front_support μ b a₀ τ hτ u v (unitFront ambient) hfrontμ,
    normalized_front_dimH_lt_four ambient a₀ (b a₀) τ hτ.ne' hdim⟩
  · rw [normalizedDirectedGraph_real_mass, Measure.restrict_apply_univ]
    exact hmassSeed
  · apply (normalizedSource_le_real_density μ hμpos hμ a₀ τ hτ).trans
    intro T
    change ENNReal.ofReal (τ ^ 3 / (μ Set.univ).toReal) * volume T ≤ _
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [μ, Measure.restrict_apply_univ] using hcostSeed

end StickyKakeya4.ActualExcessiveLocalGraph
