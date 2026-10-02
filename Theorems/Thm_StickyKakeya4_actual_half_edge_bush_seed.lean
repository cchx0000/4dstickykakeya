import Theorems.Thm_StickyKakeya4_actual_excessive_local_graph
import Theorems.Thm_StickyKakeya4_quantitative_bush_cover

/-!
# Actual directed half-edge bush seeds

A strict front dimension deficit supplies the actual probability source and
normalized directed root graph. A finite disjoint family of physical bushes
then captures half of that same ordered graph by restricting sources only.
The target variable, original residual radius, and closest-time window survive.
-/

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

noncomputable section
namespace StickyKakeya4.ActualHalfEdgeBushSeed

open ActualSlopeSource ActualExcessiveLocalGraph ResidualAffineRescaling
open ResidualPhaseLocalization ActualShellGraph

/-- Absorb the fixed bush-cover and half-mass constants into explicit powers. -/
theorem bush_power_bounds
    {eta C r M : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hM : r ^ (2 - eta / 4) ≤ M)
    (hsmallC : C * r ^ (eta / 8) ≤ 1)
    (hsmallTwo : 2 * r ^ (eta / 8) ≤ 1) :
    r ^ (3 - eta / 8) ≤ r * M / C ∧
      C / (r * M) ≤ r ^ (-3 + eta / 8) ∧
      r ^ (2 - eta / 8) ≤ M / 2 := by
  have hMpos : 0 < M := (Real.rpow_pos_of_pos hr _).trans_le hM
  have hproduct : C * r ^ (3 - eta / 8) ≤ r * M := by
    calc
      C * r ^ (3 - eta / 8) =
          (C * r ^ (eta / 8)) * (r * r ^ (2 - eta / 4)) := by
            have hsplit : r ^ (3 - eta / 8) =
                r ^ (eta / 8) * (r * r ^ (2 - eta / 4)) := by
              calc
                r ^ (3 - eta / 8) = r ^ (eta / 8 + (1 + (2 - eta / 4))) := by
                  congr 1
                  ring
                _ = r ^ (eta / 8) * (r * r ^ (2 - eta / 4)) := by
                  rw [Real.rpow_add hr, Real.rpow_add hr, Real.rpow_one]
            rw [hsplit]
            ring
      _ ≤ 1 * (r * r ^ (2 - eta / 4)) :=
        mul_le_mul_of_nonneg_right hsmallC (by positivity)
      _ ≤ r * M := by simpa using mul_le_mul_of_nonneg_left hM hr.le
  refine ⟨(le_div_iff₀ hC).mpr (by simpa [mul_comm] using hproduct), ?_, ?_⟩
  · rw [show (-3 + eta / 8 : ℝ) = -(3 - eta / 8) by ring,
      Real.rpow_neg hr.le, ← one_div]
    apply (div_le_div_iff₀ (mul_pos hr hMpos) (Real.rpow_pos_of_pos hr _)).mpr
    simpa using hproduct
  · apply (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr
    calc
      r ^ (2 - eta / 8) * 2 =
          (2 * r ^ (eta / 8)) * r ^ (2 - eta / 4) := by
            rw [mul_comm _ 2, mul_assoc, ← Real.rpow_add hr]
            rw [show (eta / 8 + (2 - eta / 4) : ℝ) = 2 - eta / 8 by ring]
      _ ≤ 1 * r ^ (2 - eta / 4) :=
        mul_le_mul_of_nonneg_right hsmallTwo (Real.rpow_nonneg hr.le _)
      _ ≤ M := by simpa using hM


/-- From original sticky data and a strict front dimension deficit, construct
arbitrarily fine directed physical root graphs together with a finite source
bush routing. Bushes have radius `2r`; the captured original edges retain
residual error `r` and every old target. Fixed constants are absorbed into the
explicit powers after choosing a finer radius. The same actual affine front
lineage and fixed chart bound are retained throughout. -/
theorem sticky_deficit_exists_half_edge_bush_seed
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
              dimH (frontAffineEquiv4 a₀ (b a₀) τ hτ.ne' '' unitFront ambient) < 4 ∧
              ρ / τ ≤ 1 ∧
              ∃ F : Finset (Set E3),
                (F : Set (Set E3)).PairwiseDisjoint id ∧
                (∀ E ∈ F, MeasurableSet E ∧
                  ENNReal.ofReal ((ρ / τ) * (G Set.univ).toReal / (35 / 2)) ≤ μ E ∧
                  ENNReal.ofReal ((ρ / τ) ^ (3 - η / 8)) ≤ μ E ∧
                  ∃ t ∈ Icc (((k : ℝ) / 8 - 1 / 8) - 2)
                    (((k : ℝ) / 8 + 1 / 4) + 2), ∃ p : E3,
                      E ⊆ physicalAffineBush b' t p (2 * (ρ / τ))) ∧
                (F.card : ℝ) ≤ (35 / 2) / ((ρ / τ) * (G Set.univ).toReal) ∧
                (F.card : ℝ) ≤ (ρ / τ) ^ (-3 + η / 8) ∧
                let U := ⋃ E ∈ F, E
                MeasurableSet U ∧ G (Uᶜ ×ˢ (Set.univ : Set E3)) ≤ G Set.univ / 2 ∧
                let H := G.restrict (U ×ˢ (Set.univ : Set E3))
                H ≤ G ∧ H ≤ (μ.restrict U).prod μ ∧
                G Set.univ / 2 ≤ H Set.univ ∧
                (ρ / τ) ^ (2 - η / 8) ≤ (H Set.univ).toReal ∧
                (∀ᵐ p ∂H, 1 < ‖p.1 - p.2‖ ∧ ‖p.1 - p.2‖ ≤ 2 ∧
                  ‖collisionResidual (p.1 - p.2) (b' p.1 - b' p.2)‖ ≤ ρ / τ ∧
                  collisionTime (p.1 - p.2) (b' p.1 - b' p.2) ∈
                    Icc (((k : ℝ) / 8 - 1 / 8) - 1) (((k : ℝ) / 8 + 1 / 4) + 1)) := by
  classical
  obtain ⟨η, hη, hη2, selector, hmeas, hvalid, hselector, hsubset, k, B,
    hB, hBsource, hBpos, hfinite, A, hA, hseed⟩ :=
    sticky_deficit_exists_excessive_directed_seed ambient hsticky hdim
  refine ⟨η, hη, hη2, selector, hmeas, hvalid, hselector, hsubset, k, B,
    hB, hBsource, hBpos, hfinite, A, hA, ?_⟩
  intro ε hε
  obtain ⟨ε₁, hε₁, hε₁cap, hsmall₁⟩ := LocalSeedAbsorption.exists_rpow_threshold
    (show 0 < η / 8 by positivity) (show (0 : ℝ) ≤ 35 / 2 by norm_num)
    (show (0 : ℝ) < 1 by norm_num) (lt_min hε (by norm_num : (0 : ℝ) < 1))
  obtain ⟨ε₀, hε₀, hε₀cap, hsmall₂⟩ := LocalSeedAbsorption.exists_rpow_threshold
    (show 0 < η / 8 by positivity) (show (0 : ℝ) ≤ 2 by norm_num)
    (show (0 : ℝ) < 1 by norm_num) hε₁
  obtain ⟨ρ, τ, hτ, a₀, D, Γ, hρ, hρ1, hτ2, hr, hrsmall, hD, ha₀B, ha₀D,
    hDpos, hΓshell, hΓdom, hprob, hb', hGdom, hGmass, hdensity, hchart,
    hsupport, hfront, hfrontdim⟩ := hseed ε₀ hε₀
  let σ : Measure E3 := (volume : Measure E3).restrict B
  let b := intercept selector hmeas hvalid hselector
  let μ := normalizedSource (σ.restrict D) a₀ τ
  let G := normalizedDirectedGraph (σ.restrict D) Γ a₀ τ
  let b' := normalizedIntercept b a₀ τ
  let r := ρ / τ
  let u : ℝ := ((k : ℝ) / 8 - 1 / 8) - 1
  let v : ℝ := ((k : ℝ) / 8 + 1 / 4) + 1
  let : IsProbabilityMeasure μ := hprob
  let : IsFiniteMeasure G := isFiniteMeasure_of_le (μ.prod μ) hGdom
  have hr1 : r ≤ 1 := hrsmall.le.trans (hε₀cap.trans (hε₁cap.trans (min_le_right _ _)))
  have hrε : r < ε := hrsmall.trans_le (hε₀cap.trans (hε₁cap.trans (min_le_left _ _)))
  have hMreal : 0 < (G Set.univ).toReal :=
    (Real.rpow_pos_of_pos hr (2 - η / 4)).trans_le hGmass
  have hM : 0 < G Set.univ := (ENNReal.toReal_pos_iff.mp hMreal).1
  have huv : u ≤ v := by dsimp [u, v]; linarith
  have hwindow : 4 * (v - u + 2) = (35 / 2 : ℝ) := by dsimp [u, v]; ring
  have hsupport' : ∀ᵐ p ∂G, ‖p.1 - p.2‖ ≤ 2 ∧
      ‖collisionResidual (p.1 - p.2) (b' p.1 - b' p.2)‖ ≤ r ∧
      collisionTime (p.1 - p.2) (b' p.1 - b' p.2) ∈ Icc u v := by
    filter_upwards [hsupport] with p hp
    exact hp.2
  obtain ⟨F, hFdisjoint, hFpieces, hFcard, hFrem, hFcapture⟩ :=
    exists_quantitative_source_bush_cover μ (by simp) G hGdom hM b' hb'
      u v r huv hr hr1 hsupport'
  rw [hwindow] at hFpieces hFcard
  obtain ⟨hmassPower, hcardPower, hcapturePower⟩ := bush_power_bounds
    (show (0 : ℝ) < 35 / 2 by norm_num) hr hGmass
    (hsmall₁ r hr (hrsmall.le.trans hε₀cap)) (hsmall₂ r hr hrsmall.le)
  let U : Set E3 := ⋃ E ∈ F, E
  have hU : MeasurableSet U :=
    MeasurableSet.biUnion F.countable_toSet (fun E hE => (hFpieces E hE).1)
  let H := G.restrict (U ×ˢ (Set.univ : Set E3))
  have hHmass : G Set.univ / 2 ≤ H Set.univ := by
    simpa only [H, Measure.restrict_apply_univ] using hFcapture
  have hHpower : r ^ (2 - η / 8) ≤ (H Set.univ).toReal := by
    apply hcapturePower.trans
    have hreal := ENNReal.toReal_mono (measure_ne_top H _) hHmass
    simpa using hreal
  refine ⟨ρ, τ, hτ, a₀, D, Γ, hρ, hρ1, hτ2, hr, hrε, hD, ha₀B, ha₀D,
    hDpos, hΓshell, hΓdom, hprob, hb', hGdom, hGmass, hdensity, hchart,
    hsupport, hfront, hfrontdim, hr1, F, hFdisjoint, ?_, hFcard,
    hFcard.trans hcardPower, hU, hFrem, Measure.restrict_le_self,
    original_graph_restrict_source_le μ G hGdom U, hHmass, hHpower,
    hsupport.filter_mono (ae_mono Measure.restrict_le_self)⟩
  intro E hE
  obtain ⟨hEm, hEmass, t, ht, p, hEp⟩ := hFpieces E hE
  refine ⟨hEm, hEmass, (ENNReal.ofReal_le_ofReal hmassPower).trans hEmass,
    t, ?_, p, hEp⟩
  have hu : u - 1 = ((k : ℝ) / 8 - 1 / 8) - 2 := by dsimp [u]; ring
  have hv : v + 1 = ((k : ℝ) / 8 + 1 / 4) + 2 := by dsimp [v]; ring
  simpa only [hu, hv] using ht

end StickyKakeya4.ActualHalfEdgeBushSeed
