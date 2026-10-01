import Theorems.Thm_StickyKakeya4_dimension_witness_extraction
import Theorems.Thm_StickyKakeya4_selector_covering_lower_bound

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace StickyKakeya4

/-- A uniform cubic lower bound for small-scale covering numbers forces upper
Minkowski dimension at least three.  The proof compares an alleged exponent
`d < 3` with the positive power `r^(3-d)` and lets `r` tend to zero. -/
theorem upperMinkowskiDim_ge_three_of_cubic_covering_lower
    {X : Type*} [PseudoMetricSpace X] (s : Set X)
    (M K : ENNReal) (hM0 : M ≠ 0) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hlower : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      M / (K * (ENNReal.ofReal (2 * r)) ^ 3) ≤
        coveringNumber s r) :
    (3 : ENNReal) ≤ upperMinkowskiDim s := by
  by_contra hnot
  have hlt : upperMinkowskiDim s < (3 : ENNReal) := lt_of_not_ge hnot
  obtain ⟨d, hd3, hdtop, C, hCtop, hupper⟩ :=
    upperMinkowskiDim_lt_extract_power_bound s hlt
  have hdreal : d.toReal < 3 := by
    rw [← ENNReal.toReal_ofNat 3]
    exact (ENNReal.toReal_lt_toReal hdtop (by norm_num)).2 hd3
  let q : ℝ := 3 - d.toReal
  have hq : 0 < q := sub_pos.mpr hdreal
  let A : ENNReal := C * K * 8
  have hAtop : A ≠ ⊤ := by
    unfold A
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCtop hKtop) (by norm_num)
  have hofReal :
      Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0)
  have hlimit :
      Tendsto (fun r : ℝ => A * (ENNReal.ofReal r).rpow q)
        (𝓝 0) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hAtop hq).comp hofReal
  have hlimitGT :
      Tendsto (fun r : ℝ => A * (ENNReal.ofReal r).rpow q)
        (𝓝[>] 0) (𝓝 0) :=
    hlimit.mono_left inf_le_left
  have hsmall :
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        A * (ENNReal.ofReal r).rpow q < M :=
    (tendsto_order.1 hlimitGT).2 M (bot_lt_iff_ne_bot.mpr hM0)
  have hrange : Set.Ioc (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨r, hupper_r, hsmall_r, hr, hrhalf⟩ :=
    (hupper.and (hsmall.and hrange)).exists
  have hLower := hlower r hr hrhalf
  have hCompare :
      M / (K * (ENNReal.ofReal (2 * r)) ^ 3) ≤
        C * (ENNReal.ofReal r).rpow (-d.toReal) :=
    hLower.trans hupper_r
  have h2r : 0 < 2 * r := by positivity
  have hB0 : K * (ENNReal.ofReal (2 * r)) ^ 3 ≠ 0 :=
    mul_ne_zero hK0
      (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h2r)))
  have hBtop : K * (ENNReal.ofReal (2 * r)) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top hKtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hone :
      M ≤
        (C * (ENNReal.ofReal r).rpow (-d.toReal)) *
          (K * (ENNReal.ofReal (2 * r)) ^ 3) :=
    (ENNReal.div_le_iff hB0 hBtop).1 hCompare
  let x : ENNReal := ENNReal.ofReal r
  have hx0 : x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hxtop : x ≠ ⊤ := ENNReal.ofReal_ne_top
  have htwo : ENNReal.ofReal (2 * r) = 2 * x := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp [x]
  have halgebra :
      (C * x.rpow (-d.toReal)) *
          (K * (ENNReal.ofReal (2 * r)) ^ 3) =
        A * x.rpow q := by
    rw [htwo]
    calc
      (C * x.rpow (-d.toReal)) * (K * (2 * x) ^ 3) =
          (C * K * 8) * (x.rpow (-d.toReal) * x ^ 3) := by ring
      _ = (C * K * 8) *
          (x.rpow (-d.toReal) * x.rpow (3 : ℝ)) := by
            congr 2
            exact (ENNReal.rpow_natCast x 3).symm
      _ = (C * K * 8) * x.rpow (-d.toReal + 3) := by
            congr 1
            exact (ENNReal.rpow_add (-d.toReal) 3 hx0 hxtop).symm
      _ = A * x.rpow q := by
            rw [show -d.toReal + 3 = 3 - d.toReal by ring]
  have : M ≤ A * x.rpow q := by
    rw [← halgebra]
    simpa [x] using hone
  exact (not_lt_of_ge this) (by simpa [x] using hsmall_r)

/-- The canonical direction probability now supplies the complete packing
dimension lower bound for a measurable full-direction selector carrier. -/
theorem direction_selector_packingDim_lower_internal
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    (3 : ENNReal) ≤ packingDim (lineCarrier selector) := by
  let mu : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  let carrier : Set (E4 × E4) := lineCarrier selector
  have hcarrierMass : mu carrier = 1 := by
    exact selectorCarrierProbability_apply_lineCarrier
      selector hmeasurable hvalid hselector
  have hcarrierNonzero : mu carrier ≠ 0 := by
    rw [hcarrierMass]
    norm_num
  by_contra hnot
  have hlt : packingDim carrier < (3 : ENNReal) := lt_of_not_ge hnot
  obtain ⟨d, hd3, pieces, hcover, hpieces⟩ :=
    packingDim_lt_extract_countable_cover carrier hlt
  obtain ⟨n, hn⟩ :=
    exists_nonzero_measure_piece_of_countable_cover mu hcover hcarrierNonzero
  let piece : Set (E4 × E4) := pieces n
  have hsupport : mu carrierᶜ = 0 := by
    exact selectorCarrierProbability_apply_compl_lineCarrier
      selector hmeasurable hvalid hselector
  have hpieceCarrier : mu (piece ∩ carrier) ≠ 0 := by
    intro hzero
    have hout : mu (piece ∩ carrierᶜ) = 0 :=
      measure_mono_null inter_subset_right hsupport
    have hunion : mu ((piece ∩ carrier) ∪ (piece ∩ carrierᶜ)) = 0 :=
      measure_union_null hzero hout
    rw [Set.inter_union_compl] at hunion
    exact hn hunion
  have hpieceUpper : (3 : ENNReal) ≤ upperMinkowskiDim piece := by
    apply upperMinkowskiDim_ge_three_of_cubic_covering_lower piece
      (mu (piece ∩ carrier)) metricSphereCapConstant hpieceCarrier
      metricSphereCapConstant_ne_zero metricSphereCapConstant_ne_top
    intro r hr hrhalf
    let B : ENNReal :=
      metricSphereCapConstant * (ENNReal.ofReal (2 * r)) ^ 3
    have h2r : 0 < 2 * r := by positivity
    have h2rone : 2 * r ≤ 1 := by linarith
    have hB0 : B ≠ 0 := by
      unfold B
      exact mul_ne_zero metricSphereCapConstant_ne_zero
        (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h2r)))
    have hBtop : B ≠ ⊤ := by
      unfold B
      exact ENNReal.mul_ne_top metricSphereCapConstant_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have hlocal :
        mu (piece ∩ carrier) / B ≤ coveringNumber (piece ∩ carrier) r := by
      apply measure_div_ballBound_le_coveringNumber
        mu (piece ∩ carrier) hr B hB0 hBtop
      intro center hcenter
      exact selectorCarrierProbability_ball_upper_bound
        selector hmeasurable hvalid hselector center hcenter.2 h2r h2rone
    exact hlocal.trans (coveringNumber_mono inter_subset_left r)
  have : (3 : ENNReal) ≤ d := hpieceUpper.trans (hpieces n)
  exact (not_le_of_gt hd3) this

end StickyKakeya4
