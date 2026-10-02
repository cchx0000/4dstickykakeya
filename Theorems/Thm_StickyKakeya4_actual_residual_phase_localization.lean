import Theorems.Thm_StickyKakeya4_actual_reference_vertical_count
import Theorems.Thm_StickyKakeya4_residual_phase_localization
import Theorems.Thm_StickyKakeya4_residual_carrier_proximity
import Theorems.Thm_StickyKakeya4_angular_residual_shell
import Theorems.Thm_StickyKakeya4_actual_shell_graph

open Filter MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.ActualResidualPhaseLocalization

open ActualSlopeSource PositiveCellRegularization PackingReferenceSource
open ResidualPhaseLocalization AngularResidualShell

/-- A reference radius no larger than the angular scale and within a factor
of two of it. This also handles angular scales between one and two. -/
theorem exists_comparable_dyadic_radius (τ : ℝ) (hτ : 0 < τ) (hτ2 : τ ≤ 2) :
    ∃ j : ℕ, dyadicRadius j ≤ τ ∧ τ ≤ 2 * dyadicRadius j := by
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < τ / 2 by positivity) (show τ / 2 ≤ 1 by linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  rw [pow_succ] at hjlo
  exact ⟨j, by dsimp [dyadicRadius]; linarith,
    by dsimp [dyadicRadius]; linarith⟩

/-- Canonical finite indexing of an actually constructed phase net. -/
def indexedCenters (net : Finset (E4 × E4)) : Fin net.card → E4 × E4 :=
  fun i => (net.equivFin.symm i).val

theorem indexedCenters_mem (net : Finset (E4 × E4)) (i : Fin net.card) :
    indexedCenters net i ∈ net := (net.equivFin.symm i).property

theorem indexedCenters_separated (net : Finset (E4 × E4)) (δ : ℝ)
    (hsep : ∀ y ∈ net, ∀ z ∈ net, y ≠ z → δ / 2 ≤ dist y z) :
    ∀ i j, i ≠ j → δ / 2 ≤ dist (indexedCenters net i) (indexedCenters net j) := by
  intro i j hij
  apply hsep _ (indexedCenters_mem net i) _ (indexedCenters_mem net j)
  intro heq
  exact hij (net.equivFin.symm.injective (Subtype.ext heq))

theorem indexedCenters_cover_ae (σ : Measure E3) (f : E3 → E4 × E4)
    (B : Set E3) (hB : ∀ᵐ a ∂σ, a ∈ B)
    (net : Finset (E4 × E4)) (δ : ℝ)
    (hcover : coversAtRadius (f '' B) δ net) :
    ∀ᵐ a ∂σ, ∃ i, dist (f a) (indexedCenters net i) < δ := by
  filter_upwards [hB] with a ha
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hcover (Set.mem_image_of_mem f ha))
  obtain ⟨hynet, hay⟩ := Set.mem_iUnion.mp hy
  refine ⟨net.equivFin ⟨y, hynet⟩, ?_⟩
  simpa only [indexedCenters, Equiv.symm_apply_apply, Metric.mem_ball] using hay

/-- A phase ball is contained in the corresponding original direction ball.
The cubic mass upper bound is derived from ordinary slope-volume domination
and the original north chart, independently of the reference-cell masses. -/
theorem actual_phase_ball_mass_le
    (σ : Measure E3) (hσ : σ ≤ volume) (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (f : E3 → E4 × E4) (_hf : Measurable f)
    (hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4))
    (center : E4 × E4) (r : ℝ) :
    σ (f ⁻¹' Metric.ball center r) ≤
      (ENNReal.ofReal (Real.pi * 4 / 3) * (12 : ENNReal) ^ (3 : ℕ)) *
        (ENNReal.ofReal r) ^ (3 : ℕ) := by
  have hsub : f ⁻¹' Metric.ball center r ⊆
      (fun a : E3 => (northSlopeDirection a : E4)) ⁻¹' Metric.ball center.1 r := by
    intro a ha
    change dist (northSlopeDirection a : E4) center.1 < r
    rw [← hfst a]
    have hdist : dist (f a).1 center.1 ≤ dist (f a) center := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact hdist.trans_lt ha
  calc
    σ (f ⁻¹' Metric.ball center r) ≤
        σ ((fun a : E3 => (northSlopeDirection a : E4)) ⁻¹' Metric.ball center.1 r) :=
      measure_mono hsub
    _ = (σ.map (fun a : E3 => (northSlopeDirection a : E4))) (Metric.ball center.1 r) := by
      have hN : Measurable (fun a : E3 => (northSlopeDirection a : E4)) :=
        measurable_subtype_coe.comp measurable_northSlopeDirection
      exact (Measure.map_apply hN measurableSet_ball).symm
    _ ≤ _ := northSlopeDirection_map_ball_le_cubic σ hσ hunit center.1 r

/-- Uniform real-valued cubic mass bound on every expanded source block. -/
theorem actual_phaseBlock_mass_toReal_le
    (σ : Measure E3) (hσ : σ ≤ volume) (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (f : E3 → E4 × E4) (hf : Measurable f)
    (hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4))
    {n : ℕ} (centers : Fin n → E4 × E4) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (i : Fin n) :
    (σ (phaseBlock f centers L δ i)).toReal ≤
      ((Real.pi * 4 / 3) * 12 ^ (3 : ℕ) * (L + 2) ^ (3 : ℕ)) * δ ^ (3 : ℕ) := by
  have h := actual_phase_ball_mass_le σ hσ hunit f hf hfst (centers i) ((L + 2) * δ)
  have ht : (ENNReal.ofReal (Real.pi * 4 / 3) * (12 : ENNReal) ^ (3 : ℕ)) *
      (ENNReal.ofReal ((L + 2) * δ)) ^ (3 : ℕ) ≠ ⊤ := by finiteness
  have hr : 0 ≤ (L + 2) * δ := mul_nonneg (by linarith) hδ
  have hpi : 0 ≤ Real.pi * 4 / 3 := by positivity
  have hreal := ENNReal.toReal_mono ht h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hpi,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hr] at hreal
  dsimp [phaseBlock]
  calc
    _ ≤ _ := hreal
    _ = _ := by ring

/-- Every original occupied reference ball gives the same lower bound on its
expanded block. No lower bound on a first-hit partition cell is used. -/
theorem reference_lower_mass_le_phaseBlock
    (σ : Measure E3) (f : E3 → E4 × E4) (hf : Measurable f)
    {n : ℕ} (centers : Fin n → E4 × E4) (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (a : ENNReal) (hlower : ∀ i, a ≤ (Measure.map f σ) (Metric.ball (centers i) δ))
    (i : Fin n) : a ≤ σ (phaseBlock f centers L δ i) := by
  apply (hlower i).trans
  rw [Measure.map_apply hf measurableSet_ball]
  apply measure_mono
  exact Set.preimage_mono (Metric.ball_subset_ball (by nlinarith))

/-- The lower original net-ball mass controls the conditional source cost at
any angular scale within a factor two of the reference radius. -/
theorem angular_scale_cubic_normalization_cost
    (c m δ τ ζ : ℝ) (hc : 0 < c) (_hδ : 0 < δ) (hτ : 0 < τ)
    (hτδ : τ ≤ 2 * δ) (hζ : 0 ≤ ζ)
    (hlower : c * δ ^ (3 + ζ) ≤ m) :
    τ ^ (3 : ℕ) / m ≤ (2 ^ (3 + ζ) / c) * τ ^ (-ζ) := by
  have hq : 0 < 3 + ζ := by linarith
  have hsmall : (τ / 2) ^ (3 + ζ) ≤ δ ^ (3 + ζ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hq.le
  have hlower' : c * (τ / 2) ^ (3 + ζ) ≤ m :=
    (mul_le_mul_of_nonneg_left hsmall hc.le).trans hlower
  have hsmallpos : 0 < c * (τ / 2) ^ (3 + ζ) :=
    mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hτq : τ ^ (3 + ζ) ≠ 0 := (Real.rpow_pos_of_pos hτ _).ne'
  have htwoq : (2 : ℝ) ^ (3 + ζ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hpow : τ ^ (-ζ) = τ ^ (3 : ℕ) / τ ^ (3 + ζ) := by
    rw [show -ζ = (3 : ℝ) - (3 + ζ) by ring, Real.rpow_sub hτ,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  calc
    τ ^ (3 : ℕ) / m ≤ τ ^ (3 : ℕ) / (c * (τ / 2) ^ (3 + ζ)) :=
      div_le_div_of_nonneg_left (by positivity) hsmallpos hlower'
    _ = (2 ^ (3 + ζ) / c) * τ ^ (-ζ) := by
      rw [Real.div_rpow hτ.le (by norm_num), hpow]
      field_simp [hc.ne', hτq, htwoq]

/-- Replacing the comparable reference radius by the original angular scale
costs no number-of-cells factor in the localized graph density. -/
theorem angular_scale_localized_density
    (Z C K m δ τ density : ℝ)
    (hZ : 0 ≤ Z) (hδ : 0 < δ) (hτ : 0 < τ) (hδτ : δ ≤ τ)
    (hden : 0 < C * δ ^ (3 : ℕ) * K * m)
    (hselected : (τ * Z) / (C * δ ^ (3 : ℕ) * K * m) ≤ density) :
    Z / (C * K * m * τ ^ (2 : ℕ)) ≤ density := by
  let D : ℝ := C * K * m
  have hD : 0 < D := by
    have hprod : 0 < D * δ ^ (3 : ℕ) := by
      convert hden using 1
      dsimp [D]
      ring
    exact (mul_pos_iff_of_pos_right (by positivity : 0 < δ ^ (3 : ℕ))).mp hprod
  have hdenle : D * δ ^ (3 : ℕ) ≤ D * τ ^ (3 : ℕ) := by
    gcongr
  have hdiv : (τ * Z) / (D * τ ^ (3 : ℕ)) ≤
      (τ * Z) / (D * δ ^ (3 : ℕ)) :=
    div_le_div_of_nonneg_left (mul_nonneg hτ.le hZ) (by positivity) hdenle
  have heq : Z / (C * K * m * τ ^ (2 : ℕ)) = (τ * Z) / (D * τ ^ (3 : ℕ)) := by
    change Z / (D * τ ^ (2 : ℕ)) = (τ * Z) / (D * τ ^ (3 : ℕ))
    field_simp [hD.ne', hτ.ne']
  rw [heq]
  exact hdiv.trans (by simpa only [D, mul_assoc, mul_left_comm, mul_comm] using hselected)


/-- A normalized restriction of the actual slope-volume source has the
expected cubic density after scaling its slope balls by `τ`. This form does
not move the physical front or replace the inherited collision variables. -/
theorem normalized_restriction_scaled_ball_bound
    (σ : Measure E3) (hσ : σ ≤ volume) (D : Set E3)
    (hm : 0 < (σ D).toReal) (τ : ℝ) (hτ : 0 ≤ τ)
    (x : E3) (r : ℝ) (hr : 0 ≤ r) :
    ((σ.restrict D) (Metric.ball x (τ * r))).toReal / (σ D).toReal ≤
      (Real.pi * 4 / 3) * (τ ^ (3 : ℕ) / (σ D).toReal) * r ^ (3 : ℕ) := by
  have hbound : (σ.restrict D) (Metric.ball x (τ * r)) ≤
      volume (Metric.ball x (τ * r)) :=
    (Measure.restrict_le_self.trans hσ) _
  have hfinite : (volume : Measure E3) (Metric.ball x (τ * r)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hreal := ENNReal.toReal_mono hfinite hbound
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg hτ hr),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)] at hreal
  calc
    _ ≤ ((τ * r) ^ (3 : ℕ) * (Real.pi * 4 / 3)) / (σ D).toReal :=
      div_le_div_of_nonneg_right hreal hm.le
    _ = _ := by ring

/-- Composition for the actual fixed reference source. The finite reference
families are inputs to this intermediate lemma; the original-data theorem
below constructs them before applying it. The returned first-hit assignment,
block containment, mass split, density gain, and normalization cost are all
proved for the literal angular residual graph. -/
theorem localize_actual_shell_in_reference_nets
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (hsubset : selector ⊆ ambient)
    (k : ℤ) (B : Set E3) (hB : MeasurableSet B)
    (hBsource : B ⊆ sourceSet selector hmeas hvalid hselector k)
    (hfinite : IsFiniteMeasure ((volume : Measure E3).restrict B))
    (ζ : ℝ) (hζ : 0 < ζ) (c : ENNReal) (hc : 0 < c) (hc1 : c ≤ 1)
    (nets : ℕ → Finset (E4 × E4))
    (hsep : ∀ j, ∀ y ∈ nets j, ∀ z ∈ nets j, y ≠ z → dyadicRadius j / 2 ≤ dist y z)
    (hcover : ∀ j, coversAtRadius
      ((slopeCarrierMap selector hmeas hvalid hselector) '' B) (dyadicRadius j) (nets j))
    (hlower : ∀ j, ∀ y ∈ nets j, c * (dyadicScale j) ^ (3 + ζ) ≤
      (Measure.map (slopeCarrierMap selector hmeas hvalid hselector)
        ((volume : Measure E3).restrict B)) (Metric.ball y (dyadicRadius j)))
    (S : ℝ) (hS : 0 ≤ S) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 < C ∧ ∃ K : ℕ,
      ∀ (J : Set ℝ), MeasurableSet J → (∀ t ∈ J, |t| ≤ S) →
      ∀ (ρ τ : ℝ), 0 < τ → τ ≤ 2 → ρ ≤ τ →
      let σ := (volume : Measure E3).restrict B
      let b := intercept selector hmeas hvalid hselector
      let f := slopeCarrierMap selector hmeas hvalid hselector
      let w := ActualShellGraph.shellGraphWeight B b J ρ τ
      let Z := angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ τ (2 * τ)
      0 < Z → ∃ j : ℕ, dyadicRadius j ≤ τ ∧ τ ≤ 2 * dyadicRadius j ∧
        LocalizationConclusion σ (graphMeasure σ w)
          (phaseCover f (indexedCenters (nets j)) (dyadicRadius j))
          (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j)) K
          (C * dyadicRadius j ^ (3 : ℕ)) ∧
        graphMeasure σ w Set.univ = ENNReal.ofReal τ * Z ∧
        (∀ i, (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
          C * dyadicRadius j ^ (3 : ℕ)) ∧
        (∀ i, c * (dyadicScale j) ^ (3 + ζ) ≤
          σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)) ∧
        ∃ i, 0 < (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ∧
          Z.toReal / (C * (K : ℝ) * (σ Set.univ).toReal * τ ^ (2 : ℕ)) ≤
            (assignedGraph (graphMeasure σ w)
              (phaseCover f (indexedCenters (nets j)) (dyadicRadius j)) i Set.univ).toReal /
              (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ^ 2 ∧
          τ ^ (3 : ℕ) /
              (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
            (2 ^ (3 + ζ) / c.toReal) * τ ^ (-ζ) ∧
          ∀ (x : E3) (r : ℝ), 0 ≤ r →
            ((σ.restrict (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i))
              (Metric.ball x (τ * r))).toReal /
                (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
              (Real.pi * 4 / 3) * ((2 ^ (3 + ζ) / c.toReal) * τ ^ (-ζ)) * r ^ (3 : ℕ) := by
  let σ : Measure E3 := (volume : Measure E3).restrict B
  let : IsFiniteMeasure σ := hfinite
  let b := intercept selector hmeas hvalid hselector
  let f := slopeCarrierMap selector hmeas hvalid hselector
  have hb : Measurable b := measurable_intercept selector hmeas hvalid hselector
  have hf : Measurable f := measurable_slopeCarrierMap selector hmeas hvalid hselector
  have hfst : ∀ a, (f a).1 = (northSlopeDirection a : E4) :=
    direction_slopeLine selector hmeas hvalid hselector
  have hσ : σ ≤ volume := Measure.restrict_le_self
  have hσB : ∀ᵐ a ∂σ, a ∈ B := ae_restrict_mem hB
  have hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1 := by
    filter_upwards [hσB] with a ha
    exact (show ‖a‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right]
      using (hBsource ha).1).le
  obtain ⟨R, hR0, hR⟩ := compact_offset_bound ambient hcompact
  let L₀ : ℝ := 6 + 24 * R + 16 * S
  let L : ℝ := 2 * L₀
  have hL₀ : 0 ≤ L₀ := by dsimp [L₀]; positivity
  have hL : 0 ≤ L := mul_nonneg (by norm_num) hL₀
  let C₀ : ℝ := (Real.pi * 4 / 3) * 12 ^ (3 : ℕ) * (L + 2) ^ (3 : ℕ)
  let C : ℝ := C₀ + 1
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  obtain ⟨K, hlocalize⟩ := exists_uniform_near_phase_graph_localization
    (X := E3) (E4 × E4) L hL
  refine ⟨L, C, hL, hC, K, ?_⟩
  intro J hJ hJS ρ τ hτ hτ2 hρτ
  dsimp only
  intro hZ
  obtain ⟨j, hδτ, hτδ⟩ := exists_comparable_dyadic_radius τ hτ hτ2
  let δ := dyadicRadius j
  let centers := indexedCenters (nets j)
  let w := ActualShellGraph.shellGraphWeight B b J ρ τ
  have hδ : 0 < δ := dyadicRadius_pos j
  have hw : Measurable w := ActualShellGraph.measurable_shellGraphWeight B hB b hb J hJ ρ τ
  have hw1 : ∀ p, w p ≤ 1 := ActualShellGraph.shellGraphWeight_le_one B b J ρ τ hτ
  have hnear : ∀ p, w p ≠ 0 → dist (f p.1) (f p.2) ≤ L * δ := by
    intro p hp
    have h := ActualShellGraph.actual_shellGraphWeight_carrier_dist_le
      selector hmeas hvalid hselector k B hBsource ambient hsubset R hR J S hJS
      ρ τ hρτ hτ p hp
    calc
      dist (f p.1) (f p.2) ≤ L₀ * τ := h
      _ ≤ L₀ * (2 * δ) := mul_le_mul_of_nonneg_left hτδ hL₀
      _ = L * δ := by dsimp [L]; ring
  have hcoverAE : ∀ᵐ a ∂σ, ∃ i, dist (f a) (centers i) < δ :=
    indexedCenters_cover_ae σ f B hσB (nets j) δ (hcover j)
  have hsep' : ∀ i i', i ≠ i' → δ / 2 ≤ dist (centers i) (centers i') :=
    indexedCenters_separated (nets j) δ (hsep j)
  have hupper : ∀ i, (σ (phaseBlock f centers L δ i)).toReal ≤ C * δ ^ (3 : ℕ) := by
    intro i
    exact (actual_phaseBlock_mass_toReal_le σ hσ hunit f hf hfst centers L δ hL hδ.le i).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C, C₀]; linarith) (by positivity))
  have hblockLower : ∀ i, c * (dyadicScale j) ^ (3 + ζ) ≤
      σ (phaseBlock f centers L δ i) :=
    reference_lower_mass_le_phaseBlock σ f hf centers L δ hL hδ.le _
      (fun i => hlower j _ (indexedCenters_mem (nets j) i))
  have hmass : graphMeasure σ w Set.univ = ENNReal.ofReal τ *
      angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ τ (2 * τ) :=
    ActualShellGraph.graphMeasure_mass_eq_angularShellContent B hB b J ρ τ
  have hdom : graphMeasure σ w ≤ σ.prod σ := graphMeasure_le_product σ w hw1
  let : IsFiniteMeasure (graphMeasure σ w) := isFiniteMeasure_of_le (σ.prod σ) hdom
  have hmasspos : 0 < (graphMeasure σ w Set.univ).toReal := by
    apply ENNReal.toReal_pos
    · rw [hmass]
      exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hτ).ne' hZ.ne').ne'
    · exact measure_ne_top _ _
  have hloc := hlocalize σ f hf (nets j).card centers δ hδ hsep' hcoverAE w hw hw1 hnear
    C hC.le hupper hmasspos
  obtain ⟨i, himass, _havg, hdensity⟩ := hloc.selected_block
  have hden : 0 < C * δ ^ (3 : ℕ) * (K : ℝ) * (σ Set.univ).toReal :=
    hloc.positive_square_mass.trans_le hloc.square_mass_budget
  have hdensity' : ENNReal.toReal
      (angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
        (fun p => b p.1 - b p.2) J ρ τ (2 * τ)) /
      (C * (K : ℝ) * (σ Set.univ).toReal * τ ^ (2 : ℕ)) ≤
      (assignedGraph (graphMeasure σ w) (phaseCover f centers δ) i Set.univ).toReal /
        (σ (phaseBlock f centers L δ i)).toReal ^ 2 := by
    apply angular_scale_localized_density _ C (K : ℝ) (σ Set.univ).toReal δ τ _
      ENNReal.toReal_nonneg hδ hτ hδτ hden
    simpa only [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ.le] using hdensity
  have hcReal : 0 < c.toReal :=
    ENNReal.toReal_pos hc.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
  have hlowerReal : c.toReal * δ ^ (3 + ζ) ≤ (σ (phaseBlock f centers L δ i)).toReal := by
    have h := ENNReal.toReal_mono (measure_ne_top σ _) (hblockLower i)
    rw [ENNReal.toReal_mul, ← ofReal_dyadicRadius j, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hδ.le] at h
    exact h
  have hcost := angular_scale_cubic_normalization_cost c.toReal _ δ τ ζ
    hcReal hδ hτ hτδ hζ.le hlowerReal
  refine ⟨j, hδτ, hτδ, hloc, hmass, hupper, hblockLower, i, himass, hdensity', hcost, ?_⟩
  intro x r hr
  apply (normalized_restriction_scaled_ball_bound σ hσ (phaseBlock f centers L δ i)
    himass τ hτ.le x r hr).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcost (by positivity)) (by positivity)

/-- Original-data localization with the source chosen once, before every later
shell graph. Compactness, packing, the occupied nets, cubic block bounds,
physical carrier proximity, and the normalization cost are all discharged
from the sticky datum. The old-time window may be chosen afterward, provided
it has the stated absolute bound. No fine-graph mass denominator is used. -/
theorem sticky_datum_exists_uniform_actual_shell_localization
    (ambient : Set MarkedLine) (hsticky : IsStickyDatum ambient)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (selector : Set MarkedLine) (hmeas : MeasurableSet selector)
      (hvalid : ∀ line ∈ selector, IsValidLine line)
      (hselector : IsDirectionSelector selector), selector ⊆ ambient ∧
      ∃ (k : ℤ) (B : Set E3) (carrier : Set (E4 × E4)) (c : ENNReal)
        (nets : ℕ → Finset (E4 × E4)),
        MeasurableSet B ∧ B ⊆ sourceSet selector hmeas hvalid hselector k ∧
        0 < (volume : Measure E3) B ∧ IsFiniteMeasure ((volume : Measure E3).restrict B) ∧
        carrier ⊆ lineCarrier ambient ∧ IsCompact carrier ∧
        B ⊆ (slopeCarrierMap selector hmeas hvalid hselector) ⁻¹' carrier ∧
        0 < c ∧ c ≤ 1 ∧
        (∀ j, ∀ y ∈ nets j, y ∈ carrier) ∧
        (∀ j, ∀ y ∈ nets j, ∀ z ∈ nets j, y ≠ z → dyadicRadius j / 2 ≤ dist y z) ∧
        (∀ j, coversAtRadius ((slopeCarrierMap selector hmeas hvalid hselector) '' B)
          (dyadicRadius j) (nets j)) ∧
        (∀ a ∈ B, ∀ s ∈ Icc ((k : ℝ) / 8 - 1 / 8) ((k : ℝ) / 8 + 1 / 4),
          heightPoint (intercept selector hmeas hvalid hselector a + s • a) s ∈
            unitFront ambient) ∧
        ∀ (S : ℝ), 0 ≤ S →
          ∃ L C : ℝ, 0 ≤ L ∧ 0 < C ∧ ∃ K : ℕ,
            ∀ (J : Set ℝ), MeasurableSet J → (∀ t ∈ J, |t| ≤ S) →
            ∀ (ρ τ : ℝ), 0 < τ → τ ≤ 2 → ρ ≤ τ →
            let σ := (volume : Measure E3).restrict B
            let b := intercept selector hmeas hvalid hselector
            let f := slopeCarrierMap selector hmeas hvalid hselector
            let w := ActualShellGraph.shellGraphWeight B b J ρ τ
            let Z := angularShellContent (σ.prod σ) (fun p => p.1 - p.2)
              (fun p => b p.1 - b p.2) J ρ τ (2 * τ)
            0 < Z → ∃ j : ℕ, dyadicRadius j ≤ τ ∧ τ ≤ 2 * dyadicRadius j ∧
              LocalizationConclusion σ (graphMeasure σ w)
                (phaseCover f (indexedCenters (nets j)) (dyadicRadius j))
                (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j)) K
                (C * dyadicRadius j ^ (3 : ℕ)) ∧
              graphMeasure σ w Set.univ = ENNReal.ofReal τ * Z ∧
              (∀ i, (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
                C * dyadicRadius j ^ (3 : ℕ)) ∧
              (∀ i, c * (dyadicScale j) ^ (3 + ζ) ≤
                σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)) ∧
              ∃ i, 0 < (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ∧
                Z.toReal / (C * (K : ℝ) * (σ Set.univ).toReal * τ ^ (2 : ℕ)) ≤
                  (assignedGraph (graphMeasure σ w)
                    (phaseCover f (indexedCenters (nets j)) (dyadicRadius j)) i Set.univ).toReal /
                    (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ^ 2 ∧
                τ ^ (3 : ℕ) /
                    (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
                  (2 ^ (3 + ζ) / c.toReal) * τ ^ (-ζ) ∧
                ∀ (x : E3) (r : ℝ), 0 ≤ r →
                  ((σ.restrict (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i))
                    (Metric.ball x (τ * r))).toReal /
                      (σ (phaseBlock f (indexedCenters (nets j)) L (dyadicRadius j) i)).toReal ≤
                    (Real.pi * 4 / 3) * ((2 ^ (3 + ζ) / c.toReal) * τ ^ (-ζ)) * r ^ (3 : ℕ) := by
  obtain ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, carrier, c, D,
      hB, hBsource, hBpos, hfinite, hcarrier, hcompact, hBsupport, hc, hc1, _hD,
      _hunit, hfront, nets, hnets⟩ :=
    sticky_datum_exists_actual_reference_restriction ambient hsticky ζ hζ
  refine ⟨selector, hmeas, hvalid, hselector, hsubset, k, B, carrier, c, nets,
    hB, hBsource, hBpos, hfinite, hcarrier, hcompact, hBsupport, hc, hc1,
    fun j => (hnets j).1, fun j => (hnets j).2.1, fun j => (hnets j).2.2.1,
    hfront, ?_⟩
  intro S hS
  exact localize_actual_shell_in_reference_nets ambient hsticky.1 selector hmeas hvalid
    hselector hsubset k B hB hBsource hfinite ζ hζ c hc hc1 nets
    (fun j => (hnets j).2.1) (fun j => (hnets j).2.2.1)
    (fun j => (hnets j).2.2.2.2) S hS

end StickyKakeya4.ActualResidualPhaseLocalization
