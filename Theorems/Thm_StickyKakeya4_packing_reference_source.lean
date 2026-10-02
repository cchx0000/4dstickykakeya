import Theorems.Thm_StickyKakeya4_positive_cell_regularization
import Theorems.Thm_StickyKakeya4_packing_reference_nets
import Theorems.Thm_StickyKakeya4_compact_packing_power_piece

open Filter MeasureTheory Set Metric
open scoped ENNReal

namespace StickyKakeya4.PackingReferenceSource

open PositiveCellRegularization

/-- The real dyadic radii corresponding to `dyadicScale`. -/
noncomputable def dyadicRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem dyadicRadius_pos (n : ℕ) : 0 < dyadicRadius n := by
  exact pow_pos (by norm_num) _

theorem ofReal_dyadicRadius (n : ℕ) : ENNReal.ofReal (dyadicRadius n) = dyadicScale n := by
  simp [dyadicRadius, dyadicScale, ENNReal.ofReal_pow, ENNReal.inv_pow]

theorem dyadicScale_le_one (n : ℕ) : dyadicScale n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- A carrier covering bound constructs separated nets and one fixed positive
source restriction. Every remaining net ball has the power lower mass bound
for the actual pushforward; the union of those occupied balls literally
covers the image of the source. No cell-mass hypothesis is assumed.

The centers are supported on the original carrier, and their separation is
preserved after discarding zero-mass balls. The lower bound concerns this
fixed source only, and does not claim persistence under later thinning. -/
theorem exists_dyadic_reference_source
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ Set.univ)
    (f : X → Y) (hf : Measurable f)
    (S : Set Y) (hS : MeasurableSet S) (hsupport : μ (f ⁻¹' S)ᶜ = 0)
    (C : ENNReal) (hC : C ≠ ⊤) (d : ℝ) (hd : 0 ≤ d)
    (κ : ℝ) (hκ : 0 < κ)
    (hcover : ∀ n, coveringNumber S (dyadicRadius n / 4) ≤
      C * (dyadicScale n) ^ (-d)) :
    ∃ c : ENNReal, 0 < c ∧ c ≤ 1 ∧
      ∃ B : Set X, MeasurableSet B ∧ B ⊆ f ⁻¹' S ∧
        μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
        ∃ nets : ℕ → Finset Y, ∀ n,
          (∀ y ∈ nets n, y ∈ S) ∧
          (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
            dyadicRadius n / 2 ≤ dist y z) ∧
          coversAtRadius (f '' B) (dyadicRadius n) (nets n) ∧
          ((nets n).card : ENNReal) ≤ (C + 1) * (dyadicScale n) ^ (-d) ∧
          ∀ y ∈ nets n,
            c * (dyadicScale n) ^ (d + κ) ≤
              (Measure.map f (μ.restrict B)) (Metric.ball y (dyadicRadius n)) := by
  classical
  have hscale0 (n : ℕ) : dyadicScale n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscaleTop (n : ℕ) : dyadicScale n ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hbudgetTop (n : ℕ) : C * (dyadicScale n) ^ (-d) ≠ ⊤ :=
    ENNReal.mul_ne_top hC (ENNReal.rpow_ne_top_of_ne_zero (hscale0 n) (hscaleTop n))
  obtain ⟨original, horiginal⟩ :=
    coveringNumber_bounds_extract_supported_separated_nets S dyadicRadius
      (fun n => C * (dyadicScale n) ^ (-d)) dyadicRadius_pos hbudgetTop hcover
  have hcard (n : ℕ) : ((original n).card : ENNReal) ≤
      (C + 1) * (dyadicScale n) ^ (-d) := by
    have hone : (1 : ENNReal) ≤ (dyadicScale n) ^ (-d) := by
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n)
        (show -d ≤ (0 : ℝ) by linarith)
    calc
      ((original n).card : ENNReal) ≤ C * (dyadicScale n) ^ (-d) + 1 :=
        (horiginal n).2.2.2.le
      _ ≤ C * (dyadicScale n) ^ (-d) + (dyadicScale n) ^ (-d) :=
        add_le_add_right hone _
      _ = (C + 1) * (dyadicScale n) ^ (-d) := by rw [add_mul, one_mul]
  let β : ℕ → Type _ := fun n => {y // y ∈ original n}
  let F : ∀ n, β n → Set X := fun n y => f ⁻¹' Metric.ball y (dyadicRadius n)
  have hF (n : ℕ) (y : β n) : MeasurableSet (F n y) :=
    measurableSet_ball.preimage hf
  have hcardβ (n : ℕ) : (Fintype.card (β n) : ENNReal) ≤
      (C + 1) * (dyadicScale n) ^ (-d) := by
    simpa [β] using hcard n
  obtain ⟨c, hc, hc1, B₀, hB₀, hloss₀, hpos₀, hcells₀⟩ :=
    exists_multiscale_positive_restriction μ hμ β F hF
      (C + 1) (by simpa using hC) d κ hκ hcardβ
  let B₁ : Set X := B₀ ∩ f ⁻¹' S
  have hB₁ : MeasurableSet B₁ := hB₀.inter (hS.preimage hf)
  have hB₁ae : B₁ =ᵐ[μ] B₀ := inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.mpr hsupport)
  obtain ⟨B, hBB₁, hB, hBae₁, hrestrict, hoccupied⟩ :=
    exists_clean_restriction μ B₁ hB₁ (fun p : Sigma β => F p.1 p.2)
      (fun p => hF p.1 p.2)
  have hBae : B =ᵐ[μ] B₀ := hBae₁.trans hB₁ae
  have hrestrict₀ : μ.restrict B = μ.restrict B₀ := Measure.restrict_congr_set hBae
  have hloss : μ Bᶜ < μ Set.univ / 2 := by
    rw [measure_congr hBae.compl]
    exact hloss₀
  have hpos : 0 < μ B := by rwa [measure_congr hBae]
  let nets : ℕ → Finset Y := fun n => (original n).filter fun y =>
    0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n))
  refine ⟨c, hc, hc1, B, hB, fun x hx => (hBB₁ hx).2, hloss, hpos, nets, ?_⟩
  intro n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (horiginal n).1 y (Finset.mem_filter.mp hy).1
  · intro y hy z hz hyz
    exact (horiginal n).2.1 y (Finset.mem_filter.mp hy).1 z
      (Finset.mem_filter.mp hz).1 hyz
  · rintro _ ⟨x, hx, rfl⟩
    have hxS : f x ∈ S := (hBB₁ hx).2
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp ((horiginal n).2.2.1 hxS)
    obtain ⟨hyOriginal, hxy⟩ := Set.mem_iUnion.mp hy
    have hpositive : 0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n)) :=
      hoccupied ⟨n, ⟨y, hyOriginal⟩⟩ ⟨x, hx, hxy⟩
    exact Set.mem_iUnion.mpr ⟨y,
      Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hyOriginal, hpositive⟩, hxy⟩⟩
  · exact (show ((nets n).card : ENNReal) ≤ ((original n).card : ENNReal) by
      exact_mod_cast Finset.card_filter_le (original n) (fun y =>
        0 < (μ.restrict B) (f ⁻¹' Metric.ball y (dyadicRadius n)))).trans
      (hcard n)
  · intro y hy
    obtain ⟨hyOriginal, hypos⟩ := Finset.mem_filter.mp hy
    rw [Measure.map_apply hf measurableSet_ball]
    have hcell := hcells₀ n ⟨y, hyOriginal⟩
    change (μ.restrict B₀) (f ⁻¹' Metric.ball y (dyadicRadius n)) = 0 ∨
      c * (dyadicScale n) ^ (d + κ) ≤
        (μ.restrict B₀) (f ⁻¹' Metric.ball y (dyadicRadius n)) at hcell
    rw [← hrestrict₀] at hcell
    exact hcell.resolve_left hypos.ne'

/-- Uniform unit-interval power covers give the exact dyadic quarter-scale
hypothesis needed by the reference-source construction. The constant absorbs
the harmless factor eight arising from the cover and closure radii. -/
theorem unit_power_cover_implies_dyadic
    {Y : Type*} [PseudoMetricSpace Y] (S : Set Y)
    (C : ENNReal) (hC : C ≠ ⊤) (d : ℝ)
    (hcover : ∀ r : ℝ, 0 < r → r ≤ 1 → coveringNumber S r ≤
      C * (ENNReal.ofReal (r / 2)) ^ (-d)) :
    ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ n,
      coveringNumber S (dyadicRadius n / 4) ≤ D * (dyadicScale n) ^ (-d) := by
  let D := C * (1 / 8 : ENNReal) ^ (-d)
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top hC
    (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  refine ⟨D, hD, ?_⟩
  intro n
  have hrpos := dyadicRadius_pos n
  have hrle : dyadicRadius n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    coveringNumber S (dyadicRadius n / 4) ≤
        C * (ENNReal.ofReal (dyadicRadius n / 4 / 2)) ^ (-d) :=
      hcover _ (by positivity) (by linarith)
    _ = D * (dyadicScale n) ^ (-d) := by
      rw [show dyadicRadius n / 4 / 2 = dyadicRadius n * (1 / 8) by ring,
        ENNReal.ofReal_mul hrpos.le, ofReal_dyadicRadius]
      norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      rw [ENNReal.mul_rpow_of_ne_top
        (show dyadicScale n ≠ ⊤ from ENNReal.pow_ne_top (by norm_num))
        (show (1 / 8 : ENNReal) ≠ ⊤ by norm_num)]
      dsimp [D]
      ac_rfl

/-- Packing dimension at most three produces, for every fixed positive slack,
a positive reference restriction and actual occupied separated dyadic nets.
The exponent `3 + ζ` is a fixed small-power loss, not a literal `o(1)` bound
for one universal source. Compactness and positive mass are inherited from a
constructed power-cover piece of the original carrier. -/
theorem exists_packingDim_le_three_reference_source
    {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Y) (hf : Measurable f)
    (S : Set Y) (hS : IsCompact S)
    (hmass : 0 < (Measure.map f μ) S) (hpacking : packingDim S ≤ 3)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ K : Set Y, K ⊆ S ∧ IsCompact K ∧
      ∃ c D : ENNReal, 0 < c ∧ c ≤ 1 ∧ D ≠ ⊤ ∧
        ∃ B : Set X, MeasurableSet B ∧ B ⊆ f ⁻¹' K ∧ 0 < μ B ∧
          ∃ nets : ℕ → Finset Y, ∀ n,
            (∀ y ∈ nets n, y ∈ K) ∧
            (∀ y ∈ nets n, ∀ z ∈ nets n, y ≠ z →
              dyadicRadius n / 2 ≤ dist y z) ∧
            coversAtRadius (f '' B) (dyadicRadius n) (nets n) ∧
            ((nets n).card : ENNReal) ≤ D * (dyadicScale n) ^ (-(3 + ζ / 2)) ∧
            ∀ y ∈ nets n,
              c * (dyadicScale n) ^ (3 + ζ) ≤
                (Measure.map f (μ.restrict B)) (Metric.ball y (dyadicRadius n)) := by
  have hpacklt : packingDim S < ENNReal.ofReal (3 + ζ / 2) := by
    apply hpacking.trans_lt
    rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨K, hKS, hK, hKmass, d, hd, hdtop, C, hC, hcover⟩ :=
    compact_packingDim_lt_extract_power_piece (Measure.map f μ) S hS hmass hpacklt
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hT : MeasurableSet (f ⁻¹' K) := hKmeas.preimage hf
  have hdReal : d.toReal < 3 + ζ / 2 := by
    have h := (ENNReal.toReal_lt_toReal hdtop ENNReal.ofReal_ne_top).mpr hd
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ 3 + ζ / 2 by linarith)] using h
  obtain ⟨C', hC', hdyadic⟩ := unit_power_cover_implies_dyadic K C hC d.toReal hcover
  let σ : Measure X := μ.restrict (f ⁻¹' K)
  have hσpos : 0 < σ Set.univ := by
    simpa only [σ, Measure.restrict_apply_univ, Measure.map_apply hf hKmeas] using hKmass
  have hσsupport : σ (f ⁻¹' K)ᶜ = 0 := by
    rw [show σ = μ.restrict (f ⁻¹' K) from rfl, Measure.restrict_apply hT.compl]
    simp
  obtain ⟨c, hc, hc1, B, hB, hBK, _hloss, hBpos, nets, hnets⟩ :=
    exists_dyadic_reference_source σ hσpos f hf K hKmeas hσsupport C' hC'
      d.toReal ENNReal.toReal_nonneg (ζ / 2) (by linarith) hdyadic
  have hrestrict : σ.restrict B = μ.restrict B := Measure.restrict_restrict_of_subset hBK
  have hBmass : 0 < μ B := by
    rwa [show σ B = μ B from Measure.restrict_eq_self μ hBK] at hBpos
  refine ⟨K, hKS, hK, c, C' + 1, hc, hc1, by simpa using hC', B, hB, hBK,
    hBmass, nets, ?_⟩
  intro n
  obtain ⟨hsupported, hsep, hnet, hcard, hlower⟩ := hnets n
  refine ⟨hsupported, hsep, hnet, ?_, ?_⟩
  · exact hcard.trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n) (by linarith)))
  · intro y hy
    rw [← hrestrict]
    exact (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_ge (dyadicScale_le_one n)
        (show d.toReal + ζ / 2 ≤ 3 + ζ by linarith))).trans (hlower y hy)

end StickyKakeya4.PackingReferenceSource
