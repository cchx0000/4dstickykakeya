import Theorems.Thm_StickyKakeya4_positive_carrier_piece
import Theorems.Thm_StickyKakeya4_marked_carrier_inverse
import Theorems.Thm_StickyKakeya4_wz_common_slab

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace StickyKakeya4

/-!
Positive-mass localization of the selector carrier to the fixed north-pole
graph chart and one marked-centre height bin.  The bin is chosen before every
fine WZ scale, so its mass and all chart constants are fixed losses.
-/

def wzNorthPole : E4 := EuclideanSpace.single (3 : Fin 4) 1

theorem norm_wzNorthPole : ‖wzNorthPole‖ = 1 := by
  simp [wzNorthPole]

def wzNorthDirection : {theta : E4 // ‖theta‖ = 1} :=
  ⟨wzNorthPole, norm_wzNorthPole⟩

def carrierMarkedCenterHeight
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (q : E4 × E4) : ℝ :=
  wzMarkedCenterHeight
    (selectorLineFromCarrier selector hmeasurable hvalid hselector q)

theorem measurable_carrierMarkedCenterHeight
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    Measurable
      (carrierMarkedCenterHeight selector hmeasurable hvalid hselector) := by
  exact measurable_wzMarkedCenterHeight.comp
    (measurable_subtype_coe.comp
      (measurable_selectorLineFromCarrier selector hmeasurable hvalid hselector))

/-- Half-open marked-centre bins of fixed width `1/8`. -/
def carrierMarkedCenterBin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (k : ℤ) : Set (E4 × E4) :=
  carrierMarkedCenterHeight selector hmeasurable hvalid hselector ⁻¹'
    Set.Ico ((k : ℝ) / 8) (((k : ℝ) + 1) / 8)

theorem measurableSet_carrierMarkedCenterBin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (k : ℤ) :
    MeasurableSet
      (carrierMarkedCenterBin selector hmeasurable hvalid hselector k) :=
  measurableSet_Ico.preimage
    (measurable_carrierMarkedCenterHeight selector hmeasurable hvalid hselector)

theorem carrier_mem_floor_center_bin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) (q : E4 × E4) :
    q ∈ carrierMarkedCenterBin selector hmeasurable hvalid hselector
      ⌊8 * carrierMarkedCenterHeight selector hmeasurable hvalid hselector q⌋ := by
  let z := carrierMarkedCenterHeight selector hmeasurable hvalid hselector q
  have hlo := Int.floor_le (8 * z)
  have hhi := Int.lt_floor_add_one (8 * z)
  change ((⌊8 * z⌋ : ℤ) : ℝ) / 8 ≤ z ∧
    z < (((⌊8 * z⌋ : ℤ) : ℝ) + 1) / 8
  constructor <;> linarith

/-- The part of the genuine selector carrier lying in a fixed positive north
cap. -/
def northCarrierRegion
    (selector : Set MarkedLine) : Set (E4 × E4) :=
  lineCarrier selector ∩ carrierDirectionBall wzNorthPole (1 / 4)

theorem measurableSet_northCarrierRegion
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    MeasurableSet (northCarrierRegion selector) :=
  (measurableSet_lineCarrier_of_selector selector hmeasurable hvalid hselector).inter
    (measurableSet_carrierDirectionBall wzNorthPole (1 / 4))

theorem selectorCarrierProbability_northCarrierRegion_ne_zero
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    (selectorCarrierProbability selector hmeasurable hvalid hselector :
      Measure (E4 × E4)) (northCarrierRegion selector) ≠ 0 := by
  let mu : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  have hae : ∀ᵐ q ∂mu, q ∈ lineCarrier selector := by
    rw [ae_iff]
    exact selectorCarrierProbability_apply_compl_lineCarrier
      selector hmeasurable hvalid hselector
  change mu (lineCarrier selector ∩
    carrierDirectionBall wzNorthPole (1 / 4)) ≠ 0
  rw [Measure.measure_inter_eq_of_ae hae]
  exact selectorCarrierProbability_carrierDirectionBall_ne_zero
    selector hmeasurable hvalid hselector wzNorthDirection (by norm_num)

/-- Some fixed centre-height bin has positive selector-carrier mass inside
the north graph chart. -/
theorem exists_positive_north_center_bin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    ∃ k : ℤ,
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4))
        (northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector k) ≠ 0 := by
  let mu : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  let bins : ℕ → Set (E4 × E4) := fun n =>
    northCarrierRegion selector ∩
      carrierMarkedCenterBin selector hmeasurable hvalid hselector
        (Equiv.intEquivNat.symm n)
  have hcover : northCarrierRegion selector ⊆ ⋃ n, bins n := by
    intro q hq
    let k : ℤ :=
      ⌊8 * carrierMarkedCenterHeight selector hmeasurable hvalid hselector q⌋
    let n : ℕ := Equiv.intEquivNat k
    apply Set.mem_iUnion.2
    refine ⟨n, hq, ?_⟩
    simpa [bins, n, k] using
      carrier_mem_floor_center_bin selector hmeasurable hvalid hselector q
  obtain ⟨n, hn⟩ := exists_nonzero_measure_piece_of_countable_cover
    mu hcover
    (selectorCarrierProbability_northCarrierRegion_ne_zero
      selector hmeasurable hvalid hselector)
  exact ⟨Equiv.intEquivNat.symm n, by simpa [mu, bins] using hn⟩

/-- On the genuine selector carrier, inversion recovers the original marked
line, not merely its unmarked direction--offset pair. -/
theorem selectorLineFromCarrier_carrier_eq_line
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (line : MarkedLine) (hline : line ∈ selector) :
    (selectorLineFromCarrier selector hmeasurable hvalid hselector
        (direction line, offset line) : MarkedLine) = line := by
  let recovered := selectorLineFromCarrier selector hmeasurable hvalid hselector
    (direction line, offset line)
  have hcarrier : (direction line, offset line) ∈ lineCarrier selector :=
    ⟨line, hline, rfl⟩
  have hpair := carrier_selectorLineFromCarrier selector hmeasurable hvalid
    hselector (direction line, offset line) hcarrier
  obtain ⟨chosen, _hchosen, hunique⟩ :=
    hselector (direction line) (hvalid line hline).1
  have hrecoveredDirection : direction (recovered : MarkedLine) = direction line :=
    congrArg Prod.fst hpair
  exact
    (hunique recovered ⟨recovered.property, hrecoveredDirection⟩).trans
      (hunique line ⟨hline, rfl⟩).symm

/-- The fixed north cap stays uniformly inside the graph chart. -/
theorem northCarrierRegion_direction_ge_half
    (selector : Set MarkedLine) (q : E4 × E4)
    (hq : q ∈ northCarrierRegion selector) :
    (1 / 2 : ℝ) ≤ q.1 (3 : Fin 4) := by
  have hball : dist q.1 wzNorthPole < (1 / 4 : ℝ) := hq.2
  have hnorm : ‖q.1 - wzNorthPole‖ < (1 / 4 : ℝ) := by
    simpa [dist_eq_norm] using hball
  have hinner := abs_real_inner_le_norm wzNorthPole (q.1 - wzNorthPole)
  rw [norm_wzNorthPole, one_mul] at hinner
  have hcoordinate :
      |q.1 (3 : Fin 4) - 1| ≤ ‖q.1 - wzNorthPole‖ := by
    simpa [wzNorthPole, EuclideanSpace.inner_single_left] using hinner
  have habs : |q.1 (3 : Fin 4) - 1| < (1 / 4 : ℝ) :=
    hcoordinate.trans_lt hnorm
  have hlower := (abs_lt.mp habs).1
  linarith

/-- Carrier height agrees with the height of the actual selected marked line.
This is where the affine mark is retained through carrier localization. -/
theorem carrierMarkedCenterHeight_carrier_eq
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (line : MarkedLine) (hline : line ∈ selector) :
    carrierMarkedCenterHeight selector hmeasurable hvalid hselector
        (direction line, offset line) =
      wzMarkedCenterHeight line := by
  unfold carrierMarkedCenterHeight
  rw [selectorLineFromCarrier_carrier_eq_line selector hmeasurable hvalid
    hselector line hline]

/-- Every finite source drawn from one localized north-chart centre bin has
one common nonempty absolute-height slab contained in all of its marked unit
segments.  The slab width and graph denominator are fixed before the fine
scale and therefore introduce no scale-dependent loss. -/
theorem finiteSource_hasCommonWZHeightSlab_of_north_center_bin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {n : ℕ} (D : FiniteScaleSource n) (hcomes : ComesFromSelector D selector)
    (k : ℤ)
    (hlocalized : ∀ i,
      (direction (D.line i), offset (D.line i)) ∈
        northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector k) :
    HasCommonWZHeightSlab D
      (Set.Icc
        ((k : ℝ) / 8 + (1 / 8 : ℝ) - (1 / 2 : ℝ) / 2)
        ((k : ℝ) / 8 + (1 / 2 : ℝ) / 2)) := by
  apply hasCommonWZHeightSlab_of_center_bin D
      (c := (1 / 2 : ℝ)) (u := (k : ℝ) / 8) (h := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  · intro i
    exact northCarrierRegion_direction_ge_half selector
      (direction (D.line i), offset (D.line i)) (hlocalized i).1
  · intro i
    have hbin := (hlocalized i).2
    simp only [carrierMarkedCenterBin, Set.mem_preimage, Set.mem_Ico] at hbin
    rw [carrierMarkedCenterHeight_carrier_eq selector hmeasurable hvalid
      hselector (D.line i) (hcomes i)] at hbin
    exact hbin.1
  · intro i
    have hbin := (hlocalized i).2
    simp only [carrierMarkedCenterBin, Set.mem_preimage, Set.mem_Ico] at hbin
    have hupper :
        wzMarkedCenterHeight (D.line i) ≤ ((k : ℝ) + 1) / 8 := by
      rw [carrierMarkedCenterHeight_carrier_eq selector hmeasurable hvalid
        hselector (D.line i) (hcomes i)] at hbin
      exact le_of_lt hbin.2
    convert hupper using 1 <;> ring

/-- The localized source satisfies the complete fixed-constant native graph
certificate, including both the denominator bound and a slab of length
`3/8`. -/
theorem finiteSource_hasNormalizedWZGraphSlab_of_north_center_bin
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    {n : ℕ} (D : FiniteScaleSource n) (hcomes : ComesFromSelector D selector)
    (k : ℤ)
    (hlocalized : ∀ i,
      (direction (D.line i), offset (D.line i)) ∈
        northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector k) :
    HasNormalizedWZGraphSlab D := by
  let a : ℝ := (k : ℝ) / 8 + (1 / 8 : ℝ) - (1 / 2 : ℝ) / 2
  let b : ℝ := (k : ℝ) / 8 + (1 / 2 : ℝ) / 2
  refine ⟨?_, a, b, ?_, ?_⟩
  · intro i
    exact northCarrierRegion_direction_ge_half selector
      (direction (D.line i), offset (D.line i)) (hlocalized i).1
  · dsimp [a, b]
    ring_nf
    norm_num
  · exact finiteSource_hasCommonWZHeightSlab_of_north_center_bin
      selector hmeasurable hvalid hselector D hcomes k hlocalized

/-- The packing-dimension witness may be chosen inside one fixed north-chart
centre-height bin.  The bin is selected before the small WZ scale; hence its
positive mass and the chart constants are fixed losses, not scale-dependent
normalizations. -/
theorem packing_selector_extract_positive_measurable_north_center_piece
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3)
    {slack : ENNReal} (hslack : 0 < slack) :
    ∃ (k : ℤ) (piece : Set (E4 × E4)),
      MeasurableSet piece ∧
      piece ⊆ lineCarrier selector ∧
      piece ⊆
        northCarrierRegion selector ∩
          carrierMarkedCenterBin selector hmeasurable hvalid hselector k ∧
      (selectorCarrierProbability selector hmeasurable hvalid hselector :
        Measure (E4 × E4)) piece ≠ 0 ∧
      ∃ d : ENNReal, d < 3 + slack ∧ d ≠ ⊤ ∧
        ∃ C : ENNReal, C ≠ ⊤ ∧
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            coveringNumber piece r ≤
              C * (ENNReal.ofReal (r / 2)).rpow (-d.toReal) := by
  obtain ⟨k, hk⟩ :=
    exists_positive_north_center_bin selector hmeasurable hvalid hselector
  let mu : Measure (E4 × E4) :=
    selectorCarrierProbability selector hmeasurable hvalid hselector
  let domain : Set (E4 × E4) :=
    northCarrierRegion selector ∩
      carrierMarkedCenterBin selector hmeasurable hvalid hselector k
  have hdomainMeas : MeasurableSet domain :=
    (measurableSet_northCarrierRegion selector hmeasurable hvalid hselector).inter
      (measurableSet_carrierMarkedCenterBin selector hmeasurable hvalid
        hselector k)
  have hdomainMass : mu domain ≠ 0 := by
    simpa [mu, domain] using hk
  have hdomainCarrier : domain ⊆ lineCarrier selector := by
    intro q hq
    exact hq.1.1
  have hrestrictedCarrier :
      (mu.restrict domain) (lineCarrier selector) ≠ 0 := by
    rw [Measure.restrict_apply
      (measurableSet_lineCarrier_of_selector selector hmeasurable hvalid hselector)]
    rw [Set.inter_eq_right.mpr hdomainCarrier]
    exact hdomainMass
  obtain ⟨raw, hraw, d, hd, hdtop, C, hCtop, hcover⟩ :=
    packingDim_eq_three_extract_nonzero_measure_power_piece
      (mu.restrict domain) (lineCarrier selector) hpacking
        hrestrictedCarrier hslack
  have haeDomain : ∀ᵐ q ∂mu.restrict domain, q ∈ domain :=
    ae_restrict_mem hdomainMeas
  have hrawRestricted : (mu.restrict domain) (domain ∩ raw) ≠ 0 := by
    rw [Measure.measure_inter_eq_of_ae haeDomain]
    exact hraw
  have hrawMass : mu (domain ∩ raw) ≠ 0 := by
    intro hz
    have hle :
        (mu.restrict domain) (domain ∩ raw) ≤ mu (domain ∩ raw) :=
      Measure.restrict_le_self (domain ∩ raw)
    rw [hz] at hle
    exact hrawRestricted (bot_unique hle)
  let internal : Set (E4 × E4) := domain ∩ raw
  have hinternalDomain : internal ⊆ domain := Set.inter_subset_left
  have hinternalCover :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        coveringNumber internal r ≤
          C * (ENNReal.ofReal r).rpow (-d.toReal) := by
    filter_upwards [hcover] with r hr
    exact (coveringNumber_mono Set.inter_subset_right r).trans hr
  let piece : Set (E4 × E4) := closure internal ∩ domain
  have hpieceMeas : MeasurableSet piece :=
    isClosed_closure.measurableSet.inter hdomainMeas
  have hpieceDomain : piece ⊆ domain := Set.inter_subset_right
  have hinternalPiece : internal ⊆ piece := by
    intro q hq
    exact ⟨subset_closure hq, hinternalDomain hq⟩
  have hpieceMass : mu piece ≠ 0 := by
    intro hz
    exact hrawMass (measure_mono_null hinternalPiece hz)
  have hhalf :
      Tendsto (fun r : ℝ => r / 2) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun r : ℝ => r / 2) (nhds 0) (nhds 0) := by
        have hc : ContinuousAt (fun r : ℝ => r / 2) 0 :=
          (continuous_id.div_const (2 : ℝ)).continuousAt
        simpa using hc.tendsto
      exact ht.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with r hr
      show 0 < r / (2 : ℝ)
      exact div_pos hr (by norm_num)
  have hcoverHalf := hhalf.eventually hinternalCover
  refine ⟨k, piece, hpieceMeas, hpieceDomain.trans hdomainCarrier,
    by simpa [domain] using hpieceDomain, by simpa [mu] using hpieceMass,
    d, hd, hdtop, C, hCtop, ?_⟩
  filter_upwards [hcoverHalf, self_mem_nhdsWithin] with r hr hrpos
  exact (coveringNumber_mono Set.inter_subset_left r).trans
    ((coveringNumber_closure_le internal hrpos).trans hr)

end StickyKakeya4
