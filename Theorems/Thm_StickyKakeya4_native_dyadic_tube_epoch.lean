import Theorems.Thm_StickyKakeya4_native_dyadic_tube_stopping
import Theorems.Thm_StickyKakeya4_finite_cell_label_reduction

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeDyadicTubeEpoch

open NativeDyadicTubeStopping ActualTubeFootprintProfiles
open DisjointProfileEpochs FiniteCoverProfileEpochs FiniteCellLabelReduction
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

def position (A : Finset Plane) (p : A) : Plane := p.val

def cells (A : Finset Plane) (δ : ℝ) (N : ℕ) (i : Index N) : A → GridLabel 1 :=
  grid (position A) (scale δ i.val.1)

def families (A : Finset Plane) (δ : ℝ) (N : ℕ) (i : Index N) : Finset (Finset A) :=
  footprints (position A) (scale δ i.val.1) (scale δ i.val.2)

def spatialConstant (K t : ℝ) : ℝ := (9 : ℝ) ^ 2 * (6 : ℝ) ^ t * K ^ 2

def pruningRate (N : ℕ) (K t : ℝ) : ℝ :=
  1 / (4 * (Fintype.card (Index N) : ℝ) * spatialConstant K t * K)

def realThreshold (δ : ℝ) (N : ℕ) (K t : ℝ) (i : Index N) : ℝ :=
  pruningRate N K t * (scale δ i.val.1 / δ) ^ t

def threshold (δ : ℝ) (N : ℕ) (K t : ℝ) (i : Index N) : ℕ :=
  ⌊realThreshold δ N K t i⌋₊

lemma index_card_pos (N : ℕ) : 0 < Fintype.card (Index N) :=
  Fintype.card_pos_iff.mpr ⟨origin N⟩

lemma index_card_le (N : ℕ) : Fintype.card (Index N) ≤ (N + 1) ^ 2 := by
  rw [Fintype.card_coe]
  calc
    (pairMenu N).card ≤ ((Finset.range (N + 1)).product (Finset.range (N + 1))).card :=
      Finset.card_filter_le _ _
    _ = (N + 1) ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product]; simp [pow_two]

lemma spatialConstant_pos {K t : ℝ} (hK : 1 ≤ K) : 0 < spatialConstant K t := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  unfold spatialConstant
  positivity

lemma pruningRate_pos (N : ℕ) {K t : ℝ} (hK : 1 ≤ K) : 0 < pruningRate N K t := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hindex : (0 : ℝ) < Fintype.card (Index N) := by exact_mod_cast index_card_pos N
  have hconstant := spatialConstant_pos (t := t) hK
  unfold pruningRate
  positivity

lemma realThreshold_pos {δ K t : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K) (N : ℕ) (i : Index N) :
    0 < realThreshold δ N K t i :=
  mul_pos (pruningRate_pos N hK) (Real.rpow_pos_of_pos (div_pos (scale_pos hδ _) hδ) _)

lemma source_card (A : Finset Plane) : (Finset.univ : Finset A).card = A.card := by simp

lemma source_grid_image (A : Finset Plane) (δ : ℝ) (N : ℕ) (i : Index N) :
    (Finset.univ.image (cells A δ N i)).card =
      (A.image (ADGridCoverMenus.gridLabel (scale δ i.val.1))).card := by
  classical
  have hpos : Finset.univ.image (position A) = A := by ext p; simp [position]
  have himage : Finset.univ.image (cells A δ N i) =
      A.image (ADGridCoverMenus.gridLabel (scale δ i.val.1)) := by
    conv_rhs => rw [← hpos, Finset.image_image]
    rfl
  rw [himage]

lemma original_card_lower (A : Finset Plane) {δ K t : ℝ}
    (hne : A.Nonempty) (_hδ : 0 < δ) (hδone : δ ≤ 1) (hK : 1 ≤ K)
    (hAD : ADBounds A δ K t) : (1 / δ) ^ t ≤ K * (A.card : ℝ) := by
  obtain ⟨x, hx⟩ := hne
  have hlower := (hAD x hx 1 hδone (by norm_num)).1
  have hcard : ((carrierBall A x 1).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show carrierBall A x 1 ⊆ A from
      fun p hp => ((mem_carrierBall A p x 1).mp hp).1)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have h := (div_le_iff₀ hKpos).mp (hlower.trans hcard)
  simpa only [mul_comm] using h

/-- The entire occupied-cell floor budget is paid once. The chosen positive
rate is explicit in the original AD constant and finite scale-pair count. -/
theorem budget_quarter (A : Finset Plane) (δ K t : ℝ) (N : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (htop : scale δ N ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t) :
    4 * rawPenalty (cells A δ N) (threshold δ N K t) Finset.univ ≤ A.card := by
  have hδN : δ ≤ scale δ N := by simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le N)
  have hδone : δ ≤ 1 := hδN.trans htop
  have hlower := original_card_lower A hne hδ hδone hK hAD
  have hrate : 0 < pruningRate N K t := pruningRate_pos N hK
  have hD : 0 < spatialConstant K t := spatialConstant_pos hK
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hindex : (0 : ℝ) < Fintype.card (Index N) := by exact_mod_cast index_card_pos N
  have hterm (i : Index N) :
      (((Finset.univ.image (cells A δ N i)).card * threshold δ N K t i : ℕ) : ℝ) ≤
        pruningRate N K t * spatialConstant K t * K * (A.card : ℝ) := by
    have hi := (mem_pairMenu N i.val).mp i.property
    have hr : 0 < scale δ i.val.1 := scale_pos hδ _
    have hδr : δ ≤ scale δ i.val.1 := by simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le i.val.1)
    have hrone : scale δ i.val.1 ≤ 1 := (scale_mono hδ.le (hi.1.trans hi.2)).trans htop
    have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A A hδ hδr hrone hrone
      hK ht ht2 hdiam hAD (Finset.Subset.refl A) hdiam
    have hfloor : (threshold δ N K t i : ℝ) ≤
        pruningRate N K t * (scale δ i.val.1 / δ) ^ t :=
      Nat.floor_le (realThreshold_pos hδ hK N i).le
    have hratio : (1 / scale δ i.val.1) * (scale δ i.val.1 / δ) = 1 / δ := by field_simp
    calc
      _ = ((A.image (ADGridCoverMenus.gridLabel (scale δ i.val.1))).card : ℝ) *
          (threshold δ N K t i : ℝ) := by rw [Nat.cast_mul, source_grid_image]
      _ ≤ (spatialConstant K t * (1 / scale δ i.val.1) ^ t) *
          (pruningRate N K t * (scale δ i.val.1 / δ) ^ t) :=
        mul_le_mul hgrid hfloor (Nat.cast_nonneg _) (by positivity)
      _ = pruningRate N K t * spatialConstant K t * (1 / δ) ^ t := by
        rw [← hratio, Real.mul_rpow (by positivity : 0 ≤ 1 / scale δ i.val.1)
          (by positivity : 0 ≤ scale δ i.val.1 / δ)]
        ring
      _ ≤ pruningRate N K t * spatialConstant K t * K * (A.card : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left hlower (mul_pos hrate hD).le
        simpa only [mul_assoc] using hm
  have hsum : (rawPenalty (cells A δ N) (threshold δ N K t) Finset.univ : ℝ) ≤ (A.card : ℝ) / 4 := by
    calc
      _ = ∑ i : Index N,
          (((Finset.univ.image (cells A δ N i)).card * threshold δ N K t i : ℕ) : ℝ) := by
        simp only [rawPenalty, Nat.cast_sum]
      _ ≤ ∑ _i : Index N, pruningRate N K t * spatialConstant K t * K * (A.card : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (A.card : ℝ) / 4 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pruningRate]
        field_simp
  exact_mod_cast (show (4 : ℝ) * (rawPenalty (cells A δ N) (threshold δ N K t) Finset.univ : ℝ) ≤
    (A.card : ℝ) by linarith only [hsum])


lemma actual_profile (A : Finset Plane) (δ : ℝ) (N : ℕ) (i : Index N) (E : Finset A) :
    profile (families A δ N) (cells A δ N) i E =
      coverProfile (position A) (scale δ i.val.1) (scale δ i.val.2) E := rfl

/-- Native global preparation: the stop, pruning rate, threshold budget,
maximizing tubes and disjoint whole-cell fibers are all constructed from the
original AD carrier. The retained mass counts unchanged original points. -/
theorem exists_native_disjoint_epoch (A : Finset Plane) (δ ε K t : ℝ) (N : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (hN : 0 < N) (htop : scale δ N ≤ 1)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ CoverProfileStopping.stepBudget ε * (N : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t) :
    ∃ e : Epoch A (Index N), ∃ D : StoppedProfile (position A) δ ε K t N e.start,
      D.pair = e.index.val ∧
      (∀ F ∈ e.pieces, F.Nonempty) ∧ e.pieces.Pairwise Disjoint ∧
      A.card ≤ 2 * (Fintype.card (Index N) * rank 2 A.card) * (support e.pieces).card ∧
      ((support e.pieces).image (position A)).card = (support e.pieces).card ∧
      (∀ F ∈ e.pieces, ∃ E ⊆ e.start, ∃ T : TubeData 1,
        Regular (gridCells (cells A δ N)) (fun j => threshold δ N K t j.1) E ∧ F ⊆ E ∧
        F = wholeCells (cells A δ N e.index) E
          (trace (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) T) ∧
        (∀ a ∈ F, InTube T (2 * scale δ e.index.val.1) (scale δ e.index.val.2) (position A a)) ∧
        ((F.image (cells A δ N e.index)).card : ℝ) ≥
          (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent / 2 ∧
        realThreshold δ N K t e.index / 4 *
          (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤ (F.card : ℝ)) := by
  classical
  obtain ⟨select, hselect⟩ := exists_stopping_selector A (position A) (fun a => a.property)
    δ ε K t N hδ hN htop hε hεhalf hK ht ht2 hlarge hdiam hAD
  have hquarter := budget_quarter A δ K t N hne hδ htop hK ht ht2 hdiam hAD
  have hbudget : rawPenalty (cells A δ N) (threshold δ N K t) Finset.univ <
      (Finset.univ : Finset A).card := by
    rw [source_card]
    have hcard := hne.card_pos
    omega
  have hcoverage : Covers (families A δ N) := by
    intro i a
    exact point_covered (position A) (scale_pos hδ i.val.1).le (scale_pos hδ i.val.2).le a
  obtain ⟨e, _hstart, hselected, hvalid, hnonempty, hdisjoint, _hrichNat, _hsupport, hmass⟩ :=
    exists_large_raw_label_epoch (families A δ N) (cells A δ N) hcoverage
      (threshold δ N K t) select 2 (by decide) Finset.univ hbudget
  obtain ⟨D, hD⟩ := hselect e.start hvalid.1
  have hDpair : D.pair = e.index.val := by simpa only [hselected] using hD
  refine ⟨e, D, hDpair, hnonempty, hdisjoint, ?_, ?_, ?_⟩
  · rw [source_card] at hmass
    rw [Nat.mul_assoc]
    omega
  · exact Finset.card_image_of_injective _ Subtype.val_injective
  · intro F hF
    obtain ⟨E, hES, hreg, hFE, hactive, hrule⟩ := hvalid.2 F hF
    obtain ⟨W, hW, hmax, hwhole, _hNat⟩ := hrule.2
    obtain ⟨T, rfl⟩ := (mem_footprints (position A) _ _ W).mp hW
    have hwholeReal := wholeCells_card_ge_half_real (cells A δ N) (realThreshold δ N K t)
      E (trace (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) T) e.index hreg
    rw [← hwhole, hmax, actual_profile] at hwholeReal
    have hactiveReal :
        (coverProfile (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) e.start : ℝ) ≤
        2 * (coverProfile (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) E : ℝ) := by
      exact_mod_cast hactive
    have himage : (F.image (cells A δ N e.index)).card =
        coverProfile (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) E := by
      rw [hwhole, wholeCells_image]
      exact hmax
    have hlower : (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤
        (coverProfile (position A) (scale δ e.index.val.1) (scale δ e.index.val.2) e.start : ℝ) := by
      simpa only [counts, hDpair] using D.selected_lower
    have hthreshold := (realThreshold_pos (t := t) hδ hK N e.index).le
    refine ⟨E, hES, T, hreg, hFE, hwhole, ?_, ?_, ?_⟩
    · intro a ha
      rw [hwhole] at ha
      exact wholeCells_in_double_width (position A) T E (scale_pos hδ e.index.val.1) ha
    · rw [himage]
      linarith only [hlower, hactiveReal]
    · have hscaled := mul_le_mul_of_nonneg_left (hlower.trans hactiveReal)
        (div_nonneg hthreshold (by norm_num : (0 : ℝ) ≤ 4))
      nlinarith only [hscaled, hwholeReal]

end
end NativeDyadicTubeEpoch
