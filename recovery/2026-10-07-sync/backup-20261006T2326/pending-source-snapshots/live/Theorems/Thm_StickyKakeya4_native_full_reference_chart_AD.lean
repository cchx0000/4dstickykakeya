import Theorems.Thm_StickyKakeya4_marked_isometric_finite_transport
import Theorems.Thm_StickyKakeya4_native_full_reference_carrier_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFullReferenceChartAD
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeFullCoarseShadow NativeCoarseCellSource NativeCoarseDirectionThinning
open NativeCoarseRepresentativeGeometry NativeUnitParentNormalization
open NativeFullReferenceCarrierLower MarkedIsometricCarrier

/-- Literal counts on the unchanged finite index set compare through the
proved carrier metric, rather than through a new source AD hypothesis. -/
theorem chart_ball_counts {n : ℕ} (D : FiniteScaleSource n)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1 / 2)
    (hvalid : ∀ i, IsValidLine (D.line i)) (i : Fin n) (r : ℝ) :
    wzCarrierBallCount D i (r / 2) ≤
      wzCarrierBallCount (MarkedIsometricFiniteTransport.source D O c) i r ∧
    wzCarrierBallCount (MarkedIsometricFiniteTransport.source D O c) i r ≤
      wzCarrierBallCount D i (2 * r) := by
  have hdist (j : Fin n) := carrier_dist_two_sided O c hc (D.line j) (D.line i) (hvalid j) (hvalid i)
  have hd (j : Fin n) :
      dist (wzCarrierPoint (MarkedIsometricFiniteTransport.source D O c) j)
        (wzCarrierPoint (MarkedIsometricFiniteTransport.source D O c) i) ≤
          2 * dist (wzCarrierPoint D j) (wzCarrierPoint D i) ∧
      dist (wzCarrierPoint D j) (wzCarrierPoint D i) ≤
        2 * dist (wzCarrierPoint (MarkedIsometricFiniteTransport.source D O c) j)
          (wzCarrierPoint (MarkedIsometricFiniteTransport.source D O c) i) := hdist j
  constructor
  · apply card_le_card
    intro j hj
    obtain ⟨hj, hclose⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj, by linarith only [(hd j).1, hclose]⟩
  · apply card_le_card
    intro j hj
    obtain ⟨hj, hclose⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj, by linarith only [(hd j).2, hclose]⟩

/-- The actual full reference family's carrier AD transfers to the actual
charted finite source. Lower radii below twice the mesh use the original
center index; the original all-radius upper handles the top endpoint.
The affine marks and shadings are those of the fixed source constructor. -/
theorem full_source_chart_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (hK : ∀ i, D.line i ∈ fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (level b : ℕ) (hb : b ≤ level)
    (E : Finset (Fin n × Index)) (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ ell : Fin (level + 1), ∀ p : Parent,
      (R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).Nonempty →
        D.thickness ^ zeta * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
          ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ≤
          D.thickness ^ (-zeta) * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1 / 2) :
    let S := fullSource h R a level b E
    let C := MarkedIsometricFiniteTransport.source S O c
    ∀ i : Fin (R.image (parentLabel D a (2 ^ b))).card, ∀ r : ℝ,
      C.thickness ≤ r → r ≤ 1 →
        (D.thickness ^ (2 * zeta) / 8) * (r / C.thickness) ^ 3 ≤
          (wzCarrierBallCount C i r : ℝ) ∧
        (wzCarrierBallCount C i r : ℝ) ≤
          (8 * (5832 * 770 ^ 3)) * D.thickness ^ (-zeta) * (r / C.thickness) ^ 3 := by
  intro S C i r hr hr1
  have hthick : C.thickness = S.thickness := rfl
  have hpos : 0 < S.thickness := by change 0 < 64 / ((2 ^ b : ℕ) : ℝ); positivity
  have hrS : S.thickness ≤ r := hr
  have hrpos : 0 < r := hpos.trans_le hrS
  have hvalid (j : Fin (R.image (parentLabel D a (2 ^ b))).card) : IsValidLine (S.line j) :=
    (zero_parent_valid_slab h a
      (representative h R a (2 ^ b) (parentIndex (R.image (parentLabel D a (2 ^ b))) j))).1
  have hcounts := chart_ball_counts S O c hc hvalid i r
  have hloCount : (wzCarrierBallCount S i (r / 2) : ℝ) ≤ wzCarrierBallCount C i r := by
    exact_mod_cast hcounts.1
  have hupCount : (wzCarrierBallCount C i r : ℝ) ≤ wzCarrierBallCount S i (2 * r) := by
    exact_mod_cast hcounts.2
  rw [hthick]
  constructor
  · by_cases hhalf : S.thickness ≤ r / 2
    · have hlo := full_carrier_lower h hK ha R level b hb E H i hhalf
        (show r / 2 ≤ 1 by linarith only [hr1])
      calc
        _ = D.thickness ^ (2 * zeta) * ((r / 2) / S.thickness) ^ 3 := by ring
        _ ≤ (wzCarrierBallCount S i (r / 2) : ℝ) := hlo
        _ ≤ _ := hloCount
    · have hratio : r / S.thickness ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith only [hhalf])
      have hpow : (r / S.thickness) ^ 3 ≤ 8 := by
        simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num] using
          pow_le_pow_left₀ (div_nonneg hrpos.le hpos.le) hratio 3
      have hweight : D.thickness ^ (2 * zeta) ≤ 1 :=
        Real.rpow_le_one h.1.2.1.le h.1.2.2.1 (mul_nonneg (by norm_num) hzeta)
      have hprod := mul_le_mul hweight hpow
        (show 0 ≤ (r / S.thickness) ^ 3 by positivity) (by norm_num : (0 : ℝ) ≤ 1)
      have hself : 0 < wzCarrierBallCount C i r := by
        apply card_pos.mpr
        exact ⟨i, mem_filter.mpr ⟨mem_univ i, by simpa only [dist_self] using hrpos.le⟩⟩
      have hone : (1 : ℝ) ≤ wzCarrierBallCount C i r := by
        exact_mod_cast Nat.succ_le_iff.mpr hself
      exact (show (D.thickness ^ (2 * zeta) / 8) * (r / S.thickness) ^ 3 ≤ 1 by
        nlinarith only [hprod]).trans hone
  · have hup := NativeFullReferenceSlopeCap.full_carrier_upper h R level b E hscale
      (fun p hp => (H ⟨b, by omega⟩ p hp).1) i
      (show S.thickness ≤ 2 * r by linarith only [hrS, hrpos])
    calc
      _ ≤ (wzCarrierBallCount S i (2 * r) : ℝ) := hupCount
      _ ≤ (5832 * 770 ^ 3) * D.thickness ^ (-zeta) * ((2 * r) / S.thickness) ^ 3 := hup
      _ = _ := by ring

end NativeFullReferenceChartAD
