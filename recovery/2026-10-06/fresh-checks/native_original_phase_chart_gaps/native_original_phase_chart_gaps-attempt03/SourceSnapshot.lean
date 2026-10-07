import Theorems.Thm_StickyKakeya4_native_coarse_carrier_geometry
import Theorems.Thm_StickyKakeya4_marked_isometric_carrier

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeOriginalPhaseChartGaps
open Classical StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeCoarseRepresentativeGeometry NativeCoarseCarrierGeometry NativeUnitParentDirections
open NativeUnitParentNormalization
open scoped RealInnerProductSpace

/-- Translating by a center of norm at most1/2 gives offset bound3 for
the actual marked chart line, including its projection correction. -/
theorem chart_offset_norm (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1/2)
    (l : MarkedLine) (hl : IsValidLine l) (hoff : ‖offset l‖ ≤ 2) :
    ‖offset (MarkedIsometricChart.line O c l)‖ ≤ 3 := by
  have hi : |inner ℝ c (direction l)| ≤ ‖c‖ := by
    simpa only [hl.1, mul_one] using abs_real_inner_le_norm c (direction l)
  have hp : ‖(inner ℝ c (direction l)) • direction l‖ ≤ ‖c‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, hl.1, mul_one] using hi
  change ‖O (offset l-c+(inner ℝ c (direction l)) • direction l)‖ ≤ 3
  rw [LinearIsometryEquiv.norm_map]
  have ht := norm_add_le (offset l-c) ((inner ℝ c (direction l)) • direction l)
  have hs := norm_sub_le (offset l) c
  linarith

/-- The constant21 is explicit: three carrier-error terms for the offset
and bounded slope, plus3 times the six-fold slope error. -/
theorem intercept_gap_of_carrier (l l' : MarkedLine)
    (hl : IsValidLine l) (hl' : IsValidLine l')
    (ht : (1/2:ℝ) ≤ direction l (3:Fin 4))
    (ht' : (1/2:ℝ) ≤ direction l' (3:Fin 4))
    (hoff : ‖offset l'‖ ≤ 3) (j : Fin 3) :
    |intercept l j-intercept l' j| ≤
      21 * dist (MarkedIsometricCarrier.carrier l) (MarkedIsometricCarrier.carrier l') := by
  let d := dist (MarkedIsometricCarrier.carrier l) (MarkedIsometricCarrier.carrier l')
  have hd : 0 ≤ d := dist_nonneg
  have ho : dist (offset l) (offset l') ≤ d := le_max_right _ _
  have hu : dist (direction l) (direction l') ≤ d := le_max_left _ _
  have hx : |offset l j.castSucc-offset l' j.castSucc| ≤ d :=
    (show _ ≤ dist (offset l) (offset l') by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (offset l) (offset l') j.castSucc).trans ho
  have hz : |offset l (3:Fin 4)-offset l' (3:Fin 4)| ≤ d :=
    (show _ ≤ dist (offset l) (offset l') by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (offset l) (offset l') (3:Fin 4)).trans ho
  have hb : |offset l' (3:Fin 4)| ≤ 3 :=
    (coordinate_abs_le_norm _ _).trans hoff
  have hs := slope_bound l hl ht j
  have hg : |slope l j-slope l' j| ≤ 6*d :=
    (slope_sub_le_direction_dist l l' hl' ht ht' j).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num))
  have he : intercept l j-intercept l' j =
      (offset l j.castSucc-offset l' j.castSucc) -
        slope l j*(offset l (3:Fin 4)-offset l' (3:Fin 4)) -
        offset l' (3:Fin 4)*(slope l j-slope l' j) := by
    unfold intercept
    ring
  rw [he]
  calc
    _ ≤ |offset l j.castSucc-offset l' j.castSucc| +
        |slope l j| * |offset l (3:Fin 4)-offset l' (3:Fin 4)| +
        |offset l' (3:Fin 4)| * |slope l j-slope l' j| := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (by rw [abs_mul])) (by rw [abs_mul]))
    _ ≤ d+2*d+3*(6*d) := add_le_add
      (add_le_add hx (mul_le_mul hs hz (abs_nonneg _) (by norm_num)))
      (mul_le_mul hb hg (abs_nonneg _) (by norm_num))
    _ = 21*d := by ring

/-- Retain the EXACT old phase partition through a fixed height-preserving
orthonormal chart. No occupied rotated-grid population is assumed. -/
theorem original_phase_chart_gaps {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i ∈ fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (N : ℕ) (hN : 0 < N) (i j : Fin n)
    (he : parentLabel D a N i=parentLabel D a N j) :
    let li := MarkedIsometricChart.line O c (NativeContractedUnitParent.line D a (0,0) i)
    let lj := MarkedIsometricChart.line O c (NativeContractedUnitParent.line D a (0,0) j)
    (∀ v : Fin 3, |slope li v-slope lj v| ≤ 672/(N:ℝ)) ∧
      ∀ v : Fin 3, |intercept li v-intercept lj v| ≤ 672/(N:ℝ) := by
  intro li lj
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi := zero_parent_valid_slab h a i
  have hj := zero_parent_valid_slab h a j
  have hli : IsValidLine li := MarkedIsometricChart.valid_line O c _ hi.1
  have hlj : IsValidLine lj := MarkedIsometricChart.valid_line O c _ hj.1
  have hti : (1/2:ℝ) ≤ direction li (3:Fin 4) := by
    change (1/2:ℝ) ≤ O (direction (NativeContractedUnitParent.line D a (0,0) i)) (3:Fin 4)
    rw [hO]
    exact hi.2.1
  have htj : (1/2:ℝ) ≤ direction lj (3:Fin 4) := by
    change (1/2:ℝ) ≤ O (direction (NativeContractedUnitParent.line D a (0,0) j)) (3:Fin 4)
    rw [hO]
    exact hj.2.1
  have hoffj : ‖offset lj‖ ≤ 3 := chart_offset_norm O c hc _ hj.1
    (compact_mark_offset (zero_parent_mem_fixedCompactClass h hK ha j)).2
  have hdist : dist (MarkedIsometricCarrier.carrier li) (MarkedIsometricCarrier.carrier lj) ≤ 32/(N:ℝ) := by
    have hchart := (MarkedIsometricCarrier.carrier_dist_two_sided O c hc _ _ hi.1 hj.1).1
    have hold := same_parameter_cell_carrier_dist h hK ha i j N hN he
    change dist (MarkedIsometricCarrier.carrier li) (MarkedIsometricCarrier.carrier lj) ≤
      2*dist (carrier D a i) (carrier D a j) at hchart
    exact hchart.trans ((mul_le_mul_of_nonneg_left hold (by norm_num)).trans_eq (by ring))
  constructor
  · intro v
    have hdir : dist (direction li) (direction lj) ≤
        dist (MarkedIsometricCarrier.carrier li) (MarkedIsometricCarrier.carrier lj) := le_max_left _ _
    have hh := (slope_sub_le_direction_dist li lj hlj hti htj v).trans
      (mul_le_mul_of_nonneg_left (hdir.trans hdist) (by norm_num))
    apply hh.trans
    calc
      6*(32/(N:ℝ)) = 192/(N:ℝ) := by ring
      _ ≤ 672/(N:ℝ) := div_le_div_of_nonneg_right (by norm_num) hNr.le
  · intro v
    exact (intercept_gap_of_carrier li lj hli hlj hti htj hoffj v).trans
      ((mul_le_mul_of_nonneg_left hdist (by norm_num)).trans_eq (by ring))

end NativeOriginalPhaseChartGaps
