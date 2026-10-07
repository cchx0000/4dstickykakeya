import Theorems.Thm_StickyKakeya4_native_relative_parent_profiles
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_middle_window_balance
import Theorems.Thm_StickyKakeya4_native_full_reference_chart_AD
import Theorems.Thm_StickyKakeya4_native_full_reference_coarse_CW

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 250000
set_option profiler true
set_option profiler.threshold 100
set_option diagnostics true
noncomputable section
namespace NativeSameReferenceChartBounds
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeLocalParentSource NativeMiddleWindowBalance
open NativeRelativeParentProfiles NativeFullCoarseShadow NativeUnitParentNormalization
open NativeFullReferenceChartAD NativeFullReferenceCoarseCW
open scoped ENNReal

/-- Original HB supplies the populations of univ in the same existing
local reference source. The scalar budget is exactly the profile payment
exported by NativeReferenceParentAdmissionBudget, not a new AD premise. -/
theorem population_through {n : ℕ} {D : FiniteScaleSource n} {eta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m + b ≤ level) (p : Parent)
    (hbudget : (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ e ≤ D.thickness ^ zeta) :
    let S := source h R Eref a m p
    ∀ j : Fin (b + 1), ∀ q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).filter
        (fun i => parentLabel S 0 (2 ^ j.val) i = q)).Nonempty →
      S.thickness ^ e * ((1 / ((2 ^ j.val : ℕ) : ℝ)) / S.thickness) ^ 3 ≤
        (((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).filter
          (fun i => parentLabel S 0 (2 ^ j.val) i = q)).card : ℝ) ∧
      (((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).filter
        (fun i => parentLabel S 0 (2 ^ j.val) i = q)).card : ℝ) ≤
          S.thickness ^ (-e) * ((1 / ((2 ^ j.val : ℕ) : ℝ)) / S.thickness) ^ 3 := by
  obtain ⟨_hcells, _hdy, _ha, _hR, _hhalf, _hshade, _hden, _hCW, H⟩ := HB
  intro S j q hq
  exact source_dyadic_population_power h R Eref a zeta level H m j.val
    (by omega) p q hbudget hq

/-- The original depth inequality supplies the genuine relative-scale
guard, without identifying the local fine thickness with the XY mesh. -/
theorem source_scale_guard {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (level m b : ℕ) (p : Parent)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hmb : m + b ≤ level) :
    ((2 ^ b : ℕ) : ℝ) * (source h R Eref a m p).thickness ≤ 1 := by
  have hfine := NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m + b, by omega⟩
  have heq : ((2 ^ b : ℕ) : ℝ) * (((2 ^ m : ℕ) : ℝ) * D.thickness / 64) =
      ((2 ^ (m + b) : ℕ) : ℝ) * D.thickness / 64 := by
    push_cast
    rw [pow_add]
    ring
  rw [source_thickness, heq]
  nlinarith only [hfine]

/-- The shading-depth parameter is absent from the actual carrier count. -/
lemma full_chart_count_depth {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level level' b : ℕ) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) (r : ℝ) :
    wzCarrierBallCount (MarkedIsometricFiniteTransport.source (fullSource h R a level b E) O c) i r =
      wzCarrierBallCount (MarkedIsometricFiniteTransport.source (fullSource h R a level' b E) O c) i r := by
  unfold wzCarrierBallCount wzCarrierPoint
  rfl

/-- Tube containment counts likewise keep only the genuine lines and radius. -/
lemma tube_count_congr {n : ℕ} (D D' : FiniteScaleSource n)
    (hline : ∀ i, D.line i = D'.line i) (hthick : D.thickness = D'.thickness)
    (U : Set E4) : wzContainedTubeCount D U = wzContainedTubeCount D' U := by
  unfold wzContainedTubeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _hi
  rw [hline i, hthick]

lemma full_thickness {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (E : Finset (Fin n × Index)) :
    (fullSource h R a level b E).thickness = 64 / ((2 ^ b : ℕ) : ℝ) := rfl

lemma full_tube_count_depth {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level level' b : ℕ) (E : Finset (Fin n × Index)) (U : Set E4) :
    wzContainedTubeCount (fullSource h R a level b E) U =
      wzContainedTubeCount (fullSource h R a level' b E) U := by
  apply tube_count_congr
  · intro i
    rw [NativeFullReferenceSlopeCap.full_line, NativeFullReferenceSlopeCap.full_line]
  · rw [full_thickness, full_thickness]

/-- Geometric transport is proved with an abstract fine source first, so
the kernel never normalizes a nested local-source shading inside a tube
containment proposition. The target keeps the specified shading depth. -/
theorem chart_bounds_of_populations {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (hK : ∀ i, D.line i ∈ fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (hR : R.Nonempty) (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ j : Fin (b + 1), ∀ q : Parent,
      (R.filter (fun i => parentLabel D a (2 ^ j.val) i = q)).Nonempty →
        D.thickness ^ zeta * ((1 / ((2 ^ j.val : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
          ((R.filter (fun i => parentLabel D a (2 ^ j.val) i = q)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2 ^ j.val) i = q)).card : ℝ) ≤
          D.thickness ^ (-zeta) * ((1 / ((2 ^ j.val : ℕ) : ℝ)) / D.thickness) ^ 3)
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1 / 2) :
    let F := fullSource h R a level b E
    let C := MarkedIsometricFiniteTransport.source F O c
    (∀ i, ∀ r : ℝ, C.thickness ≤ r → r ≤ 1 →
      (D.thickness ^ (2 * zeta) / 8) * (r / C.thickness) ^ 3 ≤ (wzCarrierBallCount C i r : ℝ) ∧
      (wzCarrierBallCount C i r : ℝ) ≤
        (8 * (5832 * 770 ^ 3)) * D.thickness ^ (-zeta) * (r / C.thickness) ^ 3) ∧
    (∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount C U : ℝ≥0∞) ≤
        (373248 * 512 ^ 4 : ℝ≥0∞) * (ENNReal.ofReal D.thickness).rpow (-eta - 3 * zeta) *
          volume U * (R.image (parentLabel D a (2 ^ b))).card) := by
  intro F C
  constructor
  · have had := full_source_chart_bounds h hzeta hK ha R b b le_rfl E hscale H O c hc
    dsimp only at had
    have hthick : C.thickness = 64 / ((2 ^ b : ℕ) : ℝ) := rfl
    have hthick' : (MarkedIsometricFiniteTransport.source (fullSource h R a b b E) O c).thickness =
        64 / ((2 ^ b : ℕ) : ℝ) := rfl
    rw [hthick'] at had
    rw [hthick]
    intro i r hr hr1
    have hcount := full_chart_count_depth h R a level b b E O c i r
    change wzCarrierBallCount C i r = _ at hcount
    rw [hcount]
    exact had i r hr hr1
  · apply MarkedIsometricFiniteTransport.CW_transport F O c
      ((373248 * 512 ^ 4 : ℝ≥0∞) * (ENNReal.ofReal D.thickness).rpow (-eta - 3 * zeta))
    intro U hU
    have hcount := full_tube_count_depth h R a level b b E U
    change wzContainedTubeCount F U = _ at hcount
    rw [hcount]
    exact full_CW h ha R hR b b le_rfl hscale H E U hU

/-- AD and CW for the second full source on univ of the SAME admitted
first-reference parent. No new R is selected and no original line label is
discarded. The native proof belongs only to the fine reference source.
The actual shading depth remains level-m+6; only geometric populations
through b are read, because the carrier/tube counts ignore shading data. -/
theorem same_reference_chart_bounds {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (he : 0 ≤ e)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m + b ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (hbudget : (64 : ℝ) ^ 3 * (source h R Eref a m p).thickness ^ e ≤ D.thickness ^ zeta)
    (selected : Finset (Fin (parentLabels D R a (2 ^ m) p).card × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (hc : ‖c‖ ≤ 1 / 2) :
    let S := source h R Eref a m p
    let F := fullSource hReferenceNative univ 0 (level - m + 6) b selected
    let C := MarkedIsometricFiniteTransport.source F O c
    (∀ i, ∀ r : ℝ, C.thickness ≤ r → r ≤ 1 →
      (S.thickness ^ (2 * e) / 8) * (r / C.thickness) ^ 3 ≤ (wzCarrierBallCount C i r : ℝ) ∧
      (wzCarrierBallCount C i r : ℝ) ≤
        (8 * (5832 * 770 ^ 3)) * S.thickness ^ (-e) * (r / C.thickness) ^ 3) ∧
    (∀ U : Set E4, Convex ℝ U →
      (wzContainedTubeCount C U : ℝ≥0∞) ≤
        (373248 * 512 ^ 4 : ℝ≥0∞) * (ENNReal.ofReal S.thickness).rpow (-localEta - 3 * e) *
          volume U * ((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
            (parentLabel S 0 (2 ^ b))).card) := by
  intro S F C
  have H := population_through h original R level HB Eref m b hmb p hbudget
  have hscale := source_scale_guard (a := a) h R Eref level m b p HB.2.1 hmb
  have hcommon := NativeActualRelativeCoarseAdmission.source_common_height_zero h R Eref a m p hReferenceNative
  have hcompact (i : Fin (parentLabels D R a (2 ^ m) p).card) : S.line i ∈ fixedCompactClass := by
    have hp := (mem_parentLabels D R a (2 ^ m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2 ^ m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2 ^ m) p _ hp.2
  have huniv : (univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).Nonempty :=
    ⟨⟨0, hReferenceNative.1.1⟩, mem_univ _⟩
  exact chart_bounds_of_populations hReferenceNative he hcompact hcommon univ huniv
    (level - m + 6) b selected hscale H O c hc

end NativeSameReferenceChartBounds
