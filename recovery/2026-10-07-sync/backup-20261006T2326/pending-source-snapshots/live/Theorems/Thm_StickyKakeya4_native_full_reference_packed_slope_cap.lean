/- UNVERIFIED draft reconstructed after the filesystem loss at 2026-10-06 10:03 UTC.
The preceding draft had not been compiled. No current verification is claimed. -/
import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_marked_isometric_finite_transport
import Theorems.Thm_StickyKakeya4_native_packed_frame_isometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section
namespace NativeFullReferencePackedSlopeCap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeFullCoarseShadow NativeCoarseCellSource
open NativeCoarseDirectionThinning NativeCoarseRepresentativeGeometry NativeUnitParentNormalization
open CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice
open scoped BigOperators

def graphDirection (l : MarkedLine) : E4 := (direction l (3 : Fin 4))⁻¹ • direction l

lemma graphDirection_spatial (l : MarkedLine) (j : Fin 3) :
    graphDirection l j.castSucc = slope l j := by
  simp only [graphDirection, slope, PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma graphDirection_height (l : MarkedLine) (hl : direction l (3 : Fin 4) ≠ 0) :
    graphDirection l (3 : Fin 4) = 1 := by
  simp only [graphDirection, PiLp.smul_apply, smul_eq_mul, inv_mul_cancel₀ hl]

lemma graphDirection_chart (O : E4 ≃ₗᵢ[ℝ] E4)
    (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4) (l : MarkedLine) :
    graphDirection (MarkedIsometricChart.line O c l) = O (graphDirection l) := by
  change ((O (direction l)) (3 : Fin 4))⁻¹ • O (direction l) =
    O ((direction l (3 : Fin 4))⁻¹ • direction l)
  rw [hO, map_smul]

theorem slope_difference_pullback (O : E4 ≃ₗᵢ[ℝ] E4)
    (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4) (l l' : MarkedLine)
    (hl : direction l (3 : Fin 4) ≠ 0) (hl' : direction l' (3 : Fin 4) ≠ 0)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hclose : ∀ j : Fin 3,
      |slope (MarkedIsometricChart.line O c l) j - slope (MarkedIsometricChart.line O c l') j| ≤ sigma)
    (j : Fin 3) : |slope l j - slope l' j| ≤ 3 * sigma := by
  let v := graphDirection (MarkedIsometricChart.line O c l) -
    graphDirection (MarkedIsometricChart.line O c l')
  have hv (k : Fin 3) : |v k.castSucc| ≤ sigma := by
    simpa only [v, PiLp.sub_apply, graphDirection_spatial] using hclose k
  have hv3 : v (3 : Fin 4) = 0 := by
    simp only [v, PiLp.sub_apply, graphDirection_chart O hO c l,
      graphDirection_chart O hO c l', hO,
      graphDirection_height l hl, graphDirection_height l' hl', sub_self]
  have hsquare (k : Fin 3) : v k.castSucc ^ 2 ≤ sigma ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (v k.castSucc)) (hv k) 2)
  have hnormsq : ‖v‖ ^ 2 ≤ 3 * sigma ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    have h0 := hsquare 0
    have h1 := hsquare 1
    have h2 := hsquare 2
    change v 0 ^ 2 + (v 1 ^ 2 + (v 2 ^ 2 + (v 3 ^ 2 + 0))) ≤ _
    rw [hv3]
    norm_num only [pow_two, zero_mul, zero_add, add_zero]
    linarith only [h0, h1, h2]
  have hnorm : ‖v‖ ≤ 3 * sigma := by
    nlinarith only [hnormsq, norm_nonneg v, hsigma, sq_nonneg sigma]
  have he : ‖graphDirection l - graphDirection l'‖ = ‖v‖ := by
    dsimp only [v]
    rw [graphDirection_chart O hO c l, graphDirection_chart O hO c l',
      ← map_sub, LinearIsometryEquiv.norm_map]
  calc
    _ = |(graphDirection l - graphDirection l') j.castSucc| := by
      rw [PiLp.sub_apply, graphDirection_spatial, graphDirection_spatial]
    _ ≤ ‖graphDirection l - graphDirection l'‖ := coordinate_abs_le_norm _ _
    _ = ‖v‖ := he
    _ ≤ 3 * sigma := hnorm

theorem slope_difference_forward (O : E4 ≃ₗᵢ[ℝ] E4)
    (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4) (l l' : MarkedLine)
    (hl : direction l (3 : Fin 4) ≠ 0) (hl' : direction l' (3 : Fin 4) ≠ 0)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hclose : ∀ j : Fin 3, |slope l j - slope l' j| ≤ sigma) (j : Fin 3) :
    |slope (MarkedIsometricChart.line O c l) j - slope (MarkedIsometricChart.line O c l') j| ≤
      3 * sigma := by
  have hInv (x : E4) : O.symm x (3 : Fin 4) = x 3 := by
    have hh := hO (O.symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at hh
    exact hh.symm
  have hz (v : MarkedLine) (hv : direction v (3 : Fin 4) ≠ 0) :
      direction (MarkedIsometricChart.line O c v) (3 : Fin 4) ≠ 0 := by
    change O (direction v) (3 : Fin 4) ≠ 0
    rw [hO]
    exact hv
  exact slope_difference_pullback O.symm hInv (-O c)
    (MarkedIsometricChart.line O c l) (MarkedIsometricChart.line O c l')
    (hz l hl) (hz l' hl') hsigma
    (fun k => by simpa only [MarkedIsometricCarrier.line_inverse] using hclose k) j

theorem same_parent_chart_slope_gap {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4)
    (i i' : Fin n) (hp : parentLabel D a N i = parentLabel D a N i') (j : Fin 3) :
    |slope (MarkedIsometricChart.line O c (NativeContractedUnitParent.line D a (0, 0) i)) j -
      slope (MarkedIsometricChart.line O c (NativeContractedUnitParent.line D a (0, 0) i')) j| ≤
      3 / (N : ℝ) := by
  have hz (v : Fin n) : direction (NativeContractedUnitParent.line D a (0, 0) v) (3 : Fin 4) ≠ 0 := by
    have hh := (zero_parent_valid_slab h a v).2.1
    linarith only [hh]
  have hh := slope_difference_forward O hO c
    (NativeContractedUnitParent.line D a (0, 0) i)
    (NativeContractedUnitParent.line D a (0, 0) i') (hz i) (hz i')
    (show 0 ≤ 1 / (N : ℝ) by positivity)
    (fun k => by
      have hclose := NativeNormalizedParentCarrierMetric.same_floor_mul_close
        (slope (D.line i) k) (slope (D.line i') k) N hN
        (congrFun (congrArg Prod.fst hp) k)
      simpa only [slope, direction_zero_parent h a] using hclose) j
  simpa only [mul_one_div] using hh

theorem full_chart_cube_card {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a (2 ^ b) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / ((2 ^ b : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (2 ^ b) i = p)).card : ℝ))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4)
    (A : Finset (Fin (R.image (parentLabel D a (2 ^ b))).card))
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (z : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j : Fin 3,
      z j ≤ slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E) O c).line i) j ∧
        slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E) O c).line i) j ≤ z j + sigma) :
    (A.card : ℝ) ≤ 5832 * D.thickness ^ (-zeta) *
      (((2 ^ b : ℕ) : ℝ) * (6 * sigma) + 2) ^ 3 := by
  by_cases hA : A.Nonempty
  · obtain ⟨i0, hi0⟩ := hA
    let S := fullSource h R a level b E
    have hlast (i : Fin (R.image (parentLabel D a (2 ^ b))).card) :
        direction (S.line i) (3 : Fin 4) ≠ 0 := by
      have hh := zero_parent_valid_slab h a
        (representative h R a (2 ^ b) (parentIndex (R.image (parentLabel D a (2 ^ b))) i))
      have hv : (1 / 2 : ℝ) ≤ direction (S.line i) (3 : Fin 4) := hh.2.1
      linarith only [hv]
    apply NativeFullReferenceSlopeCap.full_subset_cube_card h R level b E hscale H A
      (show 0 ≤ 6 * sigma by positivity) (fun j => slope (S.line i0) j - 3 * sigma)
    intro i hi j
    have hdiff := slope_difference_pullback O hO c (S.line i) (S.line i0) (hlast i) (hlast i0)
      hsigma (fun k => by
        have hx := hbox i hi k
        have hy := hbox i0 hi0 k
        apply abs_le.mpr
        constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]) j
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
    constructor <;> linarith only [hlo, hhi]
  · rw [not_nonempty_iff_eq_empty.mp hA, card_empty, Nat.cast_zero]
    positivity

theorem full_chart_cube_ratio {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a (2 ^ b) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / ((2 ^ b : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (2 ^ b) i = p)).card : ℝ))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3 : Fin 4) = x 3) (c : E4)
    (A : Finset (Fin (R.image (parentLabel D a (2 ^ b))).card)) {sigma : ℝ}
    (hsigma : 64 / ((2 ^ b : ℕ) : ℝ) ≤ sigma) (z : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j : Fin 3,
      z j ≤ slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E) O c).line i) j ∧
        slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E) O c).line i) j ≤ z j + sigma) :
    (A.card : ℝ) ≤ (5832 * 386 ^ 3) * D.thickness ^ (-zeta) *
      (sigma / (64 / ((2 ^ b : ℕ) : ℝ))) ^ 3 := by
  have hN : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by positivity
  have hd : (0 : ℝ) < 64 / ((2 ^ b : ℕ) : ℝ) := by positivity
  have hs : 0 ≤ sigma := hd.le.trans hsigma
  have hcap := full_chart_cube_card h R level b E hscale H O hO c A hs z hbox
  have hratio : 1 ≤ sigma / (64 / ((2 ^ b : ℕ) : ℝ)) :=
    (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hsigma)
  have he : ((2 ^ b : ℕ) : ℝ) * sigma = 64 * (sigma / (64 / ((2 ^ b : ℕ) : ℝ))) := by
    field_simp [hN.ne']
  have hside : ((2 ^ b : ℕ) : ℝ) * (6 * sigma) + 2 ≤
      386 * (sigma / (64 / ((2 ^ b : ℕ) : ℝ))) := by
    nlinarith only [hratio, he]
  have hpow := pow_le_pow_left₀ (show 0 ≤ ((2 ^ b : ℕ) : ℝ) * (6 * sigma) + 2 by positivity) hside 3
  calc
    _ ≤ 5832 * D.thickness ^ (-zeta) * (((2 ^ b : ℕ) : ℝ) * (6 * sigma) + 2) ^ 3 := hcap
    _ ≤ 5832 * D.thickness ^ (-zeta) * (386 * (sigma / (64 / ((2 ^ b : ℕ) : ℝ)))) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

theorem packed_cube_ratio {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a (2 ^ b) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / ((2 ^ b : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (2 ^ b) i = p)).card : ℝ))
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hdim : Module.finrank ℝ P = tangentDim s)
    (A : Finset (Fin (R.image (parentLabel D a (2 ^ b))).card)) {sigma : ℝ}
    (hsigma : 64 / ((2 ^ b : ℕ) : ℝ) ≤ sigma) (z : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j : Fin 3,
      z j ≤ slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E)
          (NativePackedFrameIsometry.frame s P hP hdim) 0).line i) j ∧
        slope ((MarkedIsometricFiniteTransport.source (fullSource h R a level b E)
          (NativePackedFrameIsometry.frame s P hP hdim) 0).line i) j ≤ z j + sigma) :
    (A.card : ℝ) ≤ (5832 * 386 ^ 3) * D.thickness ^ (-zeta) *
      (sigma / (64 / ((2 ^ b : ℕ) : ℝ))) ^ 3 :=
  full_chart_cube_ratio h R level b E hscale H (NativePackedFrameIsometry.frame s P hP hdim)
    (NativePackedFrameIsometry.frame_height s P hP hdim) 0 A hsigma z hbox

theorem same_reference_packed_cube_ratio {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m + b ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput
      (NativeLocalParentSource.source h R Eref a m p) localEta)
    (hbudget : (64 : ℝ) ^ 3 * (NativeLocalParentSource.source h R Eref a m p).thickness ^ e ≤
      D.thickness ^ zeta)
    (selected : Finset (Fin (NativeLocalParentSource.parentLabels D R a (2 ^ m) p).card × Index))
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hdim : Module.finrank ℝ P = tangentDim s)
    (A : Finset (Fin (((univ : Finset (Fin (NativeLocalParentSource.parentLabels D R a (2 ^ m) p).card)).image
      (parentLabel (NativeLocalParentSource.source h R Eref a m p) 0 (2 ^ b))).card)))
    {sigma : ℝ} (hsigma : 64 / ((2 ^ b : ℕ) : ℝ) ≤ sigma) (z : Fin 3 → ℝ)
    (hbox : let C := MarkedIsometricFiniteTransport.source
        (fullSource hReferenceNative univ 0 (level - m + 6) b selected)
        (NativePackedFrameIsometry.frame s P hP hdim) 0
      ∀ i ∈ A, ∀ j : Fin 3, z j ≤ slope (C.line i) j ∧ slope (C.line i) j ≤ z j + sigma) :
    (A.card : ℝ) ≤ (5832 * 386 ^ 3) *
      (NativeLocalParentSource.source h R Eref a m p).thickness ^ (-e) *
        (sigma / (64 / ((2 ^ b : ℕ) : ℝ))) ^ 3 := by
  have H := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b hmb p hbudget
  have hscale := NativeSameReferenceChartBounds.source_scale_guard (a := a)
    h R Eref level m b p HB.2.1 hmb
  exact packed_cube_ratio (a := 0) (zeta := e) hReferenceNative univ (level - m + 6) b selected
    hscale (fun q hq => (H ⟨b, by omega⟩ q hq).1) s P hP hdim A hsigma z hbox

end NativeFullReferencePackedSlopeCap
