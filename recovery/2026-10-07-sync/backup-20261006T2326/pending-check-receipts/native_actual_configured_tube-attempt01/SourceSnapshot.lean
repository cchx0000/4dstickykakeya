import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_incidence
import Theorems.Thm_StickyKakeya4_native_zero_parent_radius_containment
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_marked_isometric_finite_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeActualConfiguredTube
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseRepresentativeGeometry
open NativeFullCoarseShadow NativeLocalParentSource

/-- The full-family label of an actual fine line. Every occupied second
parent is retained, and the map does not select a direction color. -/
def fullIndex {n : ℕ} (D : FiniteScaleSource n) (b : ℕ) (i : Fin n) :
    Fin (((univ : Finset (Fin n)).image (parentLabel D 0 (2 ^ b))).card) :=
  ((univ : Finset (Fin n)).image (parentLabel D 0 (2 ^ b))).equivFin
    ⟨parentLabel D 0 (2 ^ b) i, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩

lemma fullIndex_readback {n : ℕ} (D : FiniteScaleSource n) (b : ℕ) (i : Fin n) :
    parentIndex ((univ : Finset (Fin n)).image (parentLabel D 0 (2 ^ b)))
      (fullIndex D b i) = parentLabel D 0 (2 ^ b) i := by
  simp only [fullIndex, parentIndex, Equiv.symm_apply_apply]

/-- A literal original shading edge maps to its actual full second-parent
tube after the corrected pxy realization. Native admission is used only for
the existing fine reference source. The two displayed scale conditions are
the actual base/radius match; no configured-point containment is assumed. -/
theorem point_mem_full_tube {n : ℕ} {D : FiniteScaleSource n} {eta localEta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i = wzCellShading (mesh D) cells i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m)
    (hscale : D.thickness ≤ (rho m) ^ 2) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (level b : ℕ) (selected : Finset (Fin (parentLabels D R a (2 ^ m) p).card × Index))
    (i : Fin (parentLabels D R a (2 ^ m) p).card) (k : Index)
    (hk : (NativePaddedCellSource.originalLabel (parentLabels D R a (2 ^ m) p) i, k) ∈
      NativeCubicalIncidenceCounts.incidences cells)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1 / 4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1 / 4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m * (R0 : ℝ))
    (hmatch : mu m * (R0 : ℝ) ≤ 4096 / ((2 ^ b : ℕ) : ℝ)) :
    let S := source h R Eref a m p
    let C := MarkedIsometricFiniteTransport.source
      (fullSource hReferenceNative univ 0 level b selected)
      (NativePackedFrameIsometry.frame s P hP hd) 0
    NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k ∈
      markedUnitTube (C.line (fullIndex S b i)) C.thickness := by
  intro S C
  let O := NativePackedFrameIsometry.frame s P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 k
  let Q := (univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
    (parentLabel S 0 (2 ^ b))
  let j := NativeCoarseDirectionThinning.representative hReferenceNative univ 0 (2 ^ b)
    (parentIndex Q (fullIndex S b i))
  have hp := (mem_parentLabels D R a (2 ^ m) p _).mp
    (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2 ^ m) p) i)
  have hx : rawPoint D a m p k ∈ markedUnitTube (S.line i) (3 * rho m) := by
    simpa only [S, source_line] using
      NativeReferenceXYGridIncidence.original_edge_rawPoint_three_rho h cells hcells ha
        m hm hscale p _ k hk hp.2
  have hcommon := NativeActualRelativeCoarseAdmission.source_common_height_zero
    h R Eref a m p hReferenceNative
  have hj : parentLabel S 0 (2 ^ b) i = parentLabel S 0 (2 ^ b) j := by
    have hh := (representative_spec hReferenceNative univ 0 (2 ^ b)
      (parentIndex_mem Q (fullIndex S b i))).2
    simpa only [fullIndex_readback] using hh.symm
  have hround : dist (O.symm cfg)
      (NativeContractedUnitParent.physicalMap S 0 (0, 0) (rawPoint D a m p k)) ≤
        3 * ((mu m * (R0 : ℝ)) / 512) := by
    rw [← O.dist_map, LinearIsometryEquiv.apply_symm_apply,
      NativeZeroParentPhysicalMap.zero_map]
    exact NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg
      hF hCfg R0 hR0 k hbase
  have ht : 3 * rho m ≤ 12288 / ((2 ^ b : ℕ) : ℝ) := by
    linarith only [hbase, hmatch]
  have hb : (mu m * (R0 : ℝ)) / 512 ≤ 8 / ((2 ^ b : ℕ) : ℝ) := by
    linarith only [hmatch]
  have hy := NativeZeroParentRadiusContainment.rounded_radius_mem hReferenceNative hcommon
    (2 ^ b) (by positivity) i j hj (rawPoint D a m p k) (O.symm cfg) hx hround ht hb
  have hout := (MarkedIsometricChart.tube_membership O 0
    (NativeContractedUnitParent.line S 0 (0, 0) j) (64 / ((2 ^ b : ℕ) : ℝ))
      (O.symm cfg)).2 hy
  have hline : C.line (fullIndex S b i) =
      MarkedIsometricChart.line O 0 (NativeContractedUnitParent.line S 0 (0, 0) j) := rfl
  have hthick : C.thickness = 64 / ((2 ^ b : ℕ) : ℝ) := rfl
  rw [hline, hthick]
  simpa only [MarkedIsometricChart.point, sub_zero, LinearIsometryEquiv.apply_symm_apply]
    using hout

end NativeActualConfiguredTube
