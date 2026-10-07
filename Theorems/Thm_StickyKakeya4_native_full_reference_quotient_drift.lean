/- UNVERIFIED actual quotient drift; awaits the coordinated quotient-map import. -/
import Theorems.Thm_StickyKakeya4_native_full_reference_direction_drift
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeFullReferenceQuotientDrift
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseCellSource NativeFullCoarseShadow NativeLocalParentSource
open NativeIncidentAffineAnchorGeometry NativeHorizontalGrainSlice NativeReferenceXYGridLinear
open NativeFullReferenceDirectionDrift
open scoped Matrix.Norms.Elementwise

/-- The true matrix quotient has operator bound2, so the actual full-source
representative contributes at most6/2^b. No coarse-direction drift bound is
an input; it is obtained from the representative's literal phase label. -/
theorem full_quotient_drift {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (j : Fin (R.image (parentLabel D a (2^b))).card) (i : Fin n)
    (hi : parentLabel D a (2^b) i = parentIndex (R.image (parentLabel D a (2^b))) j)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P = ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4 : ℝ)) :
    ‖quotientMap P hP ell hell hell4 hd M
        (horizontalSlope ((fullSource h R a level b E).line j)) -
      quotientMap P hP ell hell hell4 hd M (horizontalSlope (D.line i))‖ ≤
      6 / ((2^b : ℕ) : ℝ) := by
  have hg := full_horizontal_distance h R a level b E j i hi
  rw [dist_eq_norm] at hg
  rw [← map_sub]
  have hq := quotient_norm_le P hP ell hell hell4 hd M hM
    (horizontalSlope ((fullSource h R a level b E).line j) - horizontalSlope (D.line i))
  calc
    _ ≤ 2 * ‖horizontalSlope ((fullSource h R a level b E).line j) - horizontalSlope (D.line i)‖ := hq
    _ ≤ 2 * (3 / ((2^b : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = _ := by ring

/-- The full-family index is the literal equivFin label used by fullIndex.
Its parent readback is proved here, so the old tube alone supplies the
representative identity needed by full_quotient_drift. -/
theorem indexed_quotient_drift {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (level b : ℕ)
    (E : Finset (Fin n × Index)) (i : Fin n)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P = ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4 : ℝ)) :
    let parents := (univ : Finset (Fin n)).image (parentLabel D 0 (2^b))
    let j := parents.equivFin ⟨parentLabel D 0 (2^b) i, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩
    ‖quotientMap P hP ell hell hell4 hd M
        (horizontalSlope ((fullSource h univ 0 level b E).line j)) -
      quotientMap P hP ell hell hell4 hd M (horizontalSlope (D.line i))‖ ≤
      (3/32 : ℝ) * (64 / ((2^b : ℕ) : ℝ)) := by
  intro parents j
  have hi : parentLabel D 0 (2^b) i = parentIndex parents j := by
    simp only [j, parentIndex, Equiv.symm_apply_apply]
  have hh := full_quotient_drift h univ 0 level b E j i hi P hP ell hell hell4 hd M hM
  calc
    _ ≤ 6 / ((2^b : ℕ) : ℝ) := hh
    _ = _ := by ring

/-- Actual same-E1-source reader for the merged-point residual. Its old
value is the original localHorizontalSlope in the already selected native
frame, and its new value is the unchanged full-backbone representative. -/
theorem same_reference_quotient_drift {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (level b : ℕ)
    (selected : Finset (Fin (parentLabels D R a (2^m) p).card × Index))
    (i : Fin (parentLabels D R a (2^m) p).card)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P = ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4 : ℝ)) :
    let S := source h R Eref a m p
    let parents := (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image (parentLabel S 0 (2^b))
    let j := parents.equivFin ⟨parentLabel S 0 (2^b) i, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩
    ‖quotientMap P hP ell hell hell4 hd M
        (horizontalSlope ((fullSource hReferenceNative univ 0 level b selected).line j)) -
      quotientMap P hP ell hell hell4 hd M
        (localHorizontalSlope D (2^m) p
          (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))‖ ≤
      (3/32 : ℝ) * (64 / ((2^b : ℕ) : ℝ)) := by
  intro S parents j
  have hh := indexed_quotient_drift hReferenceNative level b selected i P hP ell hell hell4 hd M hM
  rwa [local_horizontal_readback] at hh

end NativeFullReferenceQuotientDrift
