import Theorems.Thm_StickyKakeya4_native_raw_height_source_adapter
import Theorems.Thm_StickyKakeya4_native_coarse_source_parent_readback

/- UNVERIFIED actual graph-slope readback through the two source
constructors. The coarse source is literally constructed on its actual
representative lines. An arbitrary native C cannot replace this datum.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualRawSourceSlopeReadbackDraft2317
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeRelativeParentLabels
open NativeNormalizedParentCarrierMetric

/-- Zero-parent contraction leaves the actual graph slope unchanged. -/
theorem coarse_source_slope {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction (D.line (rep q))) (direction (D.line (rep q'))))
    (i : Fin Q.card) (v : Fin 3) :
    slope ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i) v=
      slope (D.line (rep (NativeCoarseCellSource.parentIndex Q i))) v := by
  rw [NativeCoarseCellSource.source_line]
  unfold slope
  rw [NativeCoarseRepresentativeGeometry.direction_zero_parent h a]

/-- The representative-parent identity is an actual output of the same-Q
source producer. The phase identity is an actual occurrence field. Their
slope floors give d/64 error, and the final literal parent dilation turns
it into exactly sigma. No direction or plane certificate is assumed. -/
theorem actual_final_slope_error {n : ℕ} {D : FiniteScaleSource n}
    {eta etaRef : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (backbone : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (source h backbone Eref a m p) etaRef)
    (levelRef b : ℕ) (Q : Finset Parent)
    (rep : Parent → Fin (parentLabels D backbone a (2^m) p).card)
    (ECoarse : Finset (Fin (parentLabels D backbone a (2^m) p).card × Index))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h backbone Eref a m p).line (rep q)))
        (direction ((source h backbone Eref a m p).line (rep q'))))
    (hRep : ∀q∈Q,parentLabel (source h backbone Eref a m p) 0 (2^b) (rep q)=q)
    (c : ℕ) (pA : Parent) (R : Finset (Fin Q.card))
    (Efinal : Finset (Fin Q.card × Index)) (etaC : ℝ) :
    let C := NativeCoarseCellSource.source hRef 0 levelRef b Q rep ECoarse hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
      ∀i : Fin (parentLabels C R 0 (2^c) pA).card,∀oldTube : Fin n,
        NativeCoarseCellSource.parentIndex Q
          (NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i)=
            relativeLabel D a (2^m) p (2^b) oldTube →
        ∀v : Fin 3,
          |slope ((source hC R Efinal 0 c pA).line i) v-
            (((2^c:ℕ):ℝ)*NativeLocalParentGeometry.localSlope D (2^m) p oldTube v-(pA.1 v:ℝ))| ≤
            ((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64 := by
  intro C hC i oldTube hPhase v
  let j := NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i
  have hParent := hRep (NativeCoarseCellSource.parentIndex Q j)
    (NativeCoarseCellSource.parentIndex_mem Q j)
  have hFloor : ⌊((2^b:ℕ):ℝ)*slope (C.line j) v⌋=
      ⌊((2^b:ℕ):ℝ)*NativeLocalParentGeometry.localSlope D (2^m) p oldTube v⌋ := by
    rw [coarse_source_slope hRef 0 levelRef b Q rep ECoarse hsep j v]
    have hh := congrFun (congrArg Prod.fst (hParent.trans hPhase)) v
    change ⌊((2^b:ℕ):ℝ)*slope ((source h backbone Eref a m p).line
        (rep (NativeCoarseCellSource.parentIndex Q j))) v⌋=
      ⌊((2^b:ℕ):ℝ)*slope (NativeLocalParentGeometry.line D a (2^m) p oldTube) v⌋ at hh
    rw [NativeLocalParentGeometry.slope_line] at hh
    exact hh
  have hClose := same_floor_mul_close
    (slope (C.line j) v) (NativeLocalParentGeometry.localSlope D (2^m) p oldTube v)
    (2^b) (by positivity) hFloor
  rw [NativeLocalParentSource.source_line,NativeLocalParentGeometry.slope_line]
  change |(((2^c:ℕ):ℝ)*slope (C.line j) v-(pA.1 v:ℝ))-
      (((2^c:ℕ):ℝ)*NativeLocalParentGeometry.localSlope D (2^m) p oldTube v-(pA.1 v:ℝ))| ≤ _
  rw [sub_sub_sub_cancel_right,←mul_sub,abs_mul,abs_of_pos (by positivity : (0:ℝ)<((2^c:ℕ):ℝ))]
  exact (mul_le_mul_of_nonneg_left hClose (by positivity)).trans_eq (by ring)

end NativeActualRawSourceSlopeReadbackDraft2317
