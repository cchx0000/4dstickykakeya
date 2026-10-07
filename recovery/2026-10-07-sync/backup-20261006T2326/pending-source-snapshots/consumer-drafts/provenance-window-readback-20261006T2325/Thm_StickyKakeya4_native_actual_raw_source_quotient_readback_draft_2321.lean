import Theorems.Thm_StickyKakeya4_native_actual_raw_source_slope_readback_draft_2317
import Theorems.Thm_StickyKakeya4_native_actual_reference_one_T_geometry
import Theorems.Thm_StickyKakeya4_native_raw_same_point_old_cell_menu_draft_2300

/- Originally drafted without verification; consult current receipts.
The source is the literal two-stage source. The original point witness,
raw field and xi are unchanged. Representative rounding is paid separately
from the actual old affine residual. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualRawSourceQuotientReadbackDraft2321
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeRelativeParentLabels
open NativeNormalizedParentCarrierMetric NativeIncidentAffineAnchorGeometry
open NativeReferenceXYGridLinear NativeTranslatedGrainHeightOverlap
open NativeHorizontalGrainSlice NativeActualRawSourceSlopeReadbackDraft2317
open NativeRawHeightSourceAdapter NativeRememberedSourceMaps NativeLocalCellCoherence
open NativeRawSamePointOldCellMenuDraft2300
open scoped BigOperators Matrix.Norms.Elementwise

/-- Evaluate the original raw-height label on a true original k3 value. -/
def rawHeightFromInteger {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (t : ℤ) : ℤ :=
  ⌊(mesh D*((t:ℝ)+1/2))/(64/((2^m:ℕ):ℝ))⌋

theorem rawHeight_eq_integer {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (k : Index) :
    rawHeight D m k=rawHeightFromInteger D m (k 3) := rfl

/-- Choose from the retained RAW tag table, not from translated tags or
from all antecedents of an intermediate point. -/
def chosenOriginalHeight {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index))) (t : ℤ) : ℤ :=
  if ht : ∃v∈B,finalTime v=t then (Classical.choose ht).1 else 0

theorem chosenOriginalHeight_readback {nA : ℕ}
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (v : ℤ × (Fin nA × Index)) (hv : v∈B) :
    chosenOriginalHeight B (finalTime v)=v.1 := by
  have ht : ∃w∈B,finalTime w=finalTime v := ⟨v,hv,rfl⟩
  simp only [chosenOriginalHeight,dif_pos ht]
  exact hB (Classical.choose ht) (Classical.choose_spec ht).1 v hv (Classical.choose_spec ht).2

/-- One matrix field on the final native height labels, using exactly the
original f and the chosen true old height. -/
def sourceField {n nA : ℕ} {X : Type*} (D : FiniteScaleSource n) (m : ℕ)
    (B : Finset (ℤ × (Fin nA × Index))) (f : ℤ → X) (t : ℤ) : X :=
  f (rawHeightFromInteger D m (chosenOriginalHeight B t))

/-- Every actual retained raw witness at this final cell uses the same
source field value. This also applies to different cells with equal final
time, without requiring the original f to be globally Lipschitz. -/
theorem sourceField_on_raw_witness {n nA : ℕ} {X : Type*}
    (D : FiniteScaleSource n) (m : ℕ) (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (Occ : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (f : ℤ → X) (k : Index) (z : (Fin nA × Index) × (Fin n × Index))
    (hz : z∈rawCellWitnesses C c pA Occ B k) :
    sourceField D m B f (k 3)=f (rawHeight D m z.2.2) := by
  obtain ⟨hzRaw,hzCell,_hzParent⟩ := mem_filter.mp hz
  have htag := (mem_filter.mp hzRaw).2
  have htime : finalTime (rawTaggedKey C c pA z)=k 3 := congrFun hzCell 3
  have hread := chosenOriginalHeight_readback B hB (rawTaggedKey C c pA z) htag
  rw [htime] at hread
  change chosenOriginalHeight B (k 3)=z.2.2 3 at hread
  simp only [sourceField,hread,rawHeight_eq_integer]

/-- The actual parent slope translation, embedded in the horizontal plane. -/
def parentSlope (p : Parent) : E4 :=
  ActualSlopeSource.heightPoint (WithLp.toLp 2 (fun j => (p.1 j:ℝ))) 0

/-- Three coordinate errors give an ambient horizontal error, with no
unit-direction or angular-metric identification. -/
theorem horizontal_error_norm (u v : E3) (N sigma : ℝ) (p : Parent)
    (hcoord : ∀j : Fin 3,|v j-(N*u j-(p.1 j:ℝ))| ≤ sigma) :
    ‖ActualSlopeSource.heightPoint v 0-
      (N • ActualSlopeSource.heightPoint u 0-parentSlope p)‖ ≤ 3*sigma := by
  have hn := euclidean_norm_le_sum
    (ActualSlopeSource.heightPoint v 0-
      (N • ActualSlopeSource.heightPoint u 0-parentSlope p))
  rw [Fin.sum_univ_castSucc] at hn
  simp only [parentSlope,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    ActualSlopeSource.heightPoint_castSucc,ActualSlopeSource.heightPoint_last,
    mul_zero,sub_self,sub_zero,abs_zero,add_zero,Fin.sum_univ_three] at hn
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  linarith

/-- The exact transformed offset is N*xi minus the quotient of the fixed
parent slope. The old affine error and source-representative error are
both retained, in the same matrix and coordinate bases. -/
theorem quotient_residual_of_slope_error (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1≤ell) (hell4 : ell≤4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖≤(1/4:ℝ))
    (u v : E3) (xi : EuclideanSpace ℝ (Fin (4-ell))) (N error sigma : ℝ)
    (hN : 0≤N) (p : Parent)
    (hres : ‖quotientMap P hP ell hell hell4 hd M (ActualSlopeSource.heightPoint u 0)-xi‖≤error)
    (hcoord : ∀j : Fin 3,|v j-(N*u j-(p.1 j:ℝ))|≤sigma) :
    ‖quotientMap P hP ell hell hell4 hd M (ActualSlopeSource.heightPoint v 0)-
      (N • xi-quotientMap P hP ell hell hell4 hd M (parentSlope p))‖≤
        N*error+6*sigma := by
  let Q := quotientMap P hP ell hell hell4 hd M
  have heq : Q (ActualSlopeSource.heightPoint v 0)-(N • xi-Q (parentSlope p))=
      Q (ActualSlopeSource.heightPoint v 0-
        (N • ActualSlopeSource.heightPoint u 0-parentSlope p))+
      N • (Q (ActualSlopeSource.heightPoint u 0)-xi) := by
    simp only [map_sub,map_smul,smul_sub]
    abel
  change ‖Q (ActualSlopeSource.heightPoint v 0)-(N • xi-Q (parentSlope p))‖≤_
  rw [heq]
  have hround := (quotient_norm_le P hP ell hell hell4 hd M hM
    (ActualSlopeSource.heightPoint v 0-
      (N • ActualSlopeSource.heightPoint u 0-parentSlope p))).trans
      (mul_le_mul_of_nonneg_left (horizontal_error_norm u v N sigma p hcoord) (by norm_num))
  have hscale : ‖N • (Q (ActualSlopeSource.heightPoint u 0)-xi)‖≤N*error := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hN]
    exact mul_le_mul_of_nonneg_left hres hN
  have hh := norm_add_le
    (Q (ActualSlopeSource.heightPoint v 0-
      (N • ActualSlopeSource.heightPoint u 0-parentSlope p)))
    (N • (Q (ActualSlopeSource.heightPoint u 0)-xi))
  dsimp only [Q] at hh ⊢
  linarith

/-- The literal source line has the transformed old offset, using the same
original incidence and the same matrix value. hRep and hPhase are actual
same-Q/occurrence fields, not representative-equality assumptions. -/
theorem actual_final_quotient_error {n : ℕ} {D : FiniteScaleSource n}
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
    (Efinal : Finset (Fin Q.card × Index)) (etaC : ℝ)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1≤ell) (hell4 : ell≤4) (hd : Module.finrank ℝ P=ell-1)
    (f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (oldTube : Fin n) (k : Index)
    (hf : ‖f (rawHeight D m k)‖≤(1/4:ℝ)) (error : ℝ)
    (hres : ‖quotientMap P hP ell hell hell4 hd (f (rawHeight D m k))
      (localHorizontalSlope D (2^m) p oldTube)-xi k‖≤error) :
    let C := NativeCoarseCellSource.source hRef 0 levelRef b Q rep ECoarse hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
      ∀i : Fin (parentLabels C R 0 (2^c) pA).card,
        NativeCoarseCellSource.parentIndex Q
          (NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i)=
            relativeLabel D a (2^m) p (2^b) oldTube →
        ‖quotientMap P hP ell hell hell4 hd (f (rawHeight D m k))
            (ActualSlopeSource.heightPoint
              (WithLp.toLp 2 (slope ((source hC R Efinal 0 c pA).line i))) 0)-
          (((2^c:ℕ):ℝ) • xi k-
            quotientMap P hP ell hell hell4 hd (f (rawHeight D m k)) (parentSlope pA))‖≤
          ((2^c:ℕ):ℝ)*error+6*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64) := by
  intro C hC i hPhase
  exact quotient_residual_of_slope_error P hP ell hell hell4 hd _ hf
    (NativeLocalParentGeometry.localSlope D (2^m) p oldTube)
    (WithLp.toLp 2 (slope ((source hC R Efinal 0 c pA).line i)))
    (xi k) ((2^c:ℕ):ℝ) error
    (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64) (by positivity) pA hres
    (actual_final_slope_error h backbone Eref a m p hRef levelRef b Q rep ECoarse hsep hRep
      c pA R Efinal etaC hC i oldTube hPhase)

/-- The old residual is read from the checked strengthened one-T output
on the SAME original incidence. No new residual bound is an input. -/
theorem actual_one_T_quotient_error {n : ℕ} {D : FiniteScaleSource n}
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
    (Efinal : Finset (Fin Q.card × Index)) (etaC : ℝ)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=1)
    (f : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin 2)) (oldTube : Fin n) (k : Index)
    (hf : ‖f (rawHeight D m k)‖≤(1/4:ℝ))
    (r epsilonGraph : ℝ) (T : Finset (Fin n × Index))
    (H : NativeActualReferenceOneTGeometry.HasFinalGeometry D m p P hP hd f xi r epsilonGraph T)
    (hk : (oldTube,k)∈T) :
    let C := NativeCoarseCellSource.source hRef 0 levelRef b Q rep ECoarse hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
      ∀i : Fin (parentLabels C R 0 (2^c) pA).card,
        NativeCoarseCellSource.parentIndex Q
          (NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i)=
            relativeLabel D a (2^m) p (2^b) oldTube →
        ‖quotientMap P hP 2 (by norm_num) (by norm_num) hd (f (rawHeight D m k))
            (ActualSlopeSource.heightPoint
              (WithLp.toLp 2 (slope ((source hC R Efinal 0 c pA).line i))) 0)-
          (((2^c:ℕ):ℝ) • xi k-
            quotientMap P hP 2 (by norm_num) (by norm_num) hd (f (rawHeight D m k)) (parentSlope pA))‖≤
          ((2^c:ℕ):ℝ)*((5/4:ℝ)*(rho m)^(1-2*epsilonGraph))+6*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64) := by
  intro C hC i hPhase
  exact actual_final_quotient_error h backbone Eref a m p hRef levelRef b Q rep ECoarse hsep hRep
    c pA R Efinal etaC P hP 2 (by norm_num) (by norm_num) hd f xi oldTube k hf
    ((5/4:ℝ)*(rho m)^(1-2*epsilonGraph)) (H.2 (oldTube,k) hk) hC i hPhase

/-- The actual old error is bounded by 64*d, not by d. Its dilation
contributes4096*sigma; the representative rounding contributes6*sigma. -/
theorem error_budget {N error d sigma : ℝ} (hN : 0≤N)
    (herror : error≤64*d) (hscale : N*d=64*sigma) :
    N*error+6*sigma≤4102*sigma := by
  have hh := mul_le_mul_of_nonneg_left herror hN
  nlinarith only [hh,hscale]

end NativeActualRawSourceQuotientReadbackDraft2321
