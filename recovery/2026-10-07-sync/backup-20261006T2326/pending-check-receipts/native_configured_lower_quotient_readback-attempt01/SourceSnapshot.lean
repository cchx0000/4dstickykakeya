import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers

/- UNVERIFIED actual configured lower-quotient readback. The height in
coarseYKey remains its coarse integer height; it is not the old translated
height. No field regularity, field freeze, or alignment-ball input is used. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeConfiguredLowerQuotientReadback
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge CanonicalGridRecoding
open NativeActualConfiguredPoint NativeConfiguredThirdRelation NativeReferenceXYGridPoints
open CanonicalConfiguredPointRounding NativeTranslatedGrainHeightOverlap
open scoped BigOperators

/-- The literal rank-two quotient in the already packed E4 chart. -/
def lowerQuotient (F : Matrix (Fin 2) (Fin 1) ℝ) (x : E4) : Fin 2 → ℝ :=
  fun j => x j.castSucc.succ-F j 0*x 0

/-- Exact cancellation in the configured graph, including its physical
/512 contraction and the actual recoded normal key. -/
theorem graphGrid_quotient (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (z : Label ℤ 1 2) :
    lowerQuotient (Fcfg (z.1/((8*R:ℕ):ℤ))) (graphGrid .oneTwo mu R F Fcfg z) =
      NativeQuotientGridCenters.center (mu*(R:ℝ)/512)
        (newY mu R (fun t : ℤ => t/((8*R:ℕ):ℤ)) F Fcfg z).2 := by
  funext j
  fin_cases j <;>
    simp [lowerQuotient,graphGrid,assemble,configuredNormal,graphPoint,
      NativeQuotientGridCenters.center,CanonicalGridRecoding.center,newY,errorMatrix] <;> ring

/-- The actual source key's first coordinate is precisely the coarse
translated-height label. The converse needs the separately supplied Hsingle. -/
lemma coarse_height_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P=1) (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (R : ℕ) (k : Index) :
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1 =
      translatedHeight D a m k/((8*R:ℕ):ℤ) := by
  simp only [coarseYKey,newY,sourceLabel_height]

/-- This is exactly the Y point passed to the first planar alignment. -/
theorem point_quotient_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P=1) (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (R : ℕ) (k : Index) :
    lowerQuotient (Fcfg (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1)
        (point D a m p .oneTwo P hP hd F Fcfg R k) =
      NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2 :=
  graphGrid_quotient (mu m) R F Fcfg (sourceLabel D a m p .oneTwo P hP hd F k)

/-- One tangent coordinate and the actual matrix entry bound give the
5/4 Lipschitz constant from E4 to the planar sup metric. -/
theorem lowerQuotient_dist (F : Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀j,|F j 0| ≤ 1/4) (x y : E4) :
    dist (lowerQuotient F x) (lowerQuotient F y) ≤ (5/4:ℝ)*dist x y := by
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ (5/4:ℝ)*dist x y)).mpr
  intro j
  have hn : |x j.castSucc.succ-y j.castSucc.succ| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y j.castSucc.succ
  have hx : |x 0-y 0| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y (0:Fin 4)
  have he : lowerQuotient F x j-lowerQuotient F y j =
      (x j.castSucc.succ-y j.castSucc.succ)-F j 0*(x 0-y 0) := by
    dsimp only [lowerQuotient]
    ring
  rw [Real.dist_eq,he]
  calc
    _ ≤ |x j.castSucc.succ-y j.castSucc.succ|+|F j 0*(x 0-y 0)| := abs_sub _ _
    _ ≤ dist x y+(1/4:ℝ)*dist x y := by
      rw [abs_mul]
      exact add_le_add hn (mul_le_mul (hF j) hx (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Equal coarse heights suffice; no converse from coarse to old height
is smuggled into this statement. -/
theorem key_center_dist_of_same_coarse_height {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t j,|Fcfg t j 0| ≤ 1/4) (R : ℕ) (k l : Index)
    (hh : (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1 =
      (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).1) :
    dist (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2)
      (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).2) ≤
      (5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R k)
        (point D a m p .oneTwo P hP hd F Fcfg R l) := by
  rw [←point_quotient_readback D a m p P hP hd F Fcfg R k,
    ←point_quotient_readback D a m p P hP hd F Fcfg R l,hh]
  exact lowerQuotient_dist _ (hCfg _) _ _

/-- Equality of original translated heights implies the needed equality
of coarse heights directly; Hsingle is not needed in this direction. -/
theorem key_center_dist_of_same_old_height {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t j,|Fcfg t j 0| ≤ 1/4) (R : ℕ) (k l : Index)
    (hh : translatedHeight D a m k=translatedHeight D a m l) :
    dist (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2)
      (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).2) ≤
      (5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R k)
        (point D a m p .oneTwo P hP hd F Fcfg R l) := by
  apply key_center_dist_of_same_coarse_height D a m p P hP hd F Fcfg hCfg R k l
  rw [coarse_height_readback,coarse_height_readback,hh]

end NativeConfiguredLowerQuotientReadback
