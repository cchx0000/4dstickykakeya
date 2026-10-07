import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_maps
import Theorems.Thm_StickyKakeya4_native_reference_configured_time
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge
import Theorems.Thm_StickyKakeya4_native_packed_frame_isometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeActualConfiguredPoint
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints
open CanonicalConfiguredE4Bridge CanonicalConfiguredPointRounding CanonicalGridRecoding
open NativePackedFrameIsometry

lemma assemble_height (s : Split) (x : Fin (tangentDim s) → ℝ)
    (y : Fin (normalDim s) → ℝ) (t : ℝ) : assemble s x y t (3 : Fin 4) = t := by
  cases s <;> rfl

lemma assemble_spatial (s : Split) (x : Fin (tangentDim s) → ℝ)
    (y : Fin (normalDim s) → ℝ) (t t' : ℝ) (j : Fin 4) (hj : j ≠ 3) :
    assemble s x y t j = assemble s x y t' j := by
  cases s <;> fin_cases j <;> simp_all [assemble]

/-- The one configured E4 realization used by the source consumers. Both
matrix fields are functions of the literal old/coarse height labels. The
height uses translatedHeight/(8R), and the whole point receives /512. -/
def graphGrid (s : Split) (mu : ℝ) (R : ℕ)
    (Fold Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) : E4 :=
  (1 / 512 : ℝ) • assemble s
    (coarseX mu R z.2.1)
    (configuredNormal mu R (Fold z.1) (Fcfg (z.1 / ((8 * R : ℕ) : ℤ))) z.2.1 z.2.2)
    ((mu * (R : ℝ)) * (((z.1 / ((8 * R : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2))

/-- Literal actual pxy labels for the two ranks, with no independently
chosen grid or point representatives. -/
def sourceLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (k : Index) :
    Label ℤ (tangentDim s) (normalDim s) := by
  cases s with
  | oneTwo => exact NativeReferenceXYGridMaps.pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F k
  | twoOne => exact NativeReferenceXYGridMaps.pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F k

def point {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (R : ℕ) (k : Index) : E4 :=
  graphGrid s (mu m) R F Fcfg (sourceLabel D a m p s P hP hd F k)

theorem point_factorization {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (R : ℕ) :
    point D a m p s P hP hd F Fcfg R =
      graphGrid s (mu m) R F Fcfg ∘ sourceLabel D a m p s P hP hd F := rfl

lemma sourceLabel_oneTwo {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 1)
    (F : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (k : Index) :
    sourceLabel D a m p .oneTwo P hP hd F k =
      NativeReferenceXYGridMaps.pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F k := rfl

lemma sourceLabel_twoOne {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (F : ℤ → Matrix (Fin 1) (Fin 2) ℝ) (k : Index) :
    sourceLabel D a m p .twoOne P hP hd F k =
      NativeReferenceXYGridMaps.pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F k := rfl

lemma sourceLabel_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (k : Index) :
    (sourceLabel D a m p s P hP hd F k).1 = NativeTranslatedGrainHeightOverlap.translatedHeight D a m k := by
  cases s <;> rfl

lemma graphGrid_height (s : Split) (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) :
    graphGrid s mu R F Fcfg z (3 : Fin 4) =
      NativeConfiguredTimeCoarsening.finalTime (mu * (R : ℝ)) (z.1 / ((8 * R : ℕ) : ℤ)) := by
  cases s <;>
    simp only [graphGrid, assemble, PiLp.smul_apply, smul_eq_mul,
      NativeConfiguredTimeCoarsening.finalTime] <;> ring

/-- The physical time readback is expressed using the original reference
height, not the raw phase height or rawPoint's time. -/
theorem point_height_floor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (hR : 0 < R) (k : Index) (rhoFinal : ℝ) (J : ℕ)
    (hscale : 512 * rhoFinal = (mu m * (R : ℝ)) * (J : ℝ)) :
    ⌊point D a m p s P hP hd F Fcfg R k (3 : Fin 4) / rhoFinal⌋ =
      ⌊oldPoint D a m p k (3 : Fin 4) / (512 * rhoFinal)⌋ := by
  rw [point, graphGrid_height, sourceLabel_height]
  exact NativeReferenceConfiguredTime.final_height_floor D a m p R hR k rhoFinal J hscale

/-- The actual pxy horizontal labels are precisely the fine grid of the
packed native frame and its actual old-field quotient. -/
lemma sourceLabel_coordinates {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (k : Index) :
    let v := frame s P hP hd (rawPoint D a m p k)
    let z := sourceLabel D a m p s P hP hd F k
    z.2.1 = grid (mu m) (tangent s v) ∧
      z.2.2 = grid (mu m) (quotient (F z.1) (tangent s v) (normal s v)) := by
  cases s <;> constructor <;> ext j <;> fin_cases j
  all_goals
    first
    | rfl
    | simp [sourceLabel, NativeReferenceXYGridMaps.pxy, NativeGrainQuotientBins.label,
        frame_apply_oneTwo, frame_apply_twoOne, tangent, normal, assemble, grid, quotient,
        NativeReferenceXYGridLinear.quotientMap, LinearMap.sub_apply, LinearMap.comp_apply,
        Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, PiLp.sub_apply,
        Fin.sum_univ_one, Fin.sum_univ_two]

/-- Spatial recoding and the separately read actual height coordinate give
the same C=3 E4 estimate. All grid labels are literal inputs to graphGrid. -/
theorem graphGrid_distance (s : Split) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (z : Label ℤ (tangentDim s) (normalDim s)) (v : E4)
    (hOld : ∀ i j, |F z.1 i j| ≤ 1 / 4)
    (hCfg : ∀ i j, |Fcfg (z.1 / ((8 * R : ℕ) : ℤ)) i j| ≤ 1 / 4)
    (hX : z.2.1 = grid mu (tangent s v))
    (hY : z.2.2 = grid mu (quotient (F z.1) (tangent s v) (normal s v)))
    (hTime : |(mu * (R : ℝ)) * (((z.1 / ((8 * R : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2) -
      v (3 : Fin 4)| ≤ (3 / 2 : ℝ) * (mu * (R : ℝ))) :
    dist (graphGrid s mu R F Fcfg z) ((1 / 512 : ℝ) • v) ≤ 3 * ((mu * (R : ℝ)) / 512) := by
  let w := assemble s (coarseX mu R z.2.1)
    (configuredNormal mu R (F z.1) (Fcfg (z.1 / ((8 * R : ℕ) : ℤ))) z.2.1 z.2.2)
    ((mu * (R : ℝ)) * (((z.1 / ((8 * R : ℕ) : ℤ) : ℤ) : ℝ) + 1 / 2))
  have hgeneric := configured_coordinate_error s mu R hmu hR
    (F z.1) (Fcfg (z.1 / ((8 * R : ℕ) : ℤ))) hOld hCfg v
  have hcoords (j : Fin 4) : |w j - v j| ≤ (3 / 2 : ℝ) * (mu * (R : ℝ)) := by
    by_cases hj : j = 3
    · subst j
      simpa only [w, assemble_height] using hTime
    · have he : w j = configuredChart s mu R (F z.1) (Fcfg (z.1 / ((8 * R : ℕ) : ℤ))) v j := by
        dsimp only [w, configuredChart]
        rw [hX, hY]
        exact assemble_spatial _ _ _ _ _ j hj
      rw [he]
      exact hgeneric j
  have hdist := dist_le_three_of_coordinate_error (mu * (R : ℝ))
    (mul_pos hmu (by exact_mod_cast hR)).le w v hcoords
  change dist ((1 / 512 : ℝ) • w) ((1 / 512 : ℝ) • v) ≤ _
  rw [dist_smul₀]
  norm_num
  nlinarith only [hdist]

/-- The corrected configured point is close to the SAME rawPoint in its
proved native isometric frame, including the actual translated time label.
No rounding or coordinate-map certificate is a premise of this reader. -/
theorem point_distance {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t i j, |F t i j| ≤ 1 / 4) (hCfg : ∀ t i j, |Fcfg t i j| ≤ 1 / 4)
    (R : ℕ) (hR : 0 < R) (k : Index) (hbase : rho m ≤ mu m * (R : ℝ)) :
    dist (point D a m p s P hP hd F Fcfg R k)
      (frame s P hP hd ((1 / 512 : ℝ) • rawPoint D a m p k)) ≤ 3 * ((mu m * (R : ℝ)) / 512) := by
  have hlabels := sourceLabel_coordinates D a m p s P hP hd F k
  have htime := NativeReferenceConfiguredTime.coarse_height_coordinate_budget D a m hm p R hR k hbase
  rw [map_smul]
  apply graphGrid_distance s (mu m) R (mu_pos m) hR F Fcfg
    (sourceLabel D a m p s P hP hd F k) (frame s P hP hd (rawPoint D a m p k))
    (hF _) (hCfg _) hlabels.1 hlabels.2
  simpa only [sourceLabel_height, frame_height] using htime

end NativeActualConfiguredPoint
