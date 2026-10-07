import Theorems.Thm_StickyKakeya4_native_local_parent_cells
import Theorems.Thm_StickyKakeya4_native_actual_configured_height_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRememberedHeightGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentCells
open CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice NativeActualConfiguredPoint

/-- Input physical-time origin of one literal local-source cell bin. -/
def binOrigin {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (z : ℤ) : ℝ :=
  mesh D * ((shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ))

/-- Read the actual local-source time label. Its inverse input-time interval
has length256 times the local output thickness, including negative bins. -/
theorem input_center_interval {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (k : Index) (z : ℤ)
    (hz : cellLabel D a N p i k (3 : Fin 4) = z) :
    binOrigin D a N z ≤ cellCenter (mesh D) k (3 : Fin 4) ∧
      cellCenter (mesh D) k (3 : Fin 4) ≤
        binOrigin D a N z + 256 * ((N : ℝ) * D.thickness / 64) := by
  rw [cellLabel_height hd a N hN p i k] at hz
  let t : ℤ := k (3 : Fin 4) - shift D a
  let M : ℤ := (8 * N : ℕ)
  have hM : 0 < M := by dsimp [M]; positivity
  have he := Int.emod_add_mul_ediv t M
  have hrem := Int.emod_nonneg t hM.ne'
  have hremUpper := Int.emod_lt_of_pos t hM
  have hdiv : t / M = z := hz
  rw [hdiv] at he
  have hlo : M * z ≤ t := by omega
  have hhi : t + 1 ≤ M * z + M := by omega
  dsimp [t, M] at hlo hhi
  have hloR : (shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ) ≤
      (k (3 : Fin 4) : ℝ) := by
    have hh : (8 * (N : ℝ)) * (z : ℝ) ≤
        (k (3 : Fin 4) : ℝ) - (shift D a : ℝ) := by
      exact_mod_cast hlo
    linarith
  have hhiR : (k (3 : Fin 4) : ℝ) + 1 ≤
      (shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ) + 8 * (N : ℝ) := by
    have hh : (k (3 : Fin 4) : ℝ) - (shift D a : ℝ) + 1 ≤
        (8 * (N : ℝ)) * (z : ℝ) + 8 * (N : ℝ) := by
      exact_mod_cast hhi
    linarith
  have hm : 0 ≤ mesh D := by dsimp [mesh]; positivity
  change mesh D * ((shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ)) ≤
      mesh D * ((k (3 : Fin 4) : ℝ) + 1 / 2) ∧
    mesh D * ((k (3 : Fin 4) : ℝ) + 1 / 2) ≤ _
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith only [hloR]) hm
  · have hh := mul_le_mul_of_nonneg_left
      (show (k (3 : Fin 4) : ℝ) + 1 / 2 ≤
        (shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ) + 8 * (N : ℝ) by
          linarith only [hhiR]) hm
    calc
      _ ≤ mesh D * ((shift D a : ℝ) + 8 * (N : ℝ) * (z : ℝ) + 8 * (N : ℝ)) := hh
      _ = binOrigin D a N z + 256 * ((N : ℝ) * D.thickness / 64) := by
        dsimp [binOrigin, mesh]
        ring

/-- The old configured height is retained as a real coordinate. A genuine
2d shadow-center error enlarges the actual interval by at most4sigma. -/
theorem old_height_interval {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (k : Index) (z : ℤ) (x : E4)
    (hz : cellLabel D a N p i k (3 : Fin 4) = z)
    (hnear : |x (3 : Fin 4) - cellCenter (mesh D) k (3 : Fin 4)| ≤ 2 * D.thickness)
    (hscale : D.thickness ≤ (N : ℝ) * D.thickness / 64) :
    binOrigin D a N z - 2 * D.thickness ≤ x (3 : Fin 4) ∧
      x (3 : Fin 4) ≤ binOrigin D a N z - 2 * D.thickness +
        260 * ((N : ℝ) * D.thickness / 64) := by
  have hi := input_center_interval D hd a N hN p i k z hz
  have hn := abs_le.mp hnear
  constructor <;> linarith only [hi.1, hi.2, hn.1, hn.2, hscale]

/-- Count genuine old configured heights in one actual output bin, rather
than replacing their labels by already-coarsened input cell times. The old
height lattice is derived from the original configured-point construction. -/
theorem actual_old_heights_per_bin {n nC : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hdim : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R0 : ℕ) (hR0 : 0 < R0) (eps : ℝ) (heps : 0 < eps)
    (hmesh : NativeReferenceXYGridPoints.mu m * (R0 : ℝ) = 64 * eps)
    (C : FiniteScaleSource nC) (hC : 0 < C.thickness)
    (N : ℕ) (hN : 0 < N) (q : Parent) (z : ℤ)
    (S : Finset Index) (oldCell : Index → Index) (oldTube : Index → Fin nC)
    (hbin : ∀ k ∈ S, cellLabel C 0 N q (oldTube k) (oldCell k) (3 : Fin 4) = z)
    (hnear : ∀ k ∈ S,
      |point D a m p s P hP hdim F Fcfg R0 k (3 : Fin 4) -
        cellCenter (mesh C) (oldCell k) (3 : Fin 4)| ≤ 2 * C.thickness)
    (hdscale : C.thickness ≤ (N : ℝ) * C.thickness / 64)
    (hepsScale : eps ≤ (N : ℝ) * C.thickness / 64) :
    ((S.image (fun k => point D a m p s P hP hdim F Fcfg R0 k (3 : Fin 4))).card : ℝ) ≤
      4096 * (((N : ℝ) * C.thickness / 64) / eps) := by
  let sigma : ℝ := (N : ℝ) * C.thickness / 64
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  let c := binOrigin C 0 N z - 2 * C.thickness
  have hinterval : ∀ t ∈ S.image
      (fun k => point D a m p s P hP hdim F Fcfg R0 k (3 : Fin 4)),
      c ≤ t ∧ t ≤ c + 260 * sigma := by
    intro t ht
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
    exact old_height_interval C hC 0 N hN q (oldTube k) (oldCell k) z
      (point D a m p s P hP hdim F Fcfg R0 k) (hbin k hk) (hnear k hk) hdscale
  have hcap := NativeActualConfiguredHeightCaps.actual_height_interval_cap
    D a m p s P hP hdim F Fcfg R0 hR0 S c (260 * sigma) (by positivity)
  rw [filter_eq_self.mpr hinterval, hmesh] at hcap
  have hratio : 1 ≤ sigma / eps := (le_div_iff₀ heps).mpr (by simpa using hepsScale)
  have he : (260 * sigma) / (64 * eps / 512) + 2 = 2080 * (sigma / eps) + 2 := by
    field_simp
    ring
  rw [he] at hcap
  change _ ≤ 4096 * (sigma / eps)
  linarith only [hcap, hratio]

end NativeRememberedHeightGeometry
