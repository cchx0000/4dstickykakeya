import Theorems.Thm_StickyKakeya4_native_dyadic_coarse_normalization
import Theorems.Thm_StickyKakeya4_original_tube_slice_occupancy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeCoarsePhaseGeometry
open Classical NativeCoarseOriginalIncidences
variable {T : Type*}
def x (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : ShearBinFibers.Index) : ℝ :=
  (coordinates P R c).1 (0:Fin 3)
def y (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : ShearBinFibers.Index) : ℝ × ℝ :=
  ((coordinates P R c).1 (1:Fin 3),(coordinates P R c).1 (2:Fin 3))
/-- The phase embedding reads the actual normalized coarse grid center,
 with height first. It does not identify it with an old chart center. -/
theorem actual_phase_coordinate_readback (P : PhysicalRescalingIncidenceTransfer.Data T)
    (R : ℝ) (c : ShearBinFibers.Index) :
    OriginalTubeSliceOccupancy.coordinates (height P R) (x P R) (y P R) c 0=(coordinates P R c).2 ∧
      ∀ j : Fin 3, OriginalTubeSliceOccupancy.coordinates (height P R) (x P R) (y P R) c j.succ=
        (coordinates P R c).1 j := by
  constructor
  · rfl
  · intro j
    fin_cases j <;> rfl
/-- Distinct original coarse labels are separated at their ACTUAL mesh.
 This supplies the Euclidean separation needed by the literal macro theorem. -/
theorem actual_phase_separation (P : PhysicalRescalingIncidenceTransfer.Data T)
    {R : ℝ} (hm : 0 < P.σ/R) (c d : ShearBinFibers.Index) (hcd : c ≠ d) :
    P.σ/R ≤ dist (OriginalTubeSliceOccupancy.embedding (height P R) (x P R) (y P R) c)
      (OriginalTubeSliceOccupancy.embedding (height P R) (x P R) (y P R) d) := by
  let a := OriginalTubeSliceOccupancy.coordinates (height P R) (x P R) (y P R) c
  let b := OriginalTubeSliceOccupancy.coordinates (height P R) (x P R) (y P R) d
  by_cases ht : c.2=d.2
  · have hs : c.1 ≠ d.1 := by intro h; exact hcd (Prod.ext h ht)
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hs
    have hgap := NativeCoarseOriginalHeights.integer_center_gap hm (c.1 j) (d.1 j) hj
    have hbound := EuclideanAlignmentPatches.coordinate_dist_le a b j.succ
    have hec := (actual_phase_coordinate_readback P R c).2 j
    have hed := (actual_phase_coordinate_readback P R d).2 j
    change a j.succ=(coordinates P R c).1 j at hec
    change b j.succ=(coordinates P R d).1 j at hed
    rw [hec,hed] at hbound
    exact hgap.trans hbound
  · have hgap := NativeCoarseOriginalHeights.integer_center_gap hm c.2 d.2 ht
    have hbound := EuclideanAlignmentPatches.coordinate_dist_le a b 0
    have hec := (actual_phase_coordinate_readback P R c).1
    have hed := (actual_phase_coordinate_readback P R d).1
    change a 0=(coordinates P R c).2 at hec
    change b 0=(coordinates P R d).2 at hed
    rw [hec,hed] at hbound
    exact hgap.trans hbound
/-- Both scalar and transverse phase residuals come directly from the
 already proved three-coordinate physical residual on the SAME incidence. -/
theorem actual_phase_residual (P : PhysicalRescalingIncidenceTransfer.Data T)
    (R : ℝ) (c : ShearBinFibers.Index) (t : T) {error : ℝ}
    (hres : ∀ j, |(coordinates P R c).1 j-P.offset t j/R-P.slope t j*height P R c| ≤ error) :
    ‖OriginalWPhysicalDisplacement.incidenceResidual (height P R) (x P R)
      (fun s => P.offset s (0:Fin 3)/R) (fun s => P.slope s (0:Fin 3)) c t‖ ≤ error ∧
    ‖OriginalWPhysicalDisplacement.incidenceResidual (height P R) (y P R)
      (fun s => (P.offset s (1:Fin 3)/R,P.offset s (2:Fin 3)/R))
      (fun s => (P.slope s (1:Fin 3),P.slope s (2:Fin 3))) c t‖ ≤ error := by
  constructor
  · simpa only [OriginalWPhysicalDisplacement.incidenceResidual,x,smul_eq_mul,
      Real.norm_eq_abs,mul_comm] using hres (0:Fin 3)
  · rw [Prod.norm_def,max_le_iff]
    constructor
    · simpa only [OriginalWPhysicalDisplacement.incidenceResidual,y,Prod.fst_sub,
        Prod.smul_fst,smul_eq_mul,Real.norm_eq_abs,mul_comm] using hres (1:Fin 3)
    · simpa only [OriginalWPhysicalDisplacement.incidenceResidual,y,Prod.snd_sub,
        Prod.smul_snd,smul_eq_mul,Real.norm_eq_abs,mul_comm] using hres (2:Fin 3)
end NativeCoarsePhaseGeometry
