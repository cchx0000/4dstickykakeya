import Theorems.Thm_StickyKakeya4_native_merged_point_offsets
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeMergedDirectionQuotient
open Classical Finset StickyKakeya4 NativeMergedPointOffsets
open NativeHorizontalGrainSlice NativeReferenceXYGridLinear
open scoped Matrix.Norms.Elementwise

/-- A prescribed height-only field agrees with the original matrix on
actual source occurrences. No choice of a second geometric plane occurs. -/
theorem retained_quotient_residual
    {Omega Point Cell : Type*}
    (U T : Finset Omega) (hTU : T ⊆ U)
    (point : Omega → Point) (cell : Omega → Cell)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P = ell - 1)
    (M : Point → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Omega → EuclideanSpace ℝ (Fin (4-ell)))
    (fine coarse : Omega → E4) (error angular osc : ℝ)
    (hM : ∀w ∈ U, ‖M (point w)‖ ≤ (1/4 : ℝ))
    (hread : ∀w ∈ U, ∀v ∈ U, point w = point v → cell w = cell v)
    (hcoh : ∀w ∈ U, ∀v ∈ U, cell w = cell v → ‖xi w - xi v‖ ≤ osc)
    (hres : ∀w ∈ U,
      ‖quotientMap P hP ell hell hell4 hd (M (point w)) (fine w) - xi w‖ ≤ error)
    (hmove : ∀w ∈ T, ‖coarse w - fine w‖ ≤ angular)
    (w : Omega) (hw : w ∈ T) :
    ‖quotientMap P hP ell hell hell4 hd (M (point w)) (coarse w) -
        pointOffset U point xi (point w)‖ ≤ error + 2*angular + osc := by
  apply residual_on_retained_source U T hTU point cell xi
    (fun z => quotientMap P hP ell hell hell4 hd (M (point z)) (fine z))
    (fun z => quotientMap P hP ell hell hell4 hd (M (point z)) (coarse z))
    error (2*angular) osc hread hcoh hres ?_ w hw
  intro z hz
  rw [←map_sub]
  exact (quotient_norm_le P hP ell hell hell4 hd (M (point z)) (hM z (hTU hz))
    (coarse z-fine z)).trans (mul_le_mul_of_nonneg_left (hmove z hz) (by norm_num))

/-- The actual base menu has old physical width64Delta. Combining its
coherence constant129/4 with the full-parent representative distance gives
one explicit direction-graph error at analytic width8Delta. The theorem
uses the same U-defined offset for every later T. -/
theorem configured_residual_267
    {Omega Point Cell : Type*}
    (U T : Finset Omega) (hTU : T ⊆ U)
    (point : Omega → Point) (cell : Omega → Cell)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P = ell - 1)
    (M : Point → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Omega → EuclideanSpace ℝ (Fin (4-ell)))
    (fine coarse : Omega → E4) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hM : ∀w ∈ U, ‖M (point w)‖ ≤ (1/4 : ℝ))
    (hread : ∀w ∈ U, ∀v ∈ U, point w = point v → cell w = cell v)
    (hcoh : ∀w ∈ U, ∀v ∈ U, cell w = cell v →
      ‖xi w - xi v‖ ≤ (129/4 : ℝ)*(64*Delta))
    (hres : ∀w ∈ U,
      ‖quotientMap P hP ell hell hell4 hd (M (point w)) (fine w) - xi w‖ ≤ 64*Delta)
    (hmove : ∀w ∈ T, ‖coarse w-fine w‖ ≤ (3/64 : ℝ)*Delta)
    (w : Omega) (hw : w ∈ T) :
    ‖quotientMap P hP ell hell hell4 hd (M (point w)) (coarse w) -
        pointOffset U point xi (point w)‖ ≤ 267*(8*Delta) := by
  have hh := retained_quotient_residual U T hTU point cell P hP ell hell hell4 hd M xi
    fine coarse (64*Delta) ((3/64 : ℝ)*Delta) ((129/4 : ℝ)*(64*Delta))
    hM hread hcoh hres hmove w hw
  exact hh.trans (configured_direction_budget hDelta le_rfl (by ring_nf; exact le_rfl) (by ring_nf; exact le_rfl))

end NativeMergedDirectionQuotient
