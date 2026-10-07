/- NEW UNVERIFIED DRAFT, 2026-10-06.
   Exact integer height readback only. Spatial coarsening and the actual
   source height bound are supplied by their separate source readers. -/
import Theorems.Thm_StickyKakeya4_native_finite_slice_union_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace NativeCoarseHeightEndpoint
open NativeFiniteSliceUnionAD

/-- If the actual source height lies in [-4Rmax,4Rmax], every coarser
height window of width8R has the same negative/nonnegative label. -/
theorem height_label_eq_sign (Rmax R : ℕ) (hRmax : 0 < Rmax) (hR : Rmax ≤ R)
    (z : ℤ) (hz : |z| ≤ 4*(Rmax:ℤ)) :
    z/(8*(R:ℤ)) = if z < 0 then -1 else 0 := by
  have hRmaxZ : (0:ℤ) < Rmax := by exact_mod_cast hRmax
  have hRZ : (Rmax:ℤ) ≤ R := by exact_mod_cast hR
  have hden : (0:ℤ) < 8*(R:ℤ) := by omega
  obtain ⟨hlo,hhi⟩ := abs_le.mp hz
  split_ifs with hneg
  · apply (Int.ediv_eq_iff_of_pos hden).mpr
    constructor <;> omega
  · apply (Int.ediv_eq_iff_of_pos hden).mpr
    constructor <;> omega

theorem height_label_stable (Rmax R : ℕ) (hRmax : 0 < Rmax) (hR : Rmax ≤ R)
    (z : ℤ) (hz : |z| ≤ 4*(Rmax:ℤ)) :
    z/((8*R:ℕ):ℤ) = z/((8*Rmax:ℕ):ℤ) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (height_label_eq_sign Rmax R hRmax hR z hz).trans
      (height_label_eq_sign Rmax Rmax hRmax le_rfl z hz).symm

/-- Literal coarse-height windows stabilize on the same source. This
does not identify their differently coarsened spatial point maps. -/
theorem heightWindow_stable {Ω X : Type*}
    (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X)
    (Rmax R : ℕ) (hRmax : 0 < Rmax) (hR : Rmax ≤ R)
    (hheight : ∀a∈A, |height a| ≤ 4*(Rmax:ℤ)) (q : ℤ) :
    heightWindow A height value (8*R) q = heightWindow A height value (8*Rmax) q := by
  classical
  have hfilter : A.filter (fun a => height a/((8*R:ℕ):ℤ)=q) =
      A.filter (fun a => height a/((8*Rmax:ℕ):ℤ)=q) := by
    apply Finset.filter_congr
    intro a ha
    rw [height_label_stable Rmax R hRmax hR (height a) (hheight a ha)]
  exact congrArg (fun B : Finset Ω => B.image value) hfilter

end NativeCoarseHeightEndpoint
