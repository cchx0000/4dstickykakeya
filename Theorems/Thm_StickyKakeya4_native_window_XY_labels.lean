import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativeWindowXYLabels
open NativeTwoMapRetainedSliceLabels NativeAnisotropicSliceLabels

/-- Exact integer coarsening of tangent or quotient bins. -/
def gridDiv {d : ℕ} (R : ℕ) (x : Fin d → ℤ) : Fin d → ℤ := fun j => x j/(R:ℤ)

/-- Coarsen the actual fine translated height and XY labels independently.
The physical window width uses H=8T when the spatial factor is T. -/
def window {k l : ℕ} (H R : ℕ) (z : XY k l) : XY k l :=
  (z.1/(H:ℤ),(gridDiv R z.2.1,gridDiv R z.2.2))

lemma window_height {k l : ℕ} (H R : ℕ) (z : XY k l) :
    (window H R z).1=z.1/(H:ℤ) := rfl

lemma gridDiv_comp {d : ℕ} (R S : ℕ) (x : Fin d → ℤ) :
    gridDiv S (gridDiv R x)=gridDiv (R*S) x := by
  funext j
  simp only [gridDiv,Nat.cast_mul]
  exact Int.ediv_ediv_of_nonneg (Int.natCast_nonneg R)

lemma window_coarse {k l : ℕ} (H R S : ℕ) (z : XY k l) :
    coarse S (window H R z)=window H (R*S) z := by
  refine Prod.ext rfl ?_
  exact Prod.ext (gridDiv_comp R S z.2.1) (gridDiv_comp R S z.2.2)

lemma window_comp {k l : ℕ} (H R H' R' : ℕ) (z : XY k l) :
    window H' R' (window H R z)=window (H*H') (R*R') z := by
  apply Prod.ext
  · simp only [window,Nat.cast_mul]
    exact Int.ediv_ediv_of_nonneg (Int.natCast_nonneg H)
  · exact Prod.ext (gridDiv_comp R R' z.2.1) (gridDiv_comp R R' z.2.2)

lemma encode_window_coarse {k l : ℕ} (hd : k+l=3) (fine depth H R : ℕ) (z : XY k l) :
    horizontalCoarsen fine depth (encode hd (window H R z))=
      encode hd (window H (R*2^(fine-depth)) z) := by
  rw [←encode_coarse,window_coarse]

end NativeWindowXYLabels
