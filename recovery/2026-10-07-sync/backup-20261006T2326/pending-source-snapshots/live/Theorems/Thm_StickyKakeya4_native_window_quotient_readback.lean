import Theorems.Thm_StickyKakeya4_native_window_quotient_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeWindowQuotientReadback
open Classical Finset NativeWindowXYLabels NativeTwoMapRetainedSliceLabels
open NativeQuotientLatticeTransport NativeQuotientGridCenters

/-- Quotient labels of a true coarse window are an exact image of its
original fine labels, with no replacement of their cardinality by a mesh. -/
lemma quotient_eq_filtered_image {k l : ℕ} (S : Finset (XY k l)) (H R : ℕ) (h : ℤ) :
    (productSlice (S.image (window H R)) h).image Prod.snd=
      (S.filter (fun z => z.1/(H:ℤ)=h)).image (fun z => gridDiv R z.2.2) := by
  ext y
  simp only [productSlice,mem_image,mem_filter]
  constructor
  · rintro ⟨p,⟨z,⟨⟨w,hw,rfl⟩,hh⟩,rfl⟩,rfl⟩
    exact ⟨w,⟨hw,hh⟩,rfl⟩
  · rintro ⟨w,⟨hw,hh⟩,rfl⟩
    exact ⟨(window H R w).2,⟨window H R w,⟨⟨w,hw,rfl⟩,hh⟩,rfl⟩,rfl⟩

/-- This is exactly the coarse image of the union of the fine Y slices
whose genuine translated heights belong to the chosen interval. -/
lemma quotient_eq_union {k l : ℕ} (S : Finset (XY k l)) (H R : ℕ) (h : ℤ) :
    (productSlice (S.image (window H R)) h).image Prod.snd=
      ((S.image Prod.fst).filter (fun t => t/(H:ℤ)=h)).biUnion
        (fun t => ((productSlice S t).image Prod.snd).image (gridDiv R)) := by
  rw [quotient_eq_filtered_image]
  ext y
  simp only [mem_image,mem_filter,mem_biUnion,productSlice]
  constructor
  · rintro ⟨z,⟨hz,hh⟩,rfl⟩
    exact ⟨z.1,⟨⟨z,hz,rfl⟩,hh⟩,z.2.2,⟨z.2,⟨z,⟨hz,rfl⟩,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨t,⟨_ht,hh⟩,y,⟨p,⟨z,⟨hz,hzt⟩,rfl⟩,rfl⟩,rfl⟩
    exact ⟨z,⟨hz,by simpa only [hzt] using hh⟩,rfl⟩

/-- Integer coarsening is also the literal dyadic bin of the existing
real fine-grid center. -/
lemma floor_center_ediv {mesh : ℝ} (hmesh : 0 < mesh) (R : ℕ) (x : ℤ) :
    ⌊mesh*((x:ℝ)+1/2)/(mesh*(R:ℝ))⌋=x/(R:ℤ) := by
  rw [mul_div_mul_left _ _ hmesh.ne',Int.floor_div_natCast,Int.floor_intCast_add]
  norm_num

lemma center_coarse_label {l : ℕ} {mesh : ℝ} (hmesh : 0 < mesh) (R : ℕ) (y : Fin l → ℤ) :
    (fun j => ⌊center mesh y j/(mesh*(R:ℝ))⌋)=gridDiv R y := by
  funext j
  exact floor_center_ediv hmesh R (y j)

end NativeWindowQuotientReadback
