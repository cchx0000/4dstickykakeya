import Theorems.Thm_StickyKakeya4_native_window_real_interpolation
import Theorems.Thm_StickyKakeya4_native_literal_grid_cover_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowBaseCover
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowQuotientReadback NativeQuotientGridCenters FiniteVoronoiRealADCoarsening

/-- The final Y coordinates are rounded once at R0. A larger window keeps
these same normal coordinates; it does not refreeze the height field. -/
def baseUnion {k l : ℕ} (S : Finset (XY k l)) (mu : ℝ) (R0 D : ℕ) (z : XY k l) :
    Finset (Fin l → ℝ) :=
  (S.filter (fun w => w.1/((8*(R0*D):ℕ):ℤ)=z.1/((8*(R0*D):ℕ):ℤ))).image
    (fun w => center (mu*(R0:ℝ)) (gridDiv R0 w.2.2))

/-- The base time center falls in the exact intended coarse interval,
including negative heights and all dyadic boundary cases. -/
lemma base_height_label {mu : ℝ} (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (t : ℤ) :
    ⌊(mu*(R0:ℝ))*(((t/((8*R0:ℕ):ℤ):ℤ):ℝ)+1/2)/(mu*((R0*D:ℕ):ℝ))⌋=
      t/((8*(R0*D):ℕ):ℤ) := by
  have hbase : 0 < mu*(R0:ℝ) := mul_pos hmu (Nat.cast_pos.mpr hR0)
  rw [Nat.cast_mul,←mul_assoc,floor_center_ediv hbase D]
  exact height_div_comp R0 D t

/-- Actual final time coordinate before any optional common scalar
normalization; mu may already include the final factor1/512. -/
def baseTime (mu : ℝ) (R0 : ℕ) (t : ℤ) : ℝ :=
  (mu*(R0:ℝ))*(((t/((8*R0:ℕ):ℤ):ℤ):ℝ)+1/2)

def actualTimeWindow {k l : ℕ} (S : Finset (XY k l)) (mu : ℝ)
    (R0 D : ℕ) (z : XY k l) : Finset (Fin l → ℝ) :=
  (S.filter (fun w =>
    ⌊baseTime mu R0 w.1/(mu*((R0*D:ℕ):ℝ))⌋=
      ⌊baseTime mu R0 z.1/(mu*((R0*D:ℕ):ℝ))⌋)).image
    (fun w => center (mu*(R0:ℝ)) (gridDiv R0 w.2.2))

/-- The literal coarse interval of the final time centers selects exactly
the original height window used by the source profile. -/
lemma actualTimeWindow_eq {k l : ℕ} (S : Finset (XY k l)) {mu : ℝ}
    (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (z : XY k l) :
    actualTimeWindow S mu R0 D z=baseUnion S mu R0 D z := by
  simp only [actualTimeWindow,baseUnion,baseTime,base_height_label hmu R0 D hR0]

lemma base_normal_label {l : ℕ} {mu : ℝ} (hmu : 0 < mu)
    (R0 D : ℕ) (hR0 : 0 < R0) (y : Fin l → ℤ) :
    NativeLiteralGridCoverAD.label (mu*((R0*D:ℕ):ℝ))
      (center (mu*(R0:ℝ)) (gridDiv R0 y))=gridDiv (R0*D) y := by
  have hbase : 0 < mu*(R0:ℝ) := mul_pos hmu (Nat.cast_pos.mpr hR0)
  unfold NativeLiteralGridCoverAD.label
  rw [Nat.cast_mul,←mul_assoc,center_coarse_label hbase D,gridDiv_comp]

/-- Exact occupied rho-cube keys of the unchanged base-normal union.
This is a global occupied-key identity, not a claim about ball filters. -/
theorem occupied_keys {k l : ℕ} (S : Finset (XY k l)) {mu : ℝ}
    (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (z : XY k l) :
    (baseUnion S mu R0 D z).image (NativeLiteralGridCoverAD.label (mu*((R0*D:ℕ):ℝ)))=
      atPoint S (R0*D) z := by
  rw [baseUnion,image_image,atPoint_eq_image]
  apply image_congr
  intro w _hw
  exact base_normal_label hmu R0 D hR0 w.2.2

lemma representatives_eq {k l : ℕ} (S : Finset (XY k l)) {mu : ℝ}
    (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (z : XY k l) :
    NativeLiteralGridCoverAD.representatives (baseUnion S mu R0 D z) (mu*((R0*D:ℕ):ℝ))=
      points S (R0*D) (mu*((R0*D:ℕ):ℝ)) z := by
  unfold NativeLiteralGridCoverAD.representatives
  rw [occupied_keys S hmu R0 D hR0 z]
  rfl

/-- The actual matching-scale window profile gives occupied-cube AD of
its literal base-normal union. The separate global source count controls
the top-radius range in the localized-ball transfer. -/
theorem base_union_cover_AD {k l : ℕ} (S : Finset (XY k l)) {mu K G s : ℝ}
    (hmu : 0 < mu) (R0 D : ℕ) (hR0 : 0 < R0) (hD : 0 < D) (z : XY k l)
    (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds (points S (R0*D) (mu*((R0*D:ℕ):ℝ)) z) (mu*((R0*D:ℕ):ℝ)) K s)
    (Hglobal : ((atPoint S (R0*D) z).card:ℝ) ≤ G*(mu*((R0*D:ℕ):ℝ))^(-s)) :
    NativeLiteralGridCoverAD.CoverADBounds (baseUnion S mu R0 D z)
      (mu*((R0*D:ℕ):ℝ)) ((2:ℝ)^s*max K G) s := by
  have hrho : 0 < mu*((R0*D:ℕ):ℝ) := mul_pos hmu (Nat.cast_pos.mpr (Nat.mul_pos hR0 hD))
  apply NativeLiteralGridCoverAD.cover_AD_of_representatives _ hrho hK hs
  · rw [representatives_eq S hmu R0 D hR0 z]
    exact H
  · rw [representatives_eq S hmu R0 D hR0 z,points_card S (R0*D) hrho]
    exact Hglobal

end NativeWindowBaseCover
