import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint
import Theorems.Thm_StickyKakeya4_native_common_cubical_mesh

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeRotatedCellSelection
open Classical Finset StickyKakeya4 NativeMatrixHeightWholePoint
open scoped BigOperators

/-- Literal cells in a translated orthonormal physical chart. -/
def rotatedCell (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (rho : ℝ) (x : E4) : Fin 4 → ℤ :=
  wzDyadicCellIndex rho (O (x-c))

/-- The actual old-cell residue palette, independent of the occupied labels. -/
def cellColor (rho : ℝ) (x : E4) : Fin 4 → Fin 5 :=
  fun j => ⟨((wzDyadicCellIndex rho x j) % 5).toNat, by omega⟩

lemma same_grid_coordinate_close {rho : ℝ} (hrho : 0 < rho) {x y : E4}
    (h : wzDyadicCellIndex rho x=wzDyadicCellIndex rho y) (j : Fin 4) :
    |x j-y j| < rho := by
  have hh : heightCell rho 0 (x j)=heightCell rho 0 (y j) := by
    simpa only [heightCell,sub_zero,wzDyadicCellIndex] using congrFun h j
  exact same_height_cell_close hrho hh

lemma same_grid_dist_le {rho : ℝ} (hrho : 0 < rho) {x y : E4}
    (h : wzDyadicCellIndex rho x=wzDyadicCellIndex rho y) : dist x y ≤ 2*rho := by
  have hs : dist x y ^ 2 ≤ (2*rho)^2 := by
    rw [PiLp.dist_sq_eq_of_L2]
    calc
      _ ≤ ∑ _j : Fin 4,rho^2 := by
        apply sum_le_sum
        intro j _hj
        have hh : dist (x j) (y j) ≤ rho := by
          simpa only [Real.dist_eq] using (same_grid_coordinate_close hrho h j).le
        nlinarith [dist_nonneg (x j) (y j)]
      _ = _ := by simp; ring
  nlinarith [dist_nonneg x y]

lemma same_rotated_cell_dist_le (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {rho : ℝ} (hrho : 0 < rho) {x y : E4}
    (h : rotatedCell O c rho x=rotatedCell O c rho y) : dist x y ≤ 2*rho := by
  have hh := same_grid_dist_le hrho h
  simpa only [LinearIsometryEquiv.dist_map,dist_sub_right] using hh

lemma floor_difference_le_two {rho x y : ℝ} (hrho : 0 < rho)
    (h : |x-y| ≤ 2*rho) :
    ⌊y/rho⌋-2 ≤ ⌊x/rho⌋ ∧ ⌊x/rho⌋ ≤ ⌊y/rho⌋+2 := by
  have ha := abs_le.mp h
  have hlo : y/rho-1-1 ≤ x/rho := by
    apply (le_div_iff₀ hrho).mpr
    field_simp [hrho.ne']
    nlinarith
  have hhi : x/rho ≤ y/rho+1+1 := by
    apply (div_le_iff₀ hrho).mpr
    field_simp [hrho.ne']
    nlinarith
  have hl := Int.floor_mono hlo
  have hu := Int.floor_mono hhi
  rw [Int.floor_sub_one,Int.floor_sub_one] at hl
  rw [Int.floor_add_one,Int.floor_add_one] at hu
  omega

/-- Equal residue colors in one genuine rotated cell force the SAME old
physical cell. The statement is not inferred from proximity alone. -/
theorem same_color_same_original_cell (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {rho : ℝ} (hrho : 0 < rho) {x y : E4}
    (hcell : rotatedCell O c rho x=rotatedCell O c rho y)
    (hcolor : cellColor rho x=cellColor rho y) :
    wzDyadicCellIndex rho x=wzDyadicCellIndex rho y := by
  have hd := same_rotated_cell_dist_le O c hrho hcell
  funext j
  have hj : |x j-y j| ≤ 2*rho := by
    exact (by simpa only [Real.dist_eq] using PiLp.dist_apply_le x y j).trans hd
  obtain ⟨hl,hu⟩ := floor_difference_le_two hrho hj
  have hc := congrArg Fin.val (congrFun hcolor j)
  dsimp only [cellColor,wzDyadicCellIndex] at hc ⊢
  omega

/-- A maximum original-weight residue choice inside each new chart cell
keeps at least one625th of the mass, and transfers exact old-cell coherence.
All retained points stay fixed. -/
theorem select_one_rotated_grid {A : Type*} (S : Finset A) (w : A → ℕ)
    (point : A → E4) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ T : Finset A,T⊆S ∧ mass S w ≤ 625*mass T w ∧
      ∀x∈T,∀y∈T,rotatedCell O c rho (point x)=rotatedCell O c rho (point y) →
        wzDyadicCellIndex rho (point x)=wzDyadicCellIndex rho (point y) := by
  obtain ⟨chi,hsub,hlocal,hweight,hmono⟩ := select_color_per_cell S w
    (fun x => rotatedCell O c rho (point x)) (fun x => cellColor rho (point x))
  refine ⟨S.filter (fun x => cellColor rho (point x)=chi (rotatedCell O c rho (point x))),hsub,?_,?_⟩
  · simpa using hweight
  · intro x hx y hy heq
    exact same_color_same_original_cell O c hrho heq (hmono x hx y hy heq)

end NativeRotatedCellSelection
