import Theorems.Thm_StickyKakeya4_original_macro_slice_cell_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace OriginalMacroGrainReadback
open Classical Finset NativeTangentGridCoarsening OriginalMacroSliceCellCount OriginalWGrainDrift
variable {P : Type*}
def slice (E : Finset P) (height : P → ℝ) (z : ℝ) : Finset P := E.filter (fun p => height p=z)
def grains (E : Finset P) (height : P → ℝ) (grain : P → ℝ × ℝ) (z : ℝ) : Finset (ℝ × ℝ) :=
  (slice E height z).image grain
def tangentFiber (E : Finset P) (height : P → ℝ) (grain : P → ℝ × ℝ) (z : ℝ) (g : ℝ × ℝ) : Finset P :=
  (slice E height z).filter (fun p => grain p=g)
lemma grains_nonempty (E : Finset P) (height : P → ℝ) (grain : P → ℝ × ℝ)
    {z : ℝ} (hz : z ∈ E.image height) : (grains E height grain z).Nonempty := by
  obtain ⟨p,hp,hpz⟩ := mem_image.mp hz
  exact ⟨grain p,mem_image_of_mem _ (mem_filter.mpr ⟨hp,hpz⟩)⟩
lemma grain_grid_readback (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (q z : ℝ) :
    grainCells (slice E height z) q height x y F=
      planarCells (grains E height (grainCoordinate height x y F) z) id q := by
  simp only [grainCells,grains,planarCells,image_image]
  rfl
end OriginalMacroGrainReadback
