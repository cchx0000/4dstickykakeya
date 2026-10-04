import Theorems.Thm_StickyKakeya4_original_window_physical_cells
import Theorems.Thm_StickyKakeya4_native_original_phase_window_population
import Theorems.Thm_StickyKakeya4_native_dyadic_mesh_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalWindowKT
open Classical OriginalWindowPhysicalCells OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWGrainDrift FinitePhaseFieldImages
open OriginalPhaseGridPopulation NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowPopulation
open FinitePlaneProjectionGrid
/-- The literal cap for a nine-cell enlargement of the original grain window. -/
def windowFiberCap (r tau Delta width A Cxi : ℝ) : ℝ :=
  (r/Delta+2)*((4*width+A*r)/Delta+2)^2*(2*Cxi*Delta/tau+2)^2
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- Every first x-label fiber of the ACTUAL expanded W-window phase set is
 counted from original physical cells. No original state is discarded. -/
theorem actual_window_first_fiber
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x0 : ℝ) (xi0 : ℝ × ℝ) (k : GrainLabel)
    {r tau Delta width A Cxi : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta) (hwidth : 0 < width)
    (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi) (hF : ‖F z‖ ≤ A)
    (hfield : ∀ p ∈ TwoTubePathCollisionCount.points I,
      ‖offset p-field (OriginalPhaseCellPopulation.physicalCell Delta height x y p)‖ ≤ Cxi*Delta) :
    ∀ j : ℤ, (((expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height S hSV s)) k).filter
      (fun a => a.1=j)).card:ℝ) ≤ windowFiberCap r tau Delta width A Cxi := by
  let representative := rep I height S hSV
  let h := fun s : Core S => height (representative s)
  let X := fun s : Core S => x (representative s)
  let Y := fun s : Core S => y (representative s)
  let Xi := fun s : Core S => offset (representative s)
  let grain := fun s : Core S => grainCell width (grainCoordinate height x y F (representative s))
  let E := (heightSlice S z).filter (fun s => grain s ∈ neighborCells k)
  have hheight : ∀ s ∈ E, h s=z := by
    intro s hs
    exact (rep_spec I height S hSV s).2.trans (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have hgrain : ∀ s ∈ E,
      ‖grainCoordinate h X Y F s-(width*(k.1:ℝ),width*(k.2:ℝ))‖ ≤ 2*width := by
    intro s hs
    exact neighbor_grain_window hwidth _ k (Finset.mem_filter.mp hs).2
  have hfield' : ∀ s ∈ E,
      ‖Xi s-field (OriginalPhaseCellPopulation.physicalCell Delta h X Y s)‖ ≤ Cxi*Delta := by
    intro s _hs
    exact hfield _ (Finset.mem_image_of_mem Prod.fst (rep_spec I height S hSV s).1)
  have hh := original_phase_first_fiber E h X Y Xi F field z x0
    (width*(k.1:ℝ),width*(k.2:ℝ)) xi0 hr htau hDelta (by positivity : 0 ≤ 2*width) hA hCxi
    hheight hF hgrain hfield'
  intro j
  rw [expanded_eq_phase_image]
  have hwid : 2*(2*width)=4*width := by ring
  simpa only [windowFiberCap,hwid,phaseCells,phaseLabel,normalPhaseCell,E,grain,X,Xi,representative] using hh j
/-- Local absolute KT1 of the actual embedded A/window, obtained by first
 coordinate interval counting. The center is arbitrary and the labels are
 exactly the original occupied phase labels. -/
theorem actual_window_KT
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x0 : ℝ) (xi0 : ℝ × ℝ) (k : GrainLabel)
    {r tau Delta width A Cxi mesh : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta) (hwidth : 0 < width)
    (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi) (hF : ‖F z‖ ≤ A)
    (hfield : ∀ p ∈ TwoTubePathCollisionCount.points I,
      ‖offset p-field (OriginalPhaseCellPopulation.physicalCell Delta height x y p)‖ ≤ Cxi*Delta)
    (hmesh : 0 < mesh) (center : Point) (R : ℝ) (hR : mesh ≤ R) :
    (((expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height S hSV s)) k).filter
      (fun a => ‖gridPoint mesh a-center‖ ≤ R)).card:ℝ) ≤
      (4*windowFiberCap r tau Delta width A Cxi)*R/mesh := by
  have hcap := actual_window_first_fiber I height x y offset F field S hSV z x0 xi0 k
    hr htau hDelta hwidth hA hCxi hF hfield
  have hnonneg : 0 ≤ windowFiberCap r tau Delta width A Cxi := by unfold windowFiberCap; positivity
  have hh := grid_ball_population_large_radius _ hmesh hnonneg hR hcap center
  simpa only [mul_div_assoc] using hh
/-- Direct input to the actual graph-aware projection: all original phase
 labels and their original positions survive common mesh refinement. -/
theorem actual_window_projection_KT
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x0 : ℝ) (xi0 : ℝ × ℝ) (k : GrainLabel)
    {r tau Delta width A Cxi sourceMesh mesh : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta) (hwidth : 0 < width)
    (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi) (hF : ‖F z‖ ≤ A)
    (hfield : ∀ p ∈ TwoTubePathCollisionCount.points I,
      ‖offset p-field (OriginalPhaseCellPopulation.physicalCell Delta height x y p)‖ ≤ Cxi*Delta)
    (hSourceMesh : 0 < sourceMesh) (hmesh : 0 < mesh) (hmeshScale : mesh ≤ sourceMesh) :
    let Q := expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height S hSV s)) k
    ∀ i ∈ Q, ∀ R : ℝ, mesh ≤ R →
      ((Q.filter (fun j => dist3 (gridPoint sourceMesh i) (gridPoint sourceMesh j) ≤ R)).card:ℝ) ≤
        (4*windowFiberCap r tau Delta width A Cxi)*R/mesh := by
  dsimp only
  apply NativeDyadicMeshSelection.original_KT_at_finer_mesh _ _ hSourceMesh hmesh hmeshScale
    (show 0 ≤ 4*windowFiberCap r tau Delta width A Cxi by unfold windowFiberCap; positivity)
  intro i _hi R hR
  have hh := actual_window_KT I height x y offset F field S hSV z x0 xi0 k
    hr htau hDelta hwidth hA hCxi hF hfield hSourceMesh (gridPoint sourceMesh i) R hR
  simpa only [dist3_eq_norm,norm_sub_rev] using hh
end NativeOriginalWindowKT
