import Theorems.Thm_StickyKakeya4_original_phase_grid_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalWindowPhysicalCells
open Classical OriginalPhaseCellPopulation OriginalPhaseGridPopulation OriginalWGrainDrift FinitePhaseFieldImages
variable {P : Type*}
/-- Literal original physical cube count, allowing arbitrary rectangle
 lengths. The scheduled physical field scale need not dominate the window. -/
theorem physical_cells_rectangle
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ) (z cX : ℝ) (cY : ℝ × ℝ)
    {Delta LX LY : ℝ} (hDelta : 0 < Delta) (hLX : 0 ≤ LX) (hLY : 0 ≤ LY)
    (hheight : ∀ p ∈ E, height p=z)
    (hx : ∀ p ∈ E, cX ≤ x p ∧ x p ≤ cX+LX)
    (hy : ∀ p ∈ E,
      (cY.1 ≤ (y p).1 ∧ (y p).1 ≤ cY.1+LY) ∧
      (cY.2 ≤ (y p).2 ∧ (y p).2 ≤ cY.2+LY)) :
    ((physicalCells E Delta height x y).card:ℝ) ≤ (LX/Delta+2)*(LY/Delta+2)^2 := by
  let X := NativeTangentGridCoarsening.scalarCells E x Delta
  let Y := NativeTangentGridCoarsening.planarCells E y Delta
  have hX : (X.card:ℝ) ≤ LX/Delta+2 :=
    NativeTangentGridCoarsening.scalar_interval_grid_card E x hDelta hLX hx
  have hY : (Y.card:ℝ) ≤ (LY/Delta+2)^2 := by
    simpa only [pow_two] using NativeTangentGridCoarsening.planar_rectangle_grid_card E y hDelta hLY hLY hy
  have hsub : physicalCells E Delta height x y ⊆ {⌊z/Delta⌋} ×ˢ (X ×ˢ Y) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr (congrArg (fun a : ℝ => ⌊a/Delta⌋) (hheight p hp)),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩⟩
  have hc : ((physicalCells E Delta height x y).card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_product,Finset.card_singleton,one_mul] at hh
    exact_mod_cast hh
  exact hc.trans (mul_le_mul hX hY (Nat.cast_nonneg _) (by positivity))
/-- A literal x-cell inside the original sheared thin window occupies only
 this many original physical Delta-cubes. All slope/window factors remain. -/
theorem same_x_window_physical_cells
    (E : Finset P) (height x : P → ℝ) (y : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (z x0 : ℝ) (g0 : ℝ × ℝ) (k : ℤ)
    {r Delta W A : ℝ} (hr : 0 < r) (hDelta : 0 < Delta) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hcell : ∀ p ∈ E, ⌊(x p-x0)/r⌋=k)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g0‖ ≤ W) :
    ((physicalCells E Delta height x y).card:ℝ) ≤
      (r/Delta+2)*((2*W+A*r)/Delta+2)^2 := by
  let c := x0+r*(k:ℝ)
  let mid := c+r/2
  let center := g0+F z mid
  let R := W+A*(r/2)
  have hx : ∀ p ∈ E, c ≤ x p ∧ x p ≤ c+r := by
    intro p hp
    have hh := NativeTangentGridCoarsening.coarse_floor_interval hr (hcell p hp)
    dsimp [c]
    constructor <;> linarith [hh.1,hh.2]
  have hmid : ∀ p ∈ E, |x p-mid| ≤ r/2 := by
    intro p hp
    dsimp [mid]
    exact abs_le.mpr ⟨by linarith [(hx p hp).1],by linarith [(hx p hp).2]⟩
  have hy : ∀ p ∈ E, ‖y p-center‖ ≤ R := by
    intro p hp
    calc
      _ = ‖(grainCoordinate height x y F p-g0)+F z (x p-mid)‖ := by
        congr 1
        dsimp [grainCoordinate,center]
        rw [hheight p hp,map_sub]
        abel
      _ ≤ ‖grainCoordinate height x y F p-g0‖+‖F z (x p-mid)‖ := norm_add_le _ _
      _ ≤ W+A*(r/2) := add_le_add (hgrain p hp)
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hF (hmid p hp) (norm_nonneg _) hA))
      _ = R := rfl
  apply physical_cells_rectangle E height x y z c (center.1-R,center.2-R) hDelta hr.le
    (show 0 ≤ 2*W+A*r by positivity) hheight hx
  intro p hp
  have hy1 := abs_le.mp (max_le_iff.mp (hy p hp)).1
  have hy2 := abs_le.mp (max_le_iff.mp (hy p hp)).2
  simp only [Prod.fst_sub,Prod.snd_sub] at hy1 hy2
  have hR : 2*R=2*W+A*r := by dsimp [R]; ring
  change (center.1-R ≤ (y p).1 ∧ (y p).1 ≤ center.1-R+(2*W+A*r)) ∧
    (center.2-R ≤ (y p).2 ∧ (y p).2 ≤ center.2-R+(2*W+A*r))
  exact ⟨⟨by linarith [hy1.1],by linarith [hy1.2]⟩,⟨by linarith [hy2.1],by linarith [hy2.2]⟩⟩
/-- The actual phase image over one x-cell is counted using the SINGLE
 original xi field on physical Delta-cells, without any phase cap premise. -/
theorem original_phase_over_x_cell
    (E : Finset P) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (z x0 : ℝ) (g0 xi0 : ℝ × ℝ) (k : ℤ)
    {r tau Delta W A Cxi : ℝ} (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hcell : ∀ p ∈ E, ⌊(x p-x0)/r⌋=k)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g0‖ ≤ W)
    (hfield : ∀ p ∈ E, ‖offset p-field (physicalCell Delta height x y p)‖ ≤ Cxi*Delta) :
    ((phaseCells E (fun p => ⌊(x p-x0)/r⌋) tau xi0 offset).card:ℝ) ≤
      (r/Delta+2)*((2*W+A*r)/Delta+2)^2*(2*Cxi*Delta/tau+2)^2 := by
  rw [phase_card_of_fixed_tangent_cell E _ tau xi0 offset k hcell]
  have hf := original_field_phase_image E (physicalCell Delta height x y) offset field xi0 htau hDelta.le hCxi hfield
  have hp := same_x_window_physical_cells E height x y F z x0 g0 k hr hDelta hW hA hheight hF hcell hgrain
  calc
    _ ≤ (2*Cxi*Delta/tau+2)^2*((physicalCells E Delta height x y).card:ℝ) := hf
    _ ≤ (2*Cxi*Delta/tau+2)^2*((r/Delta+2)*((2*W+A*r)/Delta+2)^2) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by ring
/-- Every first-coordinate fiber of the same original phase image obeys
 the derived physical-cell cap; arbitrary original multiplicities remain. -/
theorem original_phase_first_fiber
    (E : Finset P) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (z x0 : ℝ) (g0 xi0 : ℝ × ℝ)
    {r tau Delta W A Cxi : ℝ} (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g0‖ ≤ W)
    (hfield : ∀ p ∈ E, ‖offset p-field (physicalCell Delta height x y p)‖ ≤ Cxi*Delta) :
    ∀ k : ℤ, (((phaseCells E (fun p => ⌊(x p-x0)/r⌋) tau xi0 offset).filter (fun a => a.1=k)).card:ℝ) ≤
      (r/Delta+2)*((2*W+A*r)/Delta+2)^2*(2*Cxi*Delta/tau+2)^2 := by
  intro k
  rw [phase_filter_first_image]
  apply original_phase_over_x_cell (E.filter (fun p => ⌊(x p-x0)/r⌋=k)) height x y offset F field z x0 g0 xi0 k
    hr htau hDelta hW hA hCxi
  · intro p hp
    exact hheight p (Finset.mem_filter.mp hp).1
  · exact hF
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    exact hgrain p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact hfield p (Finset.mem_filter.mp hp).1
end OriginalWindowPhysicalCells
