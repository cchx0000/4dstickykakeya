import Theorems.Thm_StickyKakeya4_native_original_phase_window_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPhaseWindowPopulation
open Classical OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalWGrainDrift FinitePhaseFieldImages OriginalPhaseGridPopulation
open NativeOriginalPhaseWindowGraph

/-- The full nine-cell phase enlargement is exactly the phase image of the
 original states whose grain labels lie in those nine cells. -/
lemma expanded_eq_phase_image {V L : Type*} [DecidableEq L]
    (E : Finset V) (grain : V → GrainLabel) (phase : V → L) (k : GrainLabel) :
    expanded E grain phase k=(E.filter (fun s => grain s ∈ neighborCells k)).image phase := by
  ext a
  simp only [expanded,occupied,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter]
  aesop

/-- An actual point in any adjacent grain cell lies within 2*width of the
 central cell's lower corner. This avoids any same-cell assumption. -/
lemma neighbor_grain_window {width : ℝ} (hwidth : 0 < width) (p : ℝ × ℝ) (k : GrainLabel)
    (hp : grainCell width p ∈ neighborCells k) :
    ‖p-(width*(k.1:ℝ),width*(k.2:ℝ))‖ ≤ 2*width := by
  have hf {a : ℝ} {n : ℤ}
      (hn : n-1 ≤ ⌊a/width⌋ ∧ ⌊a/width⌋ ≤ n+1) : |a-width*(n:ℝ)| ≤ 2*width := by
    have hl := Int.floor_le (a/width)
    have hu := Int.lt_floor_add_one (a/width)
    have hn₁ : (n:ℝ)-1 ≤ (⌊a/width⌋:ℝ) := by exact_mod_cast hn.1
    have hn₂ : (⌊a/width⌋:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast hn.2
    have hlow : ((n:ℝ)-1)*width ≤ a := (le_div_iff₀ hwidth).mp (hn₁.trans hl)
    have hupp : a < ((n:ℝ)+2)*width := (div_lt_iff₀ hwidth).mp (by linarith)
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hh := Finset.mem_product.mp hp
  exact max_le (hf (Finset.mem_Icc.mp hh.1)) (hf (Finset.mem_Icc.mp hh.2))

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- The literal enlarged phase set produced by the original incidence graph
 has a proved local one-dimensional population bound. The same single field
 on original physical Delta-cells controls every representative in it. -/
theorem original_enlarged_phase_ball_population
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (z x₀ : ℝ) (xi₀ : ℝ × ℝ) (k : GrainLabel)
    {r tau Delta width A Cxi mesh R : ℝ}
    (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta) (hwidth : 0 < width)
    (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi) (hrDelta : r ≤ Delta)
    (hphysicalwidth : 4*width+A*r ≤ Delta) (hF : ‖F z‖ ≤ A)
    (hfield : ∀ p ∈ TwoTubePathCollisionCount.points I,
      ‖offset p-field (OriginalPhaseCellPopulation.physicalCell Delta height x y p)‖ ≤ Cxi*Delta)
    (hmesh : 0 < mesh) (hR : 0 ≤ R) (center : OriginalPhaseGridPopulation.Point) :
    (((expanded (heightSlice S z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
      (fun s => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s)) k).filter
      (fun a => ‖gridPoint mesh a-center‖ ≤ R)).card : ℝ) ≤
      (27*(2*Cxi*Delta/tau+2)^2)*(2*R/mesh+2) := by
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
  have hc := original_phase_ball_population E h X Y Xi F field z x₀
    (width*(k.1:ℝ),width*(k.2:ℝ)) xi₀ hr htau hDelta (by positivity : 0 ≤ 2*width) hA hCxi
    hrDelta (by linarith) hheight hF hgrain hfield' hmesh hR center
  rw [expanded_eq_phase_image]
  exact hc

end NativeOriginalPhaseWindowPopulation
