import Theorems.Thm_StickyKakeya4_original_phase_cell_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalPhaseGridPopulation
open Classical FinitePhaseFieldImages OriginalPhaseCellPopulation OriginalWGrainDrift

abbrev Label := ℤ × (ℤ × ℤ)
abbrev Point := ℝ × (ℝ × ℝ)

def gridPoint (mesh : ℝ) (a : Label) : Point :=
  (mesh*(a.1:ℝ),(mesh*(a.2.1:ℝ),mesh*(a.2.2:ℝ)))

lemma gridPoint_injective {mesh : ℝ} (hmesh : 0 < mesh) : Function.Injective (gridPoint mesh) := by
  intro a b hab
  have hf (k : ℤ) : ⌊mesh*(k:ℝ)/mesh⌋=k :=
    OriginalHeightIntervalCap.floor_original_mesh hmesh rfl
  have hh := congrArg (fun p : Point => (⌊p.1/mesh⌋,(⌊p.2.1/mesh⌋,⌊p.2.2/mesh⌋))) hab
  simpa only [gridPoint,hf] using hh

/-- A first-coordinate population cap gives an actual grid-interval bound.
 Original grid labels are counted; no geometric covering-number certificate
 is assumed. -/
theorem first_interval_population (A : Finset Label) {mesh H length : ℝ}
    (hmesh : 0 < mesh) (hH : 0 ≤ H) (hlength : 0 ≤ length)
    (hfirst : ∀ k : ℤ, ((A.filter (fun a => a.1=k)).card : ℝ) ≤ H) (lo : ℝ) :
    ((A.filter (fun a => lo ≤ mesh*(a.1:ℝ) ∧ mesh*(a.1:ℝ) ≤ lo+length)).card : ℝ) ≤
      H*(length/mesh+2) := by
  let S := A.filter (fun a => lo ≤ mesh*(a.1:ℝ) ∧ mesh*(a.1:ℝ) ≤ lo+length)
  let Q := S.image Prod.fst
  have hmaps : ∀ a ∈ S, a.1 ∈ Q := fun a ha => Finset.mem_image_of_mem _ ha
  have hfiber : ∀ k ∈ Q, ((S.filter (fun a => a.1=k)).card : ℝ) ≤ H := by
    intro k _hk
    have hsub : S.filter (fun a => a.1=k) ⊆ A.filter (fun a => a.1=k) := by
      intro a ha
      obtain ⟨haS,hak⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haS).1,hak⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfirst k)
  have hcard := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers S Q Prod.fst H hmaps hfiber
  have hgrid : NativeTangentGridCoarsening.scalarCells S (fun a => mesh*(a.1:ℝ)) mesh=Q := by
    apply Finset.image_congr
    intro a _ha
    exact OriginalHeightIntervalCap.floor_original_mesh hmesh rfl
  have hQ := NativeTangentGridCoarsening.scalar_interval_grid_card S (fun a => mesh*(a.1:ℝ))
    hmesh hlength (fun a ha => (Finset.mem_filter.mp ha).2)
  rw [hgrid] at hQ
  calc
    _ ≤ (Q.card : ℝ)*H := hcard
    _ ≤ (length/mesh+2)*H := mul_le_mul_of_nonneg_right hQ hH
    _ = H*(length/mesh+2) := by ring

/-- Derived local one-dimensional population for the ACTUAL embedded phase
 grid, in the native nested-product maximum norm. -/
theorem grid_ball_population (A : Finset Label) {mesh H R : ℝ}
    (hmesh : 0 < mesh) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hfirst : ∀ k : ℤ, ((A.filter (fun a => a.1=k)).card : ℝ) ≤ H) (center : Point) :
    ((A.filter (fun a => ‖gridPoint mesh a-center‖ ≤ R)).card : ℝ) ≤ H*(2*R/mesh+2) := by
  have hsub : A.filter (fun a => ‖gridPoint mesh a-center‖ ≤ R) ⊆
      A.filter (fun a => center.1-R ≤ mesh*(a.1:ℝ) ∧ mesh*(a.1:ℝ) ≤ center.1-R+2*R) := by
    intro a ha
    obtain ⟨haA,hn⟩ := Finset.mem_filter.mp ha
    have hx := (max_le_iff.mp hn).1
    change |mesh*(a.1:ℝ)-center.1| ≤ R at hx
    have hh := abs_le.mp hx
    exact Finset.mem_filter.mpr ⟨haA,by linarith [hh.1],by linarith [hh.2]⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (first_interval_population A hmesh hH (show 0 ≤ 2*R by positivity) hfirst (center.1-R))

theorem grid_ball_population_large_radius (A : Finset Label) {mesh H R : ℝ}
    (hmesh : 0 < mesh) (hH : 0 ≤ H) (hR : mesh ≤ R)
    (hfirst : ∀ k : ℤ, ((A.filter (fun a => a.1=k)).card : ℝ) ≤ H) (center : Point) :
    ((A.filter (fun a => ‖gridPoint mesh a-center‖ ≤ R)).card : ℝ) ≤ 4*H*(R/mesh) := by
  have hh := grid_ball_population A hmesh hH (hmesh.le.trans hR) hfirst center
  have hratio : 1 ≤ R/mesh := (le_div_iff₀ hmesh).mpr (by simpa using hR)
  have hc : 2*R/mesh+2 ≤ 4*(R/mesh) := by rw [mul_div_assoc]; linarith
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hc hH])

variable {P : Type*}

/-- Filtering the actual phase IMAGE at one tangent label is exactly the
 phase image of the corresponding original point fiber. -/
lemma phase_filter_first_image (E : Finset P) (tangentCell : P → ℤ) (tau : ℝ)
    (xi₀ : ℝ × ℝ) (offset : P → ℝ × ℝ) (k : ℤ) :
    (phaseCells E tangentCell tau xi₀ offset).filter (fun a => a.1=k)=
      phaseCells (E.filter (fun p => tangentCell p=k)) tangentCell tau xi₀ offset := by
  ext a
  constructor
  · intro ha
    obtain ⟨ha,hak⟩ := Finset.mem_filter.mp ha
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,?_⟩,hpa⟩
    exact (congrArg Prod.fst hpa).trans hak
  · intro ha
    obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp ha
    obtain ⟨hpE,hpk⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,hpE,hpa⟩,
      (congrArg Prod.fst hpa).symm.trans hpk⟩

/-- The original microscopic physical field supplies every first-coordinate
 fiber cap of the actual phase image. A one-dimensional cap is concluded,
 rather than taken as an inherited property. -/
theorem original_phase_first_fiber_cap
    (E : Finset P) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (z x₀ : ℝ) (g₀ xi₀ : ℝ × ℝ)
    {r tau Delta W A Cxi : ℝ} (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi)
    (hrDelta : r ≤ Delta) (hwidth : 2*W+A*r ≤ Delta)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g₀‖ ≤ W)
    (hfield : ∀ p ∈ E,
      ‖offset p-field (physicalCell Delta height x y p)‖ ≤ Cxi*Delta) :
    ∀ k : ℤ, (((phaseCells E (fun p => ⌊(x p-x₀)/r⌋) tau xi₀ offset).filter
      (fun a => a.1=k)).card : ℝ) ≤ 27*(2*Cxi*Delta/tau+2)^2 := by
  intro k
  rw [phase_filter_first_image]
  apply original_phase_cells_over_x_cell (E.filter (fun p => ⌊(x p-x₀)/r⌋=k))
    height x y offset F field z x₀ g₀ xi₀ k hr htau hDelta hW hA hCxi hrDelta hwidth
  · intro p hp
    exact hheight p (Finset.mem_filter.mp hp).1
  · exact hF
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    exact hgrain p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact hfield p (Finset.mem_filter.mp hp).1

/-- Native original-field producer of the local phase population consumed by
 finite projection. All point fields and grid maps remain literal. -/
theorem original_phase_ball_population
    (E : Finset P) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (field : (ℤ × (ℤ × (ℤ × ℤ))) → ℝ × ℝ)
    (z x₀ : ℝ) (g₀ xi₀ : ℝ × ℝ)
    {r tau Delta W A Cxi mesh R : ℝ} (hr : 0 < r) (htau : 0 < tau) (hDelta : 0 < Delta)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hCxi : 0 ≤ Cxi)
    (hrDelta : r ≤ Delta) (hwidth : 2*W+A*r ≤ Delta)
    (hheight : ∀ p ∈ E, height p=z) (hF : ‖F z‖ ≤ A)
    (hgrain : ∀ p ∈ E, ‖grainCoordinate height x y F p-g₀‖ ≤ W)
    (hfield : ∀ p ∈ E,
      ‖offset p-field (physicalCell Delta height x y p)‖ ≤ Cxi*Delta)
    (hmesh : 0 < mesh) (hR : 0 ≤ R) (center : Point) :
    (((phaseCells E (fun p => ⌊(x p-x₀)/r⌋) tau xi₀ offset).filter
      (fun a => ‖gridPoint mesh a-center‖ ≤ R)).card : ℝ) ≤
      (27*(2*Cxi*Delta/tau+2)^2)*(2*R/mesh+2) := by
  exact grid_ball_population _ hmesh (by positivity) hR
    (original_phase_first_fiber_cap E height x y offset F field z x₀ g₀ xi₀
      hr htau hDelta hW hA hCxi hrDelta hwidth hheight hF hgrain hfield) center

end OriginalPhaseGridPopulation
