import Theorems.Thm_StickyKakeya4_original_shading_grid_geometry
import Theorems.Thm_StickyKakeya4_finite_plane_projection_separated

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
open Classical
namespace OriginalShadingRepresentatives
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open OriginalShadingGridGeometry FinitePlaneProjectionGrid

/-- Actual original points in one floor cell differ by at most one mesh. -/
theorem same_cell_close {h : ℝ} (hh : 0<h) (p q : ℝ×ℝ)
    (heq : grid h p = grid h q) : InBox p q h := by
  have hx := NativeTangentGridCoarsening.coarse_floor_interval hh
    (rfl : ⌊p.1/h⌋=⌊p.1/h⌋)
  have hy := NativeTangentGridCoarsening.coarse_floor_interval hh
    (rfl : ⌊p.2/h⌋=⌊p.2/h⌋)
  have hqx := NativeTangentGridCoarsening.coarse_floor_interval hh
    (congrArg Prod.fst heq.symm)
  have hqy := NativeTangentGridCoarsening.coarse_floor_interval hh
    (congrArg Prod.snd heq.symm)
  simp only [grid] at hqx hqy
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

/-- A ninth of occupied cells has mutually separated ACTUAL original
representatives. All shading memberships and original incidences survive. -/
theorem exists_separated_original_representatives {X : Type*}
    (Y : Finset X) (p : X → ℝ×ℝ) {h : ℝ} (hh : 0<h) :
    ∃ R : Finset X, R ⊆ Y ∧
      (Y.image (fun y => grid h (p y))).card ≤ 9*R.card ∧
      Set.InjOn (fun y => grid h (p y)) (↑R) ∧
      (∀ a∈R, ∀ b∈R, a≠b →
        2*h < max |(p a).1-(p b).1| |(p a).2-(p b).2|) := by
  obtain ⟨S,hSY,_himage,hinj,hcard⟩ :=
    exists_cell_representatives Y (fun y => grid h (p y))
  obtain ⟨color,_hc,R,hRS,hRcard,hcolor⟩ :=
    exists_cell_color S (fun y => grid h (p y))
  refine ⟨R,hRS.trans hSY,?_,hinj.mono hRS,?_⟩
  · rw [← hcard]
    exact hRcard
  · intro a ha b hb hab
    have hcell : grid h (p a) ≠ grid h (p b) :=
      fun he => hab (hinj (hRS ha) (hRS hb) he)
    have hmod := (hcolor a ha).trans (hcolor b hb).symm
    have hx := congrArg Prod.fst hmod
    have hy := congrArg Prod.snd hmod
    by_cases hfirst : ⌊(p a).1/h⌋=⌊(p b).1/h⌋
    · have hsecond : ⌊(p a).2/h⌋≠⌊(p b).2/h⌋ := by
        intro he
        exact hcell (Prod.ext hfirst he)
      exact (same_residue_floor_separation hh hy hsecond).trans_le (le_max_right _ _)
    · exact (same_residue_floor_separation hh hx hfirst).trans_le (le_max_left _ _)

/-- Original cells of representatives in an R-ball lift only to original
fine points in the 2R-ball when R is no smaller than the coarse mesh. -/
theorem representative_ball_original_preimage {X : Type*}
    (Y R : Finset X) (p : X → ℝ×ℝ) {h r : ℝ} (hh : 0<h) (hr : h≤r)
    (x : ℝ×ℝ) :
    Y.filter (fun y => grid h (p y)∈
      (R.filter (fun a => InBox (p a) x r)).image (fun a => grid h (p a)))
      ⊆ Y.filter (fun y => InBox (p y) x (2*r)) := by
  intro y hy
  obtain ⟨hy,hcell⟩ := Finset.mem_filter.mp hy
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hcell
  have hclose := same_cell_close hh (p y) (p a) he.symm
  have hx := hclose.trans (Finset.mem_filter.mp ha).2
  exact Finset.mem_filter.mpr ⟨hy,hx.mono (by linarith)⟩

end OriginalShadingRepresentatives
