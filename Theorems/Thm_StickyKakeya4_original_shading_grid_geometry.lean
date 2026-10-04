import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace OriginalShadingGridGeometry

def grid (h : ℝ) (p : ℝ×ℝ) : ℤ×ℤ := (⌊p.1/h⌋,⌊p.2/h⌋)
def corner (h : ℝ) (c : ℤ×ℤ) : ℝ×ℝ := (h*c.1,h*c.2)
def InBox (p x : ℝ×ℝ) (r : ℝ) : Prop := |p.1-x.1|≤r ∧ |p.2-x.2|≤r

/-- Literal lower-corner quantization moves each coordinate by at most
one mesh, while the original point remains available as a representative. -/
theorem point_in_own_cell {h : ℝ} (hh : 0<h) (p : ℝ×ℝ) :
    InBox p (corner h (grid h p)) h := by
  have hx := NativeTangentGridCoarsening.coarse_floor_interval hh
    (rfl : ⌊p.1/h⌋=⌊p.1/h⌋)
  have hy := NativeTangentGridCoarsening.coarse_floor_interval hh
    (rfl : ⌊p.2/h⌋=⌊p.2/h⌋)
  constructor
  · dsimp [corner,grid]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · dsimp [corner,grid]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma InBox.trans {p q x : ℝ×ℝ} {r s : ℝ}
    (hp : InBox p q r) (hq : InBox q x s) : InBox p x (r+s) := by
  exact ⟨(abs_sub_le p.1 q.1 x.1).trans (add_le_add hp.1 hq.1),
    (abs_sub_le p.2 q.2 x.2).trans (add_le_add hp.2 hq.2)⟩

lemma InBox.mono {p x : ℝ×ℝ} {r s : ℝ} (h : r≤s)
    (hp : InBox p x r) : InBox p x s := ⟨hp.1.trans h,hp.2.trans h⟩

/-- Every original point above a coarse cell in an R-box is inside the
actual enlarged R+h box; for R≥h this is the actual 2R-box. -/
theorem coarse_box_original_preimage {h R : ℝ} (hh : 0<h) (hR : h≤R)
    (p x : ℝ×ℝ) (hp : InBox (corner h (grid h p)) x R) :
    InBox p x (2*R) := by
  exact (InBox.trans (point_in_own_cell hh p) hp).mono (by linarith)

/-- The cell filter lifts into a genuine ORIGINAL point ball. -/
theorem coarse_box_preimage_subset {X : Type*} (Y : Finset X)
    (p : X → ℝ×ℝ) (U : Finset (ℤ×ℤ)) {h R : ℝ}
    (hh : 0<h) (hR : h≤R) (x : ℝ×ℝ) :
    Y.filter (fun y => grid h (p y) ∈ U.filter (fun c => InBox (corner h c) x R))
      ⊆ Y.filter (fun y => InBox (p y) x (2*R)) := by
  intro y hy
  obtain ⟨hy,hcell⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hy,coarse_box_original_preimage hh hR (p y) x
    (Finset.mem_filter.mp hcell).2⟩

end OriginalShadingGridGeometry
