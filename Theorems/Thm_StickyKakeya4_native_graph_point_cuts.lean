import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeGraphPhysicalLocalization
open Classical Finset OriginalWWitnessCounts

variable {P T Cell : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq Cell]

/-- Restrict by the actual point label, retaining its entire incidence fiber. -/
def cut (I : Finset (P × T)) (cell : P → Cell) (c : Cell) : Finset (P × T) :=
  I.filter (fun e => cell e.1=c)

omit [DecidableEq P] [DecidableEq T] in
lemma cut_subset (I : Finset (P × T)) (cell : P → Cell) (c : Cell) : cut I cell c⊆I :=
  filter_subset _ _

omit [DecidableEq P] [DecidableEq T] in
lemma cut_nonempty (I : Finset (P × T)) (cell : P → Cell) (c : Cell)
    (hc : c∈I.image (fun e => cell e.1)) : (cut I cell c).Nonempty := by
  obtain ⟨e,he,hec⟩ := mem_image.mp hc
  exact ⟨e,mem_filter.mpr ⟨he,hec⟩⟩

lemma cut_full_tube_fiber (I : Finset (P × T)) (cell : P → Cell) (c : Cell)
    (p : P) (hp : cell p=c) : tubesAt (cut I cell c) p=tubesAt I p := by
  ext t
  rw [mem_tubesAt,mem_tubesAt]
  simp only [cut,mem_filter,hp,and_true]

omit [DecidableEq T] in
lemma cut_point_cell (I : Finset (P × T)) (cell : P → Cell) (c : Cell)
    (p : P) (hp : p∈TwoTubePathCollisionCount.points (cut I cell c)) : cell p=c := by
  obtain ⟨e,he,hep⟩ := mem_image.mp hp
  exact (congrArg cell hep).symm.trans (mem_filter.mp he).2

end NativeGraphPhysicalLocalization
