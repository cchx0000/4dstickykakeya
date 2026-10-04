import Theorems.Thm_StickyKakeya4_original_line_residue_separation
import Theorems.Thm_StickyKakeya4_original_line_cell_source_mass
import Mathlib.Combinatorics.Pigeonhole

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

open scoped BigOperators
noncomputable section
namespace OriginalWeightedLineColorSelection
open Classical OriginalPairStripGeometry OriginalUnitLineGrid OriginalLineCellSourceMass
open OriginalLineResidueSeparation OriginalClippedUnitTube

def originalCellGraph (G S : Finset Pair) (rho : ℝ) : Finset Pair :=
  G.filter (fun z => lineCell rho z∈S.image (lineCell rho))

/-- Selected actual cells retain their full original pair fibers. -/
theorem original_selected_cell_graph_card (G S : Finset Pair) (rho : ℝ)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair)) :
    (originalCellGraph G S rho).card=
      ∑ u∈S, (G.filter (fun z => lineCell rho z=lineCell rho u)).card := by
  unfold originalCellGraph
  rw [← Finset.sum_card_fiberwise_eq_card_filter G (S.image (lineCell rho)) (lineCell rho)]
  exact Finset.sum_image (fun u hu v hv heq => hinj hu hv heq)

/-- Choose chart and residue color by ORIGINAL pair-fiber weight. The
retained graph contains whole source cell fibers and loses at most 4M³. -/
theorem exists_original_weighted_line_color
    (G R : Finset Pair) (rho : ℝ) (M : ℕ) (hM : 0<M)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (himage : R.image (lineCell rho)=G.image (lineCell rho)) :
    ∃ S : Finset Pair, S⊆R ∧
      (∀ z∈S, ∀ u∈S, lineColor rho M z=lineColor rho M u) ∧
      G.card≤4*M^3*(originalCellGraph G S rho).card := by
  let weights := fun u => (G.filter (fun z => lineCell rho z=lineCell rho u)).card
  let totals := fun c => ∑ u∈R.filter (fun z => lineColor rho M z=c), weights u
  have hmenu : (lineColors M).Nonempty :=
    ⟨lineColor rho M ((0,0),(0,0)),original_line_color_mem rho M hM _⟩
  obtain ⟨c,hc,hmax⟩ := Finset.exists_max_image (lineColors M) totals hmenu
  let S := R.filter (fun z => lineColor rho M z=c)
  have hS : S⊆R := Finset.filter_subset _ _
  have hweight : G.card≤(lineColors M).card*totals c := by
    calc
      _ = ∑ u∈R, weights u := original_line_representative_fiber_partition G R rho hinj himage
      _ = ∑ d∈lineColors M, totals d := by
        exact (Finset.sum_fiberwise_of_maps_to (s:=R) (fun z _ => original_line_color_mem rho M hM z) weights).symm
      _ ≤ ∑ _d∈lineColors M, totals c := Finset.sum_le_sum (fun d hd => hmax d hd)
      _ = _ := by simp
  refine ⟨S,hS,?_,?_⟩
  · intro z hz u hu
    exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hu).2.symm
  · rw [line_colors_card] at hweight
    rw [original_selected_cell_graph_card G S rho
      (fun _ hz _ hu heq => hinj (hS hz) (hS hu) heq)]
    exact hweight

/-- Actual weighted thinning produces separated clipped physical tubes.
Every retained label is an original representative and every retained
source pair remains in its full original cell fiber. -/
theorem exists_weighted_clipped_original_family
    (Pts : Finset Point) (G R : Finset Pair) (rho w : ℝ) (M : ℕ)
    (hrho : 0<rho) (hw : 0≤w) (hM : 0<M)
    (hmesh : 36*w<((M:ℝ)-1)*rho) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (himage : R.image (lineCell rho)=G.image (lineCell rho))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2) :
    ∃ S : Finset Pair, S⊆R ∧
      (∀ z∈S, ∀ u∈S, lineColor rho M z=lineColor rho M u) ∧
      G.card≤4*M^3*(originalCellGraph G S rho).card ∧
      ∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z w, 2*w< |scaledResidual u p| := by
  obtain ⟨S,hS,hcolor,hweight⟩ := exists_original_weighted_line_color G R rho M hM hinj himage
  refine ⟨S,hS,hcolor,hweight,?_⟩
  intro z hz u hu hne
  exact original_same_color_clipped_distinct rho w M z u hrho hw hM hmesh
    (hdistinct z (hR (hS hz))) (hdistinct u (hR (hS hu)))
    (hbox z.1 (Finset.mem_product.mp (hGP (hR (hS hz)))).1)
    (hcolor z hz u hu) (fun heq => hne (hinj (hS hz) (hS hu) heq))

end OriginalWeightedLineColorSelection
