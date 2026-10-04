import Theorems.Thm_StickyKakeya4_original_planar_tube_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace OriginalPlanarTubeChart
open Classical OriginalPlanarTubePairCount OriginalPlanarTubeParameters

def chartPairs {α : Type*} (G : Finset (α × α)) (f : α → Point2) (swap : Bool) :
    Finset (α × α) := G.filter (fun e =>
      (chart swap (f e.2)).1-(chart swap (f e.1)).1 ≠ 0 ∧
      |(chart swap (f e.2)).2-(chart swap (f e.1)).2| ≤
        |(chart swap (f e.2)).1-(chart swap (f e.1)).1|)

/-- One literal coordinate chart keeps at least half the actual original
ordered graph. No new endpoints or edges are introduced. -/
theorem exists_original_common_planar_chart {α : Type*} (G : Finset (α × α))
    (f : α → Point2) (hne : ∀ e∈G,f e.1 ≠ f e.2) :
    ∃ swap : Bool,chartPairs G f swap⊆G ∧ G.card ≤ 2*(chartPairs G f swap).card := by
  have hc : G⊆chartPairs G f false ∪ chartPairs G f true := by
    intro e he
    obtain ⟨b,hb⟩ := exists_original_pair_chart (f e.1) (f e.2) (hne e he)
    cases b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,hb⟩)
  have hn := (Finset.card_le_card hc).trans (Finset.card_union_le _ _)
  by_cases h : (chartPairs G f false).card ≤ (chartPairs G f true).card
  · exact ⟨true,Finset.filter_subset _ _,by omega⟩
  · exact ⟨false,Finset.filter_subset _ _,by omega⟩

/-- Every actual pair in a common chart has its own literal tube cell,
whose slope lies in the fixed compact slope interval. -/
theorem original_chart_cell_slope {α : Type*} (G : Finset (α × α))
    (f : α → Point2) (swap : Bool) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ e∈chartPairs G f swap,
      |h*((pairCell h (chart swap (f e.1),chart swap (f e.2))).1:ℝ)| ≤ 2 := by
  intro e he
  obtain ⟨_heG,hne,hmax⟩ := Finset.mem_filter.mp he
  exact original_pair_cell_slope h _ hh hh1 hne hmax

end OriginalPlanarTubeChart
