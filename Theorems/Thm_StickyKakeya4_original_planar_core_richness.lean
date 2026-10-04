import Theorems.Thm_StickyKakeya4_original_planar_chart_tube_energy
import Theorems.Thm_StickyKakeya4_original_tube_core_reinforcement
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
noncomputable section
open scoped BigOperators
namespace OriginalPlanarCoreRichness
open Classical OriginalPlanarTubePairCount OriginalPlanarTubeParameters OriginalPlanarTubeEnergy
open OriginalPlanarChartTubeEnergy OriginalTubeCoreReinforcement
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalAveragedSliceEnergy
abbrev Pair3 := Point3 × Point3

def stripPoints (Q : Finset Point3) (f : Point3 → ℝ × ℝ) (rho : ℝ) (e : Pair3) : Finset Point3 :=
  Q.filter (fun x => |(f x).2-(pairSlope (f e.1,f e.2)*(f x).1+pairOffset (f e.1,f e.2))| ≤ 2*rho)
def cellMap (f : Point3 → ℝ × ℝ) (h : ℝ) (e : Pair3) : TubeCell :=
  pairCell h (f e.1,f e.2)

/-- Actual ambient strip richness and the original slab energy construct
a dense graph rich in its retained CORE. Its tube labels are exactly the
rounded lines of original graph pairs, not an independently sampled family. -/
theorem exists_original_core_rich_planar_graph (Q S : Finset Point3)
    (G : Finset Pair3) (b : Frame3) (swap : Bool) (c h rho m ell : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hrho : rho ≤ h) (hm : 0 < m)
    (hSQ : S⊆Q) (hG : G⊆S.product S)
    (hbox : ∀ x∈Q,∀ j,|x j| ≤ 1)
    (hslab : ∀ x∈Q,|frameCoordinate b 2 x-c| ≤ h)
    (hne : ∀ e∈G,(chart swap (project b e.2)).1-(chart swap (project b e.1)).1 ≠ 0)
    (hmax : ∀ e∈G,|(chart swap (project b e.2)).2-(chart swap (project b e.1)).2| ≤
      |(chart swap (project b e.2)).1-(chart swap (project b e.1)).1|)
    (hrich : ∀ e∈G,m ≤ ((stripPoints Q (fun x => chart swap (project b x)) rho e).card : ℝ))
    (hbudget : 240000*sliceEnergy Q h*ell^2 ≤ m^2*G.card) :
    ∃ G' : Finset Pair3,G'⊆G ∧ (G.card : ℝ) ≤ 2*G'.card ∧
      ∀ e∈G',ell ≤ ((tubePoints S (fun x => chart swap (project b x)) h
        (cellMap (fun x => chart swap (project b x)) h e)).card : ℝ) := by
  let f : Point3 → ℝ × ℝ := fun x => chart swap (project b x)
  let assign := cellMap f h
  let T := G.image assign
  let region : TubeCell → Finset Point3 := tubePoints Q f h
  have hfbox (x : Point3) (hx : x∈Q) : |(f x).1| ≤ 3 ∧ |(f x).2| ≤ 3 :=
    original_chart_coordinate_bounds swap _ (original_projected_coordinate_bounds b x (hbox x hx))
  have hmap (e : Pair3) (he : e∈G) : assign e∈T := Finset.mem_image_of_mem _ he
  have hslope (z : TubeCell) (hz : z∈T) : |h*(z.1:ℝ)| ≤ 2 := by
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact original_pair_cell_slope h _ hh hh1 (hne e he) (hmax e he)
  have hassign (e : Pair3) (he : e∈G) : e.1∈region (assign e) ∧ e.2∈region (assign e) := by
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hG he)
    have hend := original_pair_endpoints_in_cell h (f e.1,f e.2) hh (hne e he)
      (hfbox e.1 (hSQ h1)).1 (hfbox e.2 (hSQ h2)).1
    exact ⟨Finset.mem_filter.mpr ⟨hSQ h1,hend.1⟩,Finset.mem_filter.mpr ⟨hSQ h2,hend.2⟩⟩
  have hQregion (z : TubeCell) : Q∩region z=region z :=
    Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hrichT (z : TubeCell) (hz : z∈T) : m ≤ ((Q∩region z).card : ℝ) := by
    rw [hQregion]
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    have hsub : stripPoints Q f rho e⊆region (assign e) := by
      intro x hx
      obtain ⟨hxQ,hstrip⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxQ,
        original_pair_strip_in_cell h rho _ (f x) hh hrho (hfbox x hxQ).1 hstrip⟩
    exact (hrich e he).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
  have henergy : (∑ z∈T,((Q∩region z).card : ℝ)^2) ≤ 120000*sliceEnergy Q h := by
    simp only [hQregion]
    exact original_chart_slab_tube_square_energy Q T b swap c h hh hh1 hbox hslab hslope
  obtain ⟨G',hG'G,hkeep,hpop⟩ := original_core_rich_graph Q S G T region assign
    m (120000*sliceEnergy Q h) ell hm hG hmap hassign hrichT henergy (by
      nlinarith only [hbudget])
  refine ⟨G',hG'G,hkeep,?_⟩
  intro e he
  have hset : S∩region (assign e)=tubePoints S f h (assign e) := by
    ext x
    simp only [Finset.mem_inter,region,tubePoints,Finset.mem_filter]
    exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx => ⟨hx.1,hSQ hx.1,hx.2⟩⟩
  change ell ≤ ((tubePoints S f h (assign e)).card : ℝ)
  rw [← hset]
  exact (hpop e he).2.2.2

end OriginalPlanarCoreRichness
