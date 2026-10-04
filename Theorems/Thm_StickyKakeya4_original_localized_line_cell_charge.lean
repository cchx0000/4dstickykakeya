import Theorems.Thm_StickyKakeya4_original_unit_parameter_physical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalLocalizedLineCellCharge
open Classical
open OriginalPairStripGeometry OriginalPhysicalPairTube OriginalUnitLineParameters
open OriginalTwoHopPairFamily OriginalUnitLineGrid OriginalLineRepresentativeCharge
open NativeRadialClassPruning OriginalUnitParameterPhysical

def parameterNear (W : ℝ) (a z : Pair) : Prop :=
  |unitX z-unitX a|≤W ∧ |unitY z-unitY a|≤W ∧ |unitOffset z-unitOffset a|≤W

/-- Actual class-hop line information puts the original two-hop endpoints
in the reference physical tube at width 6W+16rho. -/
theorem original_local_two_hop_physical_endpoints
    (Pts : Finset Point) (G : Finset Pair) (rho W : ℝ) (a z : Pair)
    (hrho : 0<rho) (ha : a.1≠a.2) (hz : z∈G)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2) (hnear : parameterNear W a z) :
    twoHopPairs G rho z⊆(physicalPairTube Pts (6*W+16*rho) a).product
      (physicalPairTube Pts (6*W+16*rho) a) := by
  intro v hv
  obtain ⟨u,hu,hr,hvG,hf⟩ := (mem_two_hop_pairs G rho z v).mp hv
  obtain ⟨hx,hy,hc⟩ := original_class_hops_parameter_close Pts z u v rho hrho
    (Finset.mem_product.mp (hGP hz)).2 (Finset.mem_product.mp (hGP hu)).1 hbox
    (hdistinct z hz) (hdistinct u hu) (hdistinct v hvG) hr.symm hf.symm
  have hxa : |unitX v-unitX a|≤2*rho+W :=
    (abs_sub_le (unitX v) (unitX z) (unitX a)).trans (by
      rw [abs_sub_comm (unitX v)]
      linarith only [hx,hnear.1])
  have hya : |unitY v-unitY a|≤2*rho+W :=
    (abs_sub_le (unitY v) (unitY z) (unitY a)).trans (by
      rw [abs_sub_comm (unitY v)]
      linarith only [hy,hnear.2.1])
  have hca : |unitOffset v-unitOffset a|≤4*rho+W :=
    (abs_sub_le (unitOffset v) (unitOffset z) (unitOffset a)).trans (by
      rw [abs_sub_comm (unitOffset v)]
      linarith only [hc,hnear.2.2])
  have hout := original_parameter_close_endpoints Pts v a (2*rho+W) (4*rho+W)
    ha (hGP hvG) hbox hxa hya hca
  simpa only [show 4*(2*rho+W)+2*(4*rho+W)=6*W+16*rho by ring] using hout

/-- The native localized count behind (238), on the literal line grid.
Its right side counts actual original points in a genuine physical tube;
no overlap or endpoint-containment budget is supplied. -/
theorem original_local_line_cell_charge
    (Pts : Finset Point) (G R : Finset Pair) (rho W k : ℝ) (a : Pair)
    (hrho : 0<rho) (hk : 0≤k) (ha : a.1≠a.2) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ)) :
    4*k^2*((R.filter (parameterNear W a)).card : ℝ)≤
      539*((physicalPairTube Pts (6*W+16*rho) a).card : ℝ)^2 := by
  classical
  exact localized_original_representative_pair_charge Pts
    (physicalPairTube Pts (6*W+16*rho) a) G (R.filter (parameterNear W a)) rho k
    hrho hk (fun _ hz => hR (Finset.mem_filter.mp hz).1)
    (fun _ hz _ hu heq => hinj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hu).1 heq)
    hGP hbox hdistinct hrich (fun z hz => original_local_two_hop_physical_endpoints
      Pts G rho W a z hrho ha (hR (Finset.mem_filter.mp hz).1) hGP hbox hdistinct
      (Finset.mem_filter.mp hz).2)

end OriginalLocalizedLineCellCharge
