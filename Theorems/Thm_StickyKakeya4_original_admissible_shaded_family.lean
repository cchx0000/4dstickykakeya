import Theorems.Thm_StickyKakeya4_original_weighted_line_color_selection
import Theorems.Thm_StickyKakeya4_original_clipped_tube_cap_charge
import Theorems.Thm_StickyKakeya4_original_clipped_tube_representation
import Theorems.Thm_StickyKakeya4_original_arbitrary_strip_cap_charge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
namespace OriginalAdmissibleShadedFamily
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalUnitLineGrid OriginalLineRepresentativeCharge OriginalRepresentativeShading
open OriginalClippedUnitTube OriginalLineResidueSeparation OriginalWeightedLineColorSelection
open OriginalClippedTubeRepresentation OriginalClippedTubeCapCharge

/-- Construct the actual finite physical rectangle family and its literal
original shadings. Weighted chart/color thinning retains original graph
fibers. Separation and the external physical cap charge are derived. -/
theorem exists_original_admissible_shaded_family
    (Pts : Finset Point) (G : Finset Pair) (rho w k : ℝ) (M : ℕ)
    (hrho : 0<rho) (hwidth : 3*rho≤w) (hk : 0≤k) (hM : 0<M)
    (hmesh : 36*w<((M:ℝ)-1)*rho)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) :
    ∃ S : Finset Pair, S⊆G ∧ originalCellGraph G S rho⊆G ∧
      G.card≤4*M^3*(originalCellGraph G S rho).card ∧
      Set.InjOn (lineCell rho) (↑S : Set Pair) ∧
      (∀ z∈S, ∀ u∈S, normalChart z=normalChart u) ∧
      (S.image (fun z => clippedTube z w)).card=S.card ∧
      (∀ z∈S, ∀ u∈S, z≠u → ∃ p∈clippedTube z w, 2*w< |scaledResidual u p|) ∧
      (∀ z∈S,
        2*k≤(((originalShading Pts G rho z).image halfPoint).card : ℝ) ∧
        ↑((originalShading Pts G rho z).image halfPoint)⊆clippedTube z w) ∧
      4*k^2*(S.card : ℝ)≤539*(G.card : ℝ) ∧
      ∀ (W : ℝ) (u a : Pair), W≤1/4 → u.1≠u.2 → a∈containedClipped S w W u →
        4*k^2*((containedClipped S w W u).card : ℝ)≤
          539*((physicalPairTube Pts (432*W+16*rho) a).card : ℝ)^2 := by
  have hw : 0≤w := by linarith only [hrho,hwidth]
  obtain ⟨R,hR,hinj,himage⟩ := exists_original_line_cell_representatives G rho
  obtain ⟨S,hSR,hcolor,hweight,hsep⟩ := exists_weighted_clipped_original_family Pts G R rho w M
    hrho hw hM hmesh hR hinj himage hGP hbox hdistinct
  have hSG : S⊆G := hSR.trans hR
  have hSInj : Set.InjOn (lineCell rho) (↑S : Set Pair) :=
    fun _ hz _ hu heq => hinj (hSR hz) (hSR hu) heq
  have hphysicalInj : Set.InjOn (fun z => clippedTube z w) (↑S : Set Pair) := by
    intro z hz u hu heq
    by_contra hne
    obtain ⟨p,hp,hfar⟩ := hsep z hz u hu hne
    change clippedTube z w=clippedTube u w at heq
    rw [heq] at hp
    have hnear := hp.1
    linarith only [hfar,hnear,hw]
  refine ⟨S,hSG,Finset.filter_subset _ _,hweight,hSInj,
    (fun z hz u hu => congrArg (fun c : LineColor => c.1) (hcolor z hz u hu)),
    Finset.card_image_iff.mpr hphysicalInj,hsep,?_,?_,?_⟩
  · intro z hz
    constructor
    · rw [original_half_shading_card]
      exact original_representative_shading_lower Pts G rho k z hrho (hSG hz)
        hGP hbox hdistinct (hrich z (hSG hz)).2
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      have hpT := original_shading_half_mem_clipped Pts G rho z p (hdistinct z (hSG hz)) hbox hp
      exact ⟨hpT.1.trans hwidth,hpT.2⟩
  · exact original_representative_pair_charge Pts G S rho k hrho hk hSG hSInj
      hGP hbox hdistinct hrich
  · intro W u a hW hu ha
    exact original_clipped_cap_pair_charge Pts G S rho w W k u a hrho hw hW hk hu ha
      hSG hSInj (fun z hz v hv => congrArg (fun c : LineColor => c.1) (hcolor z hz v hv))
      hGP hbox hdistinct hrich

end OriginalAdmissibleShadedFamily
