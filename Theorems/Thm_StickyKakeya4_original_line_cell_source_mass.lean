import Theorems.Thm_StickyKakeya4_original_line_cell_physical_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped BigOperators
noncomputable section
namespace OriginalLineCellSourceMass
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube
open OriginalUnitLineGrid OriginalUnitParameterPhysical OriginalLineCellPhysicalCover

/-- An actual parameter cell's original graph fiber is bounded by the
square of the original physical tube population, with both labels retained. -/
theorem original_line_cell_fiber_mass
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (u : Pair)
    (hrho : 0<rho) (hu : u.1≠u.2) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) :
    (G.filter (fun z => lineCell rho z=lineCell rho u)).card≤
      (physicalPairTube Pts (6*rho) u).card^2 := by
  have hsub : G.filter (fun z => lineCell rho z=lineCell rho u)⊆
      (physicalPairTube Pts (6*rho) u).product (physicalPairTube Pts (6*rho) u) := by
    intro z hz
    obtain ⟨hzG,heq⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx,hy,hc⟩ := original_same_cell_parameter_close rho z u hrho heq
    have hout := original_parameter_close_endpoints Pts z u rho rho hu (hGP hzG) hbox hx hy hc
    simpa only [show 4*rho+2*rho=6*rho by ring] using hout
  simpa only [Finset.product_eq_sprod,Finset.card_product,pow_two] using Finset.card_le_card hsub

/-- The representative weights partition the full ORIGINAL graph exactly.
This identity is suitable for later weighted thinning of representatives. -/
theorem original_line_representative_fiber_partition
    (G R : Finset Pair) (rho : ℝ)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (himage : R.image (lineCell rho)=G.image (lineCell rho)) :
    G.card=∑ u∈R, (G.filter (fun z => lineCell rho z=lineCell rho u)).card := by
  rw [Finset.card_eq_sum_card_image (lineCell rho) G,← himage]
  exact Finset.sum_image (fun u hu v hv heq => hinj hu hv heq)

/-- The original graph mass is covered by the actual representative tube
populations, the finite counting input behind (233). -/
theorem original_line_representative_source_mass
    (Pts : Finset Point) (G R : Finset Pair) (rho : ℝ)
    (hrho : 0<rho) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (himage : R.image (lineCell rho)=G.image (lineCell rho))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2) :
    G.card≤∑ u∈R, (physicalPairTube Pts (6*rho) u).card^2 := by
  rw [original_line_representative_fiber_partition G R rho hinj himage]
  exact Finset.sum_le_sum (fun u hu => original_line_cell_fiber_mass Pts G rho u
    hrho (hdistinct u (hR hu)) hGP hbox)

end OriginalLineCellSourceMass
