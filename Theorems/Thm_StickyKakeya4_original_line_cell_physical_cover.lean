import Theorems.Thm_StickyKakeya4_original_unit_parameter_physical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalLineCellPhysicalCover
open OriginalPairStripGeometry OriginalPhysicalPairTube OriginalUnitLineParameters
open OriginalUnitLineGrid OriginalLineRepresentativeCharge OriginalUnitParameterPhysical
open NativeRadialClassPruning

private theorem same_floor_close (x y rho : ℝ) (hrho : 0<rho)
    (heq : ⌊x/rho⌋=⌊y/rho⌋) : |x-y|≤rho := by
  have hxlo := (le_div_iff₀ hrho).mp (Int.floor_le (x/rho))
  have hxhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (x/rho))
  have hylo := (le_div_iff₀ hrho).mp (Int.floor_le (y/rho))
  have hyhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (y/rho))
  rw [← heq] at hylo hyhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem original_same_cell_parameter_close (rho : ℝ) (z u : Pair)
    (hrho : 0<rho) (heq : lineCell rho z=lineCell rho u) :
    |unitX z-unitX u|≤rho ∧ |unitY z-unitY u|≤rho ∧
    |unitOffset z-unitOffset u|≤rho := by
  exact ⟨same_floor_close _ _ rho hrho (congrArg (fun c : LineCell => c.1) heq),
    same_floor_close _ _ rho hrho (congrArg (fun c : LineCell => c.2.1) heq),
    same_floor_close _ _ rho hrho (congrArg (fun c : LineCell => c.2.2) heq)⟩

/-- One literal cell representative covers all original bounded rho-tube
support assigned to its parameter cell, at physical width 10rho. -/
theorem original_same_cell_physical_cover (Pts : Finset Point) (rho : ℝ) (z u : Pair)
    (hrho : 0<rho) (hz : z.1≠z.2) (hu : u.1≠u.2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (heq : lineCell rho z=lineCell rho u) :
    physicalPairTube Pts rho z⊆physicalPairTube Pts (10*rho) u := by
  obtain ⟨hx,hy,hc⟩ := original_same_cell_parameter_close rho z u hrho heq
  have hh := original_parameter_support_transfer Pts z u rho rho rho hz hu hbox hx hy hc
  simpa only [show 4*rho+4*rho+2*rho=10*rho by ring] using hh

/-- A finite family of original pair lines simultaneously has literal
cell assignment, physical support covering, and the proved global charge. -/
theorem exists_charged_original_physical_cover
    (Pts : Finset Point) (G : Finset Pair) (rho k : ℝ)
    (hrho : 0<rho) (hk : 0≤k)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ)) :
    ∃ R : Finset Pair, R⊆G ∧ Set.InjOn (lineCell rho) (↑R : Set Pair) ∧
      R.image (lineCell rho)=G.image (lineCell rho) ∧
      4*k^2*(R.card : ℝ)≤539*(G.card : ℝ) ∧
      ∀ z∈G, ∃ u∈R, lineCell rho z=lineCell rho u ∧
        physicalPairTube Pts rho z⊆physicalPairTube Pts (10*rho) u := by
  classical
  obtain ⟨R,hR,hi,heq,hcharge⟩ := exists_charged_original_line_representatives
    Pts G rho k hrho hk hGP hbox hdistinct hrich
  refine ⟨R,hR,hi,heq,hcharge,?_⟩
  intro z hz
  have hcell : lineCell rho z∈R.image (lineCell rho) := by
    rw [heq]
    exact Finset.mem_image_of_mem _ hz
  obtain ⟨u,hu,hu_eq⟩ := Finset.mem_image.mp hcell
  exact ⟨u,hu,hu_eq.symm,original_same_cell_physical_cover Pts rho z u hrho
    (hdistinct z hz) (hdistinct u (hR hu)) hbox hu_eq.symm⟩

end OriginalLineCellPhysicalCover
