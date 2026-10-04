import Theorems.Thm_StickyKakeya4_original_line_cell_physical_cover
import Theorems.Thm_StickyKakeya4_original_localized_line_cell_charge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalRepresentativeShading
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open NativeRadialClassGeometry OriginalUnitLineParameters OriginalUnitParameterPhysical
open OriginalLocalizedLineCellCharge

/-- Original roots with an actual original partner whose unit-line
parameters lie near the reference original pair. -/
def originalShading (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z : Pair) : Finset Point :=
  Pts.filter (fun p => ∃ q, (p,q)∈G ∧ parameterNear (2*rho) z (p,q))

private theorem reverse_class_parameter_near
    (Pts : Finset Point) (rho : ℝ) (z u : Pair)
    (hrho : 0<rho) (hzroot : z.2∈Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hz : z.1≠z.2) (hu : u.1≠u.2)
    (heq : reverseClass rho u=reverseClass rho z) :
    parameterNear (2*rho) z u := by
  obtain ⟨hroot,hang⟩ := reverse_class_geometry rho hrho z u heq.symm
  have hh := original_same_root_parameter_close z.2 z.1 u.1 rho hz.symm
    (by simpa only [hroot] using hu.symm) (hbox z.2 hzroot)
    (by simpa only [hroot] using hang.le)
  have he : (z.2,u.1)=u.swap := Prod.ext hroot rfl
  change |unitX z.swap-unitX (z.2,u.1)|≤rho ∧
    |unitY z.swap-unitY (z.2,u.1)|≤rho ∧
    |unitOffset z.swap-unitOffset (z.2,u.1)|≤2*rho at hh
  rw [he,(original_unit_parameter_swap z).1,(original_unit_parameter_swap u).1,
    (original_unit_parameter_swap z).2.1,(original_unit_parameter_swap u).2.1,
    (original_unit_parameter_swap z).2.2,(original_unit_parameter_swap u).2.2,
    neg_sub_neg,neg_sub_neg,neg_sub_neg] at hh
  exact ⟨by linarith only [hh.1,hrho],by linarith only [hh.2.1,hrho],hh.2.2⟩

/-- The reverse class supplies distinct ORIGINAL shaded roots. This gives
(231) for the actual parameter-assigned family without a shading-mass premise. -/
theorem original_representative_shading_lower
    (Pts : Finset Point) (G : Finset Pair) (rho k : ℝ) (z : Pair)
    (hrho : 0<rho) (hz : z∈G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : 2*k≤((G.filter (fun u => reverseClass rho u=reverseClass rho z)).card : ℝ)) :
    2*k≤((originalShading Pts G rho z).card : ℝ) := by
  have hcard : (G.filter (fun u => reverseClass rho u=reverseClass rho z)).card≤
      (originalShading Pts G rho z).card := by
    apply Finset.card_le_card_of_injOn (fun u : Pair => u.1)
    · intro u hu
      obtain ⟨huG,heq⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hGP huG)).1,u.2,huG,
        reverse_class_parameter_near Pts rho z u hrho
          (Finset.mem_product.mp (hGP hz)).2 hbox (hdistinct z hz) (hdistinct u huG) heq⟩
    · intro u hu v hv heq
      apply Prod.ext heq
      exact congrArg (fun c : ClassLabel => c.1)
        ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  exact hrich.trans (Nat.cast_le.mpr hcard)

/-- The constructed original shading is supported in the actual reference
physical tube, with fixed width 12rho on the bounded source. -/
theorem original_representative_shading_support
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z : Pair)
    (hz : z.1≠z.2) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) :
    originalShading Pts G rho z⊆physicalPairTube Pts (12*rho) z := by
  intro p hp
  obtain ⟨_hpP,q,hqG,hnear⟩ := Finset.mem_filter.mp hp
  have hh := original_parameter_close_endpoints Pts (p,q) z (2*rho) (2*rho)
    hz (hGP hqG) hbox hnear.1 hnear.2.1 hnear.2.2
  have hout := (Finset.mem_product.mp hh).1
  simpa only [show 4*(2*rho)+2*(2*rho)=12*rho by ring] using hout

/-- Every shaded original center has a literal original partner. The whole
shading lies in that partner line's 24rho physical tube, ready for the
retained original annular ball profile centered at this same point. -/
theorem original_shading_center_tube_witness
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z : Pair) (p : Point)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hp : p∈originalShading Pts G rho z) :
    ∃ q, (p,q)∈G ∧ originalShading Pts G rho z⊆physicalPairTube Pts (24*rho) (p,q) := by
  obtain ⟨_hpP,q,hqG,hqnear⟩ := Finset.mem_filter.mp hp
  refine ⟨q,hqG,?_⟩
  intro x hx
  obtain ⟨_hxP,y,hyG,hynear⟩ := Finset.mem_filter.mp hx
  have hX : |unitX (x,y)-unitX (p,q)|≤4*rho :=
    (abs_sub_le (unitX (x,y)) (unitX z) (unitX (p,q))).trans (by
      rw [abs_sub_comm (unitX z)]
      linarith only [hynear.1,hqnear.1])
  have hY : |unitY (x,y)-unitY (p,q)|≤4*rho :=
    (abs_sub_le (unitY (x,y)) (unitY z) (unitY (p,q))).trans (by
      rw [abs_sub_comm (unitY z)]
      linarith only [hynear.2.1,hqnear.2.1])
  have hC : |unitOffset (x,y)-unitOffset (p,q)|≤4*rho :=
    (abs_sub_le (unitOffset (x,y)) (unitOffset z) (unitOffset (p,q))).trans (by
      rw [abs_sub_comm (unitOffset z)]
      linarith only [hynear.2.2,hqnear.2.2])
  have hh := original_parameter_close_endpoints Pts (x,y) (p,q) (4*rho) (4*rho)
    (hdistinct (p,q) hqG) (hGP hyG) hbox hX hY hC
  have hout := (Finset.mem_product.mp hh).1
  simpa only [show 4*(4*rho)+2*(4*rho)=24*rho by ring] using hout

end OriginalRepresentativeShading
