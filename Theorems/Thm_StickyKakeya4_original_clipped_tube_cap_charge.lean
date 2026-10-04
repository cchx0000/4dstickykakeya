import Theorems.Thm_StickyKakeya4_original_external_tube_cap_geometry
import Theorems.Thm_StickyKakeya4_original_line_residue_separation
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalClippedTubeCapCharge
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalUnitLineGrid OriginalLineResidueSeparation OriginalClippedUnitTube
open OriginalLocalizedLineCellCharge OriginalExternalTubeCapGeometry

def containedClipped (S : Finset Pair) (w W : ℝ) (u : Pair) : Finset Pair :=
  S.filter (fun z => clippedTube z w⊆clippedTube u W)

/-- Literal physical tube containment implies the original-point cap
charge. The ambient cap line is arbitrary; the reference a is an actual
contained original representative. -/
theorem original_clipped_cap_pair_charge
    (Pts : Finset Point) (G S : Finset Pair) (rho w W k : ℝ) (u a : Pair)
    (hrho : 0<rho) (hw : 0≤w) (hW : W≤1/4) (hk : 0≤k)
    (hu : u.1≠u.2) (ha : a∈containedClipped S w W u) (hS : S⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hchart : ∀ z∈S, ∀ v∈S, normalChart z=normalChart v)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) :
    4*k^2*((containedClipped S w W u).card : ℝ)≤
      539*((physicalPairTube Pts (432*W+16*rho) a).card : ℝ)^2 := by
  have haS := (Finset.mem_filter.mp ha).1
  have hsub : containedClipped S w W u⊆S.filter (parameterNear (72*W) a) := by
    intro z hz
    obtain ⟨hzS,hzcontain⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzS,?_⟩
    exact original_common_external_strip_parameter_close z a u w W hw hW
      (hdistinct z (hS hzS)) (hdistinct a (hS haS)) hu
      (hbox z.1 (Finset.mem_product.mp (hGP (hS hzS))).1) (hchart z hzS a haS)
      (fun p hp => (hzcontain hp).1) (fun p hp => ((Finset.mem_filter.mp ha).2 hp).1)
  have hcount := original_local_line_cell_charge Pts G S rho (72*W) k a hrho hk
    (hdistinct a (hS haS)) hS hinj hGP hbox hdistinct hrich
  have hcard : ((containedClipped S w W u).card : ℝ)≤
      ((S.filter (parameterNear (72*W) a)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hout := (mul_le_mul_of_nonneg_left hcard (by positivity : 0≤4*k^2)).trans hcount
  simpa only [show 6*(72*W)+16*rho=432*W+16*rho by ring] using hout

end OriginalClippedTubeCapCharge
