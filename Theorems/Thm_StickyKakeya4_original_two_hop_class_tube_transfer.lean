import Theorems.Thm_StickyKakeya4_bounded_original_angle_tube_transfer
import Theorems.Thm_StickyKakeya4_native_radial_class_geometry
import Theorems.Thm_StickyKakeya4_original_annular_graph_deletion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalTwoHopClassTubeTransfer
open OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open NativeRadialClassGeometry BoundedOriginalAngleTubeTransfer OriginalAnnularGraphDeletion

/-- Two actual same-root angle steps, with the intermediate original line
reversed, transfer bounded original support through widths rho, 12rho,
and 56rho. Both original angle comparisons remain explicit. -/
theorem original_two_hop_angle_support_transfer
    (Pts : Finset Point) (p a b c : Point) (rho : ℝ)
    (hrho : 0≤rho) (hp : p∈Pts) (hb : b∈Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hpa : p≠a) (hpb : p≠b) (hbc : b≠c)
    (hangle1 : |radialAngle p a-radialAngle p b|≤rho)
    (hangle2 : |radialAngle b p-radialAngle b c|≤rho) :
    physicalPairTube Pts rho (p,a)⊆physicalPairTube Pts (56*rho) (b,c) := by
  have hfirst := original_bounded_same_root_support_transfer Pts p a b rho rho
    hrho hp hbox hpa hpb hangle1
  have hsecond := original_bounded_same_root_support_transfer Pts b p c (12*rho) rho
    hrho hb hbox hpb.symm hbc hangle2
  rw [show 4*rho+8*rho=12*rho by ring] at hfirst
  rw [show 4*(12*rho)+8*rho=56*rho by ring] at hsecond
  intro v hv
  have hmid := hfirst hv
  have hmid' : v∈physicalPairTube Pts (12*rho) (b,p) := by
    change v∈physicalPairTube Pts (12*rho) (p,b).swap
    simpa only [physical_pair_tube_swap] using hmid
  exact hsecond hmid'

/-- The original reverse class followed by the original forward class is
the actual two-hop configuration in A.1 (235). Every original point in the
neighbour's rho-tube lies in the reference pair's 56rho-tube. This follows
from the literal angle bins, not from a line-proximity premise. -/
theorem original_reverse_forward_class_support_transfer
    (Pts : Finset Point) (z u v : Pair) (rho : ℝ)
    (hrho : 0<rho) (hzroot : z.2∈Pts) (huroot : u.1∈Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hz : z.1≠z.2) (hu : u.1≠u.2) (hv : v.1≠v.2)
    (hreverse : reverseClass rho z=reverseClass rho u)
    (hforward : forwardClass rho u=forwardClass rho v) :
    physicalPairTube Pts rho v⊆physicalPairTube Pts (56*rho) z := by
  rcases z with ⟨p,a⟩
  rcases u with ⟨q,b⟩
  rcases v with ⟨r,c⟩
  obtain ⟨hroot1,hangle1⟩ := reverse_class_geometry rho hrho (p,a) (q,b) hreverse
  change a=b at hroot1
  subst b
  obtain ⟨hroot2,hangle2⟩ := forward_class_geometry rho hrho (q,a) (r,c) hforward
  change q=r at hroot2
  subst r
  have hang1 : |radialAngle q c-radialAngle q a|≤rho := by
    simpa only [abs_sub_comm] using hangle2.le
  have hang2 : |radialAngle a q-radialAngle a p|≤rho := by
    simpa only [abs_sub_comm] using hangle1.le
  have htransfer := original_two_hop_angle_support_transfer Pts q c a p rho hrho.le
    huroot hzroot hbox hv hu hz.symm hang1 hang2
  intro x hx
  have hh := htransfer hx
  change x∈physicalPairTube Pts (56*rho) (p,a).swap at hh
  simpa only [physical_pair_tube_swap] using hh

end OriginalTwoHopClassTubeTransfer
