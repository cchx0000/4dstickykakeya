import Theorems.Thm_StickyKakeya4_original_pair_strip_physical_bridge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace RootedSharedAnnularTubeTransfer
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open PlanarStripIntersection NativeRichPairTubeFamily OriginalPairStripPhysicalBridge

/-- Shared original root and actual annular point yield full physical
support containment in a selected original pair tube of width 38w/tau. -/
theorem rooted_original_shared_point_transfer
    (Pts : Finset Point) (p a b q v : Point) (w tau : ℝ)
    (hw : 0≤w) (htau : 0<tau) (htau1 : tau≤1)
    (hpa : p≠a) (hpb : p≠b) (hpP : p∈Pts)
    (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hqA : q∈physicalPairTube Pts w (p,a))
    (hqB : q∈physicalPairTube Pts w (p,b))
    (hsep : tau≤euclideanDistance p q)
    (hvA : v∈physicalPairTube Pts w (p,a)) :
    v∈physicalPairTube Pts (38*w/tau) (p,b) := by
  classical
  let i : Pair := (p,a)
  let j : Pair := (p,b)
  have hnA := original_pair_normalized i hpa
  have hnB := original_pair_normalized j hpb
  have hpA : |PlanarStripIntersection.residual (normalX i) (normalY i) (offset i) p|≤2*w := by
    rw [(original_pair_on_line i).1,abs_zero]
    positivity
  have hpB : |PlanarStripIntersection.residual (normalX j) (normalY j) (offset j) p|≤2*w := by
    rw [(original_pair_on_line j).1,abs_zero]
    positivity
  have hqA' := (Finset.mem_filter.mp (physical_pair_tube_subset Pts w i hpa hqA)).2
  have hqB' := (Finset.mem_filter.mp (physical_pair_tube_subset Pts w j hpb hqB)).2
  have hvA' := (Finset.mem_filter.mp (physical_pair_tube_subset Pts w i hpa hvA)).2
  have hvP := (Finset.mem_filter.mp hvA).1
  let D := determinant (normalX i) (normalY i) (normalX j) (normalY j)
  have hcoords := common_point_coordinate_bounds
    (normalX i) (normalY i) (normalX j) (normalY j) (offset i) (offset j)
    (2*w) p q (by positivity) hnA.1 hnA.2.1 hnB.1 hnB.2.1 hpA hqA' hpB hqB'
  change |D| * |q.1-p.1| ≤ 4*(2*w) ∧ |D| * |q.2-p.2| ≤ 4*(2*w) at hcoords
  have hmax : |D| * boxDistance p q≤8*w := by
    unfold boxDistance
    rcases le_total |q.1-p.1| |q.2-p.2| with h|h
    · rw [max_eq_right h]
      nlinarith only [hcoords.2]
    · rw [max_eq_left h]
      nlinarith only [hcoords.1]
  have hsepbox := hsep.trans (euclidean_le_two_box p q)
  have hdet : |D|≤16*w/tau := by
    apply (le_div_iff₀ htau).mpr
    have hh := mul_le_mul_of_nonneg_left hsepbox (abs_nonneg D)
    nlinarith only [hh,hmax]
  have hx : |v.1-p.1|≤2 :=
    (abs_sub _ _).trans (by linarith only [(hbox v hvP).1,(hbox p hpP).1])
  have hy : |v.2-p.2|≤2 :=
    (abs_sub _ _).trans (by linarith only [(hbox v hvP).2,(hbox p hpP).2])
  have hcontain := bounded_strip_containment
    (normalX i) (normalY i) (normalX j) (normalY j) (offset i) (offset j)
    (2*w) p v hnA.2.2 hnB.1 hnB.2.1 hpA hvA' hpB hx hy
  have hwdiv : w≤w/tau := by
    apply (le_div_iff₀ htau).mpr
    nlinarith only [mul_le_mul_of_nonneg_left htau1 hw]
  have hres : |PlanarStripIntersection.residual (normalX j) (normalY j) (offset j) v|≤38*w/tau := by
    change |PlanarStripIntersection.residual (normalX j) (normalY j) (offset j) v|≤3*(2*w)+2* |D| at hcontain
    simp only [mul_div_assoc] at hdet ⊢
    nlinarith only [hcontain,hdet,hwdiv]
  exact original_strip_subset_physical Pts (38*w/tau) j hpb
    (Finset.mem_filter.mpr ⟨hvP,hres⟩)
end RootedSharedAnnularTubeTransfer
