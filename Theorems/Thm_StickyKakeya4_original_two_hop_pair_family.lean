import Theorems.Thm_StickyKakeya4_original_two_hop_class_tube_transfer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped BigOperators
noncomputable section
namespace OriginalTwoHopPairFamily
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open NativeRadialClassPruning OriginalTwoHopClassTubeTransfer

/-- Literal original neighbour pairs reached by one reverse class and one
forward class. The intermediate original pair is retained as a witness. -/
def twoHopPairs (G : Finset Pair) (rho : ℝ) (z : Pair) : Finset Pair := by
  classical
  exact (G.filter (fun u => reverseClass rho u=reverseClass rho z)).biUnion
    (fun u => G.filter (fun v => forwardClass rho v=forwardClass rho u))

theorem mem_two_hop_pairs (G : Finset Pair) (rho : ℝ) (z v : Pair) :
    v∈twoHopPairs G rho z ↔ ∃ u∈G, reverseClass rho u=reverseClass rho z ∧
      v∈G ∧ forwardClass rho v=forwardClass rho u := by
  classical
  simp only [twoHopPairs,Finset.mem_biUnion,Finset.mem_filter]
  constructor
  · rintro ⟨u,⟨hu,hr⟩,hv,hf⟩
    exact ⟨u,hu,hr,hv,hf⟩
  · rintro ⟨u,hu,hr,hv,hf⟩
    exact ⟨u,⟨hu,hr⟩,hv,hf⟩

private theorem original_forward_fibers_disjoint (G : Finset Pair) (rho : ℝ) (z : Pair) :
    ((G.filter (fun u => reverseClass rho u=reverseClass rho z)):Set Pair).PairwiseDisjoint
      (fun u => G.filter (fun v => forwardClass rho v=forwardClass rho u)) := by
  classical
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro x hxu hxv
  have hfirst : u.1=v.1 := congrArg (fun c : ClassLabel => c.1)
    ((Finset.mem_filter.mp hxu).2.symm.trans (Finset.mem_filter.mp hxv).2)
  have hsecond : u.2=v.2 := congrArg (fun c : ClassLabel => c.1)
    ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  exact hne (Prod.ext hfirst hsecond)

/-- The actual two-sided rich classes construct at least 4k² DISTINCT
original neighbour pairs. No path count or multiplicity bound is assumed. -/
theorem original_two_hop_pair_count (G : Finset Pair) (rho k : ℝ) (z : Pair)
    (hk : 0≤k) (hz : z∈G)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ)) :
    4*k^2≤((twoHopPairs G rho z).card : ℝ) := by
  classical
  let U := G.filter (fun u => reverseClass rho u=reverseClass rho z)
  have hcard : (twoHopPairs G rho z).card=
      ∑ u∈U, (G.filter (fun v => forwardClass rho v=forwardClass rho u)).card :=
    Finset.card_biUnion (original_forward_fibers_disjoint G rho z)
  have hsum : (2*k)*(U.card : ℝ)≤((twoHopPairs G rho z).card : ℝ) := by
    calc
      _ = ∑ _u∈U, 2*k := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ ∑ u∈U, ((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact (hrich u (Finset.mem_filter.mp hu).1).1
      _ = _ := by exact_mod_cast hcard.symm
  have hU : 2*k≤(U.card : ℝ) := (hrich z hz).2
  have hm := mul_le_mul_of_nonneg_left hU (by positivity : 0≤2*k)
  nlinarith only [hsum,hm]

/-- Every actual neighbour pair remains in G and has BOTH original
endpoints in the original reference pair's 56rho physical support. This is
the local pair-charge input before a tube-family multiplicity argument. -/
theorem original_two_hop_pair_support
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z : Pair)
    (hrho : 0<rho) (hz : z∈G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2) :
    twoHopPairs G rho z⊆G ∧
    twoHopPairs G rho z⊆(physicalPairTube Pts (56*rho) z).product
      (physicalPairTube Pts (56*rho) z) := by
  classical
  have hmem (v : Pair) (hv : v∈twoHopPairs G rho z) : v∈G := by
    obtain ⟨_u,_hu,_hr,hvG,_hf⟩ := (mem_two_hop_pairs G rho z v).mp hv
    exact hvG
  refine ⟨hmem,?_⟩
  intro v hv
  obtain ⟨u,hu,hr,hvG,hf⟩ := (mem_two_hop_pairs G rho z v).mp hv
  have htransfer := original_reverse_forward_class_support_transfer Pts z u v rho hrho
    (Finset.mem_product.mp (hGP hz)).2 (Finset.mem_product.mp (hGP hu)).1 hbox
    (hdistinct z hz) (hdistinct u hu) (hdistinct v hvG) hr.symm hf.symm
  have hvPts := Finset.mem_product.mp (hGP hvG)
  have hfirst : v.1∈physicalPairTube Pts rho v := by
    apply Finset.mem_filter.mpr
    refine ⟨hvPts.1,0,?_⟩
    simpa only [linePoint,zero_mul,add_zero,euclideanDistance,sub_self,
      zero_pow (by decide : 2≠0),zero_add,Real.sqrt_zero] using hrho.le
  have hsecond : v.2∈physicalPairTube Pts rho v := by
    apply Finset.mem_filter.mpr
    refine ⟨hvPts.2,1,?_⟩
    have hline : linePoint v 1=v.2 := by apply Prod.ext <;> dsimp [linePoint] <;> ring
    rw [hline]
    simpa only [euclideanDistance,sub_self,zero_pow (by decide : 2≠0),zero_add,
      Real.sqrt_zero] using hrho.le
  exact Finset.mem_product.mpr ⟨htransfer hfirst,htransfer hsecond⟩

end OriginalTwoHopPairFamily
