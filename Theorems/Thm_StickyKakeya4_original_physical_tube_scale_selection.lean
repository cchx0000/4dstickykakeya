import Theorems.Thm_StickyKakeya4_original_physical_pair_tube
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open scoped BigOperators
noncomputable section
namespace OriginalPhysicalTubeScaleSelection
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion

def dyadicRadius (j : ℕ) : ℝ := (1/2)^j

def scaleMenu (n : ℕ) : Finset ℝ := (Finset.range (n+1)).image dyadicRadius

theorem physical_tube_mono (Pts : Finset Point) (z : Pair) {r R : ℝ} (h : r≤R) :
    physicalPairTube Pts r z⊆physicalPairTube Pts R z := by
  classical
  intro p hp
  obtain ⟨hpP,s,hs⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpP,s,hs.trans h⟩

theorem original_tube_card_bounds (Pts : Finset Point) (z : Pair) (r : ℝ)
    (hp : z.1∈Pts) (hr : 0≤r) :
    0<(physicalPairTube Pts r z).card ∧ (physicalPairTube Pts r z).card≤Pts.card := by
  classical
  constructor
  · apply Finset.card_pos.mpr
    refine ⟨z.1,Finset.mem_filter.mpr ⟨hp,0,?_⟩⟩
    simpa only [linePoint,zero_mul,add_zero,euclideanDistance,sub_self,
      zero_pow (by decide : 2≠0),zero_add,Real.sqrt_zero] using hr
  · exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The explicit finite dyadic menu covers every original radius above its
bottom scale, with a factor two and no change of original points. -/
theorem dyadic_radius_cover (n : ℕ) (r : ℝ)
    (hrlo : dyadicRadius n≤2*r) (hrhi : r≤1) :
    ∃ j≤n, r≤dyadicRadius j ∧ dyadicRadius j≤2*r := by
  classical
  let S := (Finset.range (n+1)).filter (fun j => r≤dyadicRadius j)
  have hS : S.Nonempty := ⟨0,Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),by simpa only [dyadicRadius,pow_zero] using hrhi⟩⟩
  let j := S.max' hS
  have hjS : j∈S := Finset.max'_mem _ _
  obtain ⟨hjrange,hrj⟩ := Finset.mem_filter.mp hjS
  have hj : j≤n := by have := Finset.mem_range.mp hjrange; omega
  refine ⟨j,hj,hrj,?_⟩
  by_cases hjn : j=n
  · rw [hjn]
    exact hrlo
  · have hjnext : j+1<n+1 := by omega
    have hnext : dyadicRadius (j+1)<r := by
      by_contra h
      have hm : j+1∈S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hjnext,le_of_not_gt h⟩
      have hh : j+1≤j := Finset.le_max' S (j+1) hm
      omega
    have heq : dyadicRadius (j+1)=dyadicRadius j/2 := by
      unfold dyadicRadius
      rw [pow_succ]
      ring
    rw [heq] at hnext
    linarith only [hnext]

/-- Maximum density uses the actual original-point physical tube counts. -/
def score (Pts : Finset Point) (sigma r : ℝ) (z : Pair) : ℝ :=
  (physicalPairTube Pts r z).card/r^sigma

def chosenScale (Pts : Finset Point) (S : Finset ℝ) (hS : S.Nonempty)
    (sigma : ℝ) (z : Pair) : ℝ :=
  Classical.choose (Finset.exists_max_image S (fun r => score Pts sigma r z) hS)

theorem chosen_scale_spec (Pts : Finset Point) (S : Finset ℝ) (hS : S.Nonempty)
    (sigma : ℝ) (z : Pair) :
    chosenScale Pts S hS sigma z∈S ∧
    ∀ r∈S, score Pts sigma r z≤score Pts sigma (chosenScale Pts S hS sigma z) z :=
  Classical.choose_spec (Finset.exists_max_image S (fun r => score Pts sigma r z) hS)

/-- Literal original labels are partitioned by their selected physical
radius and selected actual occupancy bin. -/
theorem exists_original_densest_graph_bin
    (Pts : Finset Point) (G : Finset Pair) (S : Finset ℝ) (sigma : ℝ)
    (hG : G.Nonempty) (hGP : G⊆Pts.product Pts) (hS : S.Nonempty)
    (hpos : ∀ r∈S, 0<r) :
    ∃ rho∈S, ∃ j : ℕ, j<Nat.log 2 Pts.card+1 ∧
      ∃ H : Finset Pair, H⊆G ∧ H.Nonempty ∧
      G.card≤S.card*(Nat.log 2 Pts.card+1)*H.card ∧
      ∀ z∈H, chosenScale Pts S hS sigma z=rho ∧
        2^j≤(physicalPairTube Pts rho z).card ∧
        (physicalPairTube Pts rho z).card<2^(j+1) ∧
        ∀ r∈S, score Pts sigma r z≤score Pts sigma rho z := by
  classical
  let f : Pair→ℝ×ℕ := fun z =>
    (chosenScale Pts S hS sigma z,Nat.log 2
      (physicalPairTube Pts (chosenScale Pts S hS sigma z) z).card)
  let Labels := S.product (Finset.range (Nat.log 2 Pts.card+1))
  have hf (z : Pair) (hz : z∈G) : f z∈Labels := by
    have hr := (chosen_scale_spec Pts S hS sigma z).1
    have hcount := (original_tube_card_bounds Pts z _
      (Finset.mem_product.mp (hGP hz)).1 (hpos _ hr).le).2
    apply Finset.mem_product.mpr
    refine ⟨hr,Finset.mem_range.mpr ?_⟩
    exact Nat.lt_succ_of_le (Nat.log_mono_right (b:=2) hcount)
  have hLabels : Labels.Nonempty := ⟨f hG.choose,hf _ hG.choose_spec⟩
  obtain ⟨label,hlabel,hmax⟩ := Finset.exists_max_image Labels
    (fun y => (G.filter (fun z => f z=y)).card) hLabels
  let H := G.filter (fun z => f z=label)
  have hsum : ∑ y∈Labels, (G.filter (fun z => f z=y)).card=G.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hf
  have hmass : G.card≤Labels.card*H.card := by
    calc
      _ = ∑ y∈Labels, (G.filter (fun z => f z=y)).card := hsum.symm
      _ ≤ ∑ _y∈Labels, H.card := Finset.sum_le_sum (fun y hy => hmax y hy)
      _ = _ := by simp
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    have hg := hG.card_pos
    by_contra hh
    have hh0 : H.card=0 := by omega
    rw [hh0,mul_zero] at hmass
    omega
  obtain ⟨hrho,hj⟩ := Finset.mem_product.mp hlabel
  refine ⟨label.1,hrho,label.2,Finset.mem_range.mp hj,H,Finset.filter_subset _ _,hH,?_,?_⟩
  · simpa only [Labels,Finset.product_eq_sprod,Finset.card_product,Finset.card_range] using hmass
  · intro z hz
    obtain ⟨hzG,hzf⟩ := Finset.mem_filter.mp hz
    have hscale : chosenScale Pts S hS sigma z=label.1 := congrArg Prod.fst hzf
    have hlevel : Nat.log 2 (physicalPairTube Pts label.1 z).card=label.2 := by
      have h := congrArg Prod.snd hzf
      dsimp [f] at h
      simpa only [hscale] using h
    have hcount := original_tube_card_bounds Pts z label.1
      (Finset.mem_product.mp (hGP hzG)).1 (hpos _ hrho).le
    refine ⟨hscale,?_,?_,?_⟩
    · rw [← hlevel]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hcount.1)
    · rw [← hlevel]
      exact Nat.lt_pow_succ_log_self (by decide) _
    · simpa only [hscale] using (chosen_scale_spec Pts S hS sigma z).2

end OriginalPhysicalTubeScaleSelection
