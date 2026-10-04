import Theorems.Thm_StickyKakeya4_original_angular_tube_incidence
import Theorems.Thm_StickyKakeya4_finite_plane_projection_representatives
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace OriginalAngularClassPopulation
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalAngularTubeIncidence FinitePlaneProjectionGrid PlanarFrostmanBallConversion
open scoped BigOperators

/-- Original far tube points pay for every occupied angle class of one
fixed root. The representatives and all incidence counts are constructed. -/
theorem root_original_angle_population (P Q : Finset Point) (p : Point)
    {rho tau m : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1)
    (hne : ∀ q∈Q, p≠q)
    (hmass : ∀ q∈Q, m≤(((physicalPairTube P rho (p,q)).filter
      (fun v => tau≤euclideanDistance p v)).card : ℝ)) :
    m*((Q.image (fun q => ⌊radialAngle p q/rho⌋)).card : ℝ) ≤100/tau*P.card := by
  obtain ⟨S,hSQ,_himage,hinj,hScard⟩ :=
    exists_cell_representatives Q (fun q => ⌊radialAngle p q/rho⌋)
  let rel := fun (q v : Point) => tau≤euclideanDistance p v ∧ v∈physicalPairTube P rho (p,q)
  have hlower : ∀ q∈S, m≤((P.bipartiteAbove rel q).card : ℝ) := by
    intro q hq
    have heq : P.bipartiteAbove rel q=(physicalPairTube P rho (p,q)).filter
        (fun v => tau≤euclideanDistance p v) := by
      ext v
      simp only [Finset.bipartiteAbove,rel,physicalPairTube,Finset.mem_filter]
      tauto
    rw [heq]
    exact hmass q (hSQ hq)
  have hupper : ∀ v∈P, ((S.bipartiteBelow rel v).card : ℝ)≤100/tau := by
    intro v _hv
    by_cases hfar : tau≤euclideanDistance p v
    · simpa only [Finset.bipartiteBelow,rel,hfar,true_and] using
        original_point_tube_incidence_euclidean P S p v hrho htau htau1 hfar
          (fun q hq => hne q (hSQ hq)) hinj
    · simp only [Finset.bipartiteBelow,rel,hfar,false_and,Finset.filter_false,
        Finset.card_empty,Nat.cast_zero]
      positivity
  have hcount := Finset.card_nsmul_le_card_nsmul (R:=ℝ) (r:=rel) (s:=S) (t:=P)
    hlower hupper
  simpa only [nsmul_eq_mul,hScard,mul_comm] using hcount

/-- Global actual forward class count (229), obtained by summing the
proved original-root incidence bound, without an assumed overlap budget. -/
theorem original_forward_class_population (P : Finset Point) (G : Finset Pair)
    {rho tau m : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1) (hm : 0≤m)
    (hG : G ⊆ P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hmass : ∀ z∈G, m≤(((physicalPairTube P rho z).filter
      (fun v => tau≤euclideanDistance z.1 v)).card : ℝ)) :
    m*((G.image (forwardClass rho)).card : ℝ) ≤100/tau*(P.card : ℝ)^2 := by
  let Q := fun p : Point => P.filter (fun q => (p,q)∈G)
  let cells := fun p : Point => (Q p).image (fun q => ⌊radialAngle p q/rho⌋)
  have hcover : G.image (forwardClass rho) ⊆ P.biUnion (fun p => {p} ×ˢ cells p) := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    have hp := Finset.mem_product.mp (hG hz)
    exact Finset.mem_biUnion.mpr ⟨z.1,hp.1,Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self _,Finset.mem_image.mpr
        ⟨z.2,Finset.mem_filter.mpr ⟨hp.2,hz⟩,rfl⟩⟩⟩
  have hcard : ((G.image (forwardClass rho)).card : ℝ) ≤
      ∑ p∈P, ((cells p).card : ℝ) := by
    calc
      _ ≤ ((P.biUnion (fun p => {p} ×ˢ cells p)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hcover)
      _ ≤ ∑ p∈P, (({p} ×ˢ cells p).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ = _ := by simp
  have hlocal : ∀ p∈P, m*((cells p).card : ℝ)≤100/tau*P.card := by
    intro p _hp
    exact root_original_angle_population P (Q p) p hrho htau htau1
      (fun q hq => hne (p,q) (Finset.mem_filter.mp hq).2)
      (fun q hq => hmass (p,q) (Finset.mem_filter.mp hq).2)
  calc
    _ ≤ m*(∑ p∈P, ((cells p).card : ℝ)) := mul_le_mul_of_nonneg_left hcard hm
    _ = ∑ p∈P, m*((cells p).card : ℝ) := Finset.mul_sum _ _ _
    _ ≤ ∑ _p∈P, (100/tau*(P.card : ℝ)) := Finset.sum_le_sum hlocal
    _ = _ := by simp; ring

end OriginalAngularClassPopulation
