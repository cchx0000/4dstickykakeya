import Theorems.Thm_StickyKakeya4_native_a1_initial_radial_graph
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped BigOperators
noncomputable section
namespace OriginalRadialNearDiagonal
open OriginalPairStripGeometry PlanarFrostmanBallConversion

/-- The source's separation radius is queried inside the ORIGINAL profile
range and its Frostman coefficient is exactly delta^eta. -/
theorem original_separation_radius (delta t eta : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ht : 0<t) (heta : 0≤eta) (hetat : eta≤t/2) :
    delta≤delta^(2*eta/t) ∧ delta^(2*eta/t)≤1 ∧
      delta^(-eta)*(delta^(2*eta/t))^t=delta^eta := by
  have hexp : 2*eta/t≤1 := (div_le_iff₀ ht).mpr (by linarith)
  have hlow := Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp
  have hhigh := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show 0≤2*eta/t by positivity)
  refine ⟨by simpa only [Real.rpow_one] using hlow,
    by simpa only [Real.rpow_zero] using hhigh,?_⟩
  rw [← Real.rpow_mul hd.le,← Real.rpow_add hd]
  congr 1
  field_simp
  ring

/-- Remove actual close ORIGINAL pairs, charging their full count to the
original point Frostman profile at the proved legal source radius. Any
previous physical-tube property survives because the output is a subgraph. -/
theorem remove_original_near_diagonal
    (Pts : Finset Point) (G : Finset Pair) (delta t eta : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ht : 0<t) (heta : 0≤eta) (hetat : eta≤t/2)
    (hGP : G⊆Pts.product Pts)
    (hfrostman : ∀ p∈Pts, ∀ r : ℝ, delta≤r → r≤1 →
      ((Pts.filter (fun q => euclideanDistance p q≤r)).card : ℝ)≤
        delta^(-eta)*r^t*Pts.card) :
    ∃ H : Finset Pair, H⊆G ∧
      (∀ z∈H, delta^(2*eta/t)≤euclideanDistance z.1 z.2) ∧
      (G.card : ℝ)≤H.card+delta^eta*(Pts.card : ℝ)^2 := by
  classical
  let r := delta^(2*eta/t)
  let H := G.filter (fun z => r≤euclideanDistance z.1 z.2)
  let Bad := (Pts.product Pts).filter (fun z => euclideanDistance z.1 z.2<r)
  obtain ⟨hrlow,hrhigh,hcoef⟩ := original_separation_radius delta t eta hd hd1 ht heta hetat
  have hrow (p : Point) (hp : p∈Pts) :
      ((Pts.filter (fun q => euclideanDistance p q<r)).card : ℝ)≤delta^eta*Pts.card := by
    have hsubset : Pts.filter (fun q => euclideanDistance p q<r)⊆
        Pts.filter (fun q => euclideanDistance p q≤r) := by
      intro q hq
      obtain ⟨hqP,hqr⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqP,hqr.le⟩
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans
      (hfrostman p hp r hrlow hrhigh)
    simpa only [r,hcoef] using hh
  have hBadEq : Bad.card=∑ p∈Pts, (Pts.filter (fun q => euclideanDistance p q<r)).card := by
    simp only [Bad,Finset.card_eq_sum_ones,Finset.sum_filter,
      Finset.product_eq_sprod,Finset.sum_product]
  have hBad : (Bad.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2 := by
    have hEq : (Bad.card : ℝ)=∑ p∈Pts, ((Pts.filter (fun q => euclideanDistance p q<r)).card : ℝ) := by
      exact_mod_cast hBadEq
    rw [hEq]
    calc
      _ ≤ ∑ _p∈Pts, delta^eta*(Pts.card : ℝ) := Finset.sum_le_sum hrow
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcover : G⊆H∪Bad := by
    intro z hz
    by_cases hsep : r≤euclideanDistance z.1 z.2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz,hsep⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hGP hz,lt_of_not_ge hsep⟩))
  have hcard : (G.card : ℝ)≤H.card+Bad.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le H Bad)
  refine ⟨H,Finset.filter_subset _ _,?_,?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · linarith only [hcard,hBad]

end OriginalRadialNearDiagonal
