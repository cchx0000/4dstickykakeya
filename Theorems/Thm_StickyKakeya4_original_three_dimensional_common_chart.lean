import Theorems.Thm_StickyKakeya4_original_three_dimensional_pair_tube_family
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalCommonChart
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeParameters OriginalThreeDimensionalPairTubeFamily

def chartPairs (G : Finset Pair3) (i : Fin 3) : Finset Pair3 :=
  G.filter (fun z => z.2 i-z.1 i≠0 ∧ ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)

/-- One largest-coordinate chart retains a third of the original ordered
graph. The chart is selected from actual endpoint differences. -/
theorem exists_original_common_chart (G : Finset Pair3) (hne : ∀ z∈G, z.1≠z.2) :
    ∃ i : Fin 3, chartPairs G i⊆G ∧ G.card≤3*(chartPairs G i).card := by
  have hcover : G⊆(Finset.univ : Finset (Fin 3)).biUnion (chartPairs G) := by
    intro z hz
    obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
      (fun j => |z.2 j-z.1 j|) Finset.univ_nonempty
    have hi : z.2 i-z.1 i≠0 := by
      intro hi0
      apply hne z hz
      funext j
      have hh := hmax j (Finset.mem_univ j)
      rw [hi0,abs_zero] at hh
      exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))).symm
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hz,hi,fun j => hmax j (Finset.mem_univ j)⟩⟩
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun j => (chartPairs G j).card) Finset.univ_nonempty
  have hs : (∑ j : Fin 3, (chartPairs G j).card)≤3*(chartPairs G i).card := by
    calc
      _ ≤ ∑ _j : Fin 3, (chartPairs G i).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  refine ⟨i,Finset.filter_subset _ _,?_⟩
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans hs)

/-- Actual original rich-pair tubes admit a finite original representative
family in a common chart. The original Frostman law, not a tube-count
certificate, pays the pair fibers and gives the inverse-square-scale
family count. Every retained original shading point has its original
representative tube after a fixed width enlargement. -/
theorem exists_original_common_chart_tube_family (P : Finset Point3) (G : Finset Pair3)
    (delta eta rho : ℝ) (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤rho) (hrho : 8*rho≤1)
    (hG : G⊆P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ∃ i : Fin 3, ∃ T : Finset Pair3, T⊆chartPairs G i ∧ T⊆G ∧
      Set.InjOn (parameterCell rho i) T ∧
      (G.card : ℝ)≤3*T.card*(3200*delta^(-eta)*rho*P.card)^2 ∧
      ∀ z∈chartPairs G i, ∃ v∈T,
        physicalPairTube3 P rho z⊆physicalPairTube3 P (8*rho) v := by
  obtain ⟨i,hsub,hcard⟩ := exists_original_common_chart G hne
  obtain ⟨T,hT,hinj,_himage,hcount,hmap⟩ := exists_original_parameter_tube_family
    P (chartPairs G i) delta eta rho i hd hd1 heta hquery hrho (hsub.trans hG) hbox
    (fun z hz => (Finset.mem_filter.mp hz).2.1)
    (fun z hz => (Finset.mem_filter.mp hz).2.2) hfrostman
  refine ⟨i,T,hT,hT.trans hsub,hinj,?_,?_⟩
  · have hc : (G.card : ℝ)≤3*(chartPairs G i).card := by exact_mod_cast hcard
    have hm := mul_le_mul_of_nonneg_left hcount (show (0:ℝ)≤3 by norm_num)
    nlinarith only [hc,hm]
  · intro z hz
    obtain ⟨v,hv,_hcell,ht⟩ := hmap z hz
    exact ⟨v,hv,ht⟩

end OriginalThreeDimensionalCommonChart
