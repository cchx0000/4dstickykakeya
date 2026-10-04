import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_parameters
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_frostman
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace OriginalThreeDimensionalPairTubeFamily
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeParameters OriginalThreeDimensionalTubeFrostman

lemma original_endpoints_mem_tube (z : Pair3) (rho : ℝ) (hrho : 0≤rho) :
    z.1∈physicalTube3 z.1 z.2 rho ∧ z.2∈physicalTube3 z.1 z.2 rho := by
  constructor
  · refine ⟨0,?_⟩
    simpa [distance3,linePoint3] using hrho
  · refine ⟨1,?_⟩
    simpa [distance3,linePoint3] using hrho

/-- The full original ordered-pair fiber of a parameter cell is paid by
the square of its actual representative tube's original point population. -/
theorem original_parameter_pair_fiber (P : Finset Point3) (G : Finset Pair3)
    (rho : ℝ) (i : Fin 3) (v : Pair3) (hrho : 0<rho)
    (hG : G⊆P.product P) (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈G, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hv : v∈G) :
    (G.filter (fun z => parameterCell rho i z=parameterCell rho i v)).card≤
      (physicalPairTube3 P (8*rho) v).card^2 := by
  let T := physicalPairTube3 P (8*rho) v
  have hsub : G.filter (fun z => parameterCell rho i z=parameterCell rho i v)⊆T.product T := by
    intro z hz
    obtain ⟨hzG,hcell⟩ := Finset.mem_filter.mp hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp (hG hzG)
    have ends := original_endpoints_mem_tube z rho hrho.le
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hp,original_parameter_tube_transfer rho i z v hrho
        (hne z hzG) (hne v hv) (hmax z hzG) hcell z.1 (hbox z.1 hp) ends.1⟩
    · exact Finset.mem_filter.mpr ⟨hq,original_parameter_tube_transfer rho i z v hrho
        (hne z hzG) (hne v hv) (hmax z hzG) hcell z.2 (hbox z.2 hq) ends.2⟩
  have hh := Finset.card_le_card hsub
  simpa only [Finset.product_eq_sprod,Finset.card_product,pow_two,T] using hh

/-- Select actual original endpoint-pair representatives of the actual
parameter cells. Original 2-Frostman bounds derive the family lower count;
all original pairs and all their bounded shading points retain an actual
representative tube. -/
theorem exists_original_parameter_tube_family (P : Finset Point3) (G : Finset Pair3)
    (delta eta rho : ℝ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta)
    (hquery : delta≤rho) (hrho : 8*rho≤1)
    (hG : G⊆P.product P) (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hne : ∀ z∈G, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈G, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ∃ T : Finset Pair3, T⊆G ∧ Set.InjOn (parameterCell rho i) T ∧
      T.image (parameterCell rho i)=G.image (parameterCell rho i) ∧
      (G.card : ℝ)≤T.card*(3200*delta^(-eta)*rho*P.card)^2 ∧
      ∀ z∈G, ∃ v∈T, parameterCell rho i z=parameterCell rho i v ∧
        physicalPairTube3 P rho z⊆physicalPairTube3 P (8*rho) v := by
  have hp : 0<rho := hd.trans_le hquery
  let f := parameterCell rho i
  obtain ⟨T,hTG,hinj,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑G : Set Pair3) (G.image f) (by
      intro c hc
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨z,hz,rfl⟩)
  have hcount := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers G (G.image f) f
    ((3200*delta^(-eta)*rho*P.card)^2)
    (fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩) (by
      intro c hc
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
      have hf := original_parameter_pair_fiber P G rho i v hp hG hbox hne hmax hv
      have ht := original_tube_two_frostman_count P v delta eta (8*rho) hd hd1 heta
        (by linarith only [hquery,hp]) hrho hbox hfrostman
      have ht' : ((physicalPairTube3 P (8*rho) v).card : ℝ)≤3200*delta^(-eta)*rho*P.card := by
        nlinarith only [ht]
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg (physicalPairTube3 P (8*rho) v).card) ht' 2
      exact (show ((G.filter (fun z => f z=f v)).card : ℝ)≤
        ((physicalPairTube3 P (8*rho) v).card : ℝ)^2 by exact_mod_cast hf).trans hs)
  have hc : T.card=(G.image f).card := by rw [← himage,Finset.card_image_of_injOn hinj]
  refine ⟨T,hTG,hinj,himage,by simpa only [← hc] using hcount,?_⟩
  intro z hz
  have hfz : f z∈T.image f := by rw [himage]; exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hfz
  refine ⟨v,hv,heq.symm,?_⟩
  intro x hx
  obtain ⟨hxP,hxt⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxP,original_parameter_tube_transfer rho i z v hp
    (hne z hz) (hne v (hTG hv)) (hmax z hz) heq.symm x (hbox x hxP) hxt⟩

end OriginalThreeDimensionalPairTubeFamily
