import Theorems.Thm_StickyKakeya4_original_three_dimensional_shade_group_concentration
import Theorems.Thm_StickyKakeya4_original_three_dimensional_localized_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalGroupSourceMass
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalShadeGroupConcentration OriginalThreeDimensionalLocalizedEnergy

/-- A dense actual tube group forces original mass in its supporting set.
The point energy retains the ambient P normalization. -/
theorem original_dense_group_source_mass (P S : Finset Point3) (R : Finset Pair3)
    (delta rho K nu H : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0 < delta) (hquery : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 1 ≤ K) (hnu : 0 ≤ nu) (hP : P.Nonempty) (hSP : S⊆P)
    (hterminal : 1 ≤ 2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hne : ∀ z∈R, z.2 i-z.1 i ≠ 0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j| ≤ |z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r^2*P.card)
    (hsupport : ∀ z∈R,physicalPairTube3 P (8*rho) z⊆S)
    (hrich : ∀ z∈R,nu*rho*P.card ≤ ((physicalPairTube3 P (8*rho) z).card : ℝ))
    (hcount : H ≤ rho^2*R.card) :
    H*nu^2*P.card ≤ 4000000000*((N:ℝ)+1)*K*S.card := by
  have hrho := hd.trans_le hquery
  have hp : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have henergy := original_supported_tube_square_energy P S R delta rho K N i hSP hd hquery hK
    hrho1 hterminal hbox hne hmax hcell hfrostman hsupport
  have hlo : (R.card : ℝ)*(nu*rho*P.card)^2 ≤
      ∑ z∈R,((physicalPairTube3 P (8*rho) z).card : ℝ)^2 := by
    calc
      _ = ∑ _z∈R,(nu*rho*P.card)^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z hz => pow_le_pow_left₀ (by positivity) (hrich z hz) 2)
  have hscaled := mul_le_mul_of_nonneg_right hcount (show 0 ≤ nu^2*(P.card : ℝ)^2 by positivity)
  apply (mul_le_mul_iff_of_pos_right hp).mp
  nlinarith only [henergy,hlo,hscaled]

/-- Combine the actual shade union estimate and original localized energy
without assuming a desired concentration or renormalized Frostman law. -/
theorem exists_original_shaded_group_source_mass {ι : Type*} (J : Finset ι)
    (P : Finset Point3) (S : ι → Finset Point3) (R : ι → Finset Pair3)
    (Y : Pair3 → Finset Point3) (delta rho K nu b h B : ℝ) (N : ℕ) (i : Fin 3)
    (hd : 0 < delta) (hquery : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 1 ≤ K) (hnu : 0 ≤ nu) (hP : P.Nonempty)
    (hb : 0 < b) (hsmall : rho ≤ b/4800) (hh : 0 < h) (hB : 0 < B)
    (hterminal : 1 ≤ 2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r^2*P.card)
    (hSP : ∀ k∈J,S k⊆P)
    (hne : ∀ k∈J,∀ z∈R k,z.2 i-z.1 i ≠ 0)
    (hmax : ∀ k∈J,∀ z∈R k,∀ j,|z.2 j-z.1 j| ≤ |z.2 i-z.1 i|)
    (hcell : ∀ k∈J,Set.InjOn (parameterCell rho i) (R k))
    (hYP : ∀ k∈J,∀ z∈R k,Y z⊆P)
    (hshade : ∀ k∈J,∀ z∈R k,∀ x∈Y z,x∈physicalTube3 z.1 z.2 (4*rho))
    (hinj : ∀ k∈J,∀ z∈R k,Set.InjOn (cell rho) (Y z))
    (hmass : ∀ k∈J,∀ z∈R k,b ≤ rho*(Y z).card)
    (hsupport : ∀ k∈J,∀ z∈R k,physicalPairTube3 P (8*rho) z⊆S k)
    (hrich : ∀ k∈J,∀ z∈R k,nu*rho*P.card ≤ ((physicalPairTube3 P (8*rho) z).card : ℝ))
    (hpop : h ≤ rho^2*∑ k∈J,((R k).card : ℝ))
    (hunion : rho^2*∑ k∈J,(((R k).biUnion Y).card : ℝ) ≤ B) :
    ∃ k∈J,h^2*b^4*nu^2*P.card ≤
      400000000000000000000000000*((N:ℝ)+1)*K*B^2*(S k).card := by
  have hrho := hd.trans_le hquery
  obtain ⟨k,hk,_hn,hcount⟩ := exists_original_dense_shade_group J R Y rho b h B i hrho hrho1
    hb hsmall hh hB hne hmax hcell hshade
    (fun k hk z hz x hx => hbox x (hYP k hk z hz hx)) hinj hmass hpop hunion
  let C : ℝ := 100000000000000000*B^2
  have hCp : 0 < C := by dsimp [C]; positivity
  have hcount' : h^2*b^4/C ≤ rho^2*(R k).card := by
    apply (div_le_iff₀ hCp).mpr
    dsimp [C]
    nlinarith only [hcount]
  have he := original_dense_group_source_mass P (S k) (R k) delta rho K nu (h^2*b^4/C) N i
    hd hquery hrho1 hK hnu hP (hSP k hk) hterminal hbox (hne k hk) (hmax k hk)
    (hcell k hk) hfrostman (hsupport k hk) (hrich k hk) hcount'
  have hm := mul_le_mul_of_nonneg_right he hCp.le
  have hc : (h^2*b^4/C*nu^2*P.card)*C=h^2*b^4*nu^2*P.card := by field_simp
  rw [hc] at hm
  refine ⟨k,hk,?_⟩
  dsimp [C] at hm
  nlinarith only [hm]

end OriginalThreeDimensionalGroupSourceMass
