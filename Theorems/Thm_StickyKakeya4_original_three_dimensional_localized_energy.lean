import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_incidence_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalLocalizedEnergy
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubePairCount OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalTubeFamilyEnergy

/-- Localizing the outer source sum preserves the ORIGINAL ambient
Frostman normalization. No Frostman law for the restricted measure is used. -/
theorem original_localized_pair_energy (P S : Finset Point3) (delta rho K : ℝ) (N : ℕ)
    (hSP : S⊆P) (hd : 0<delta) (hquery : delta≤rho) (hK : 1≤K)
    (hterminal : 1≤2*dyadicRadius rho N)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta≤r → r≤1 →
      ((P.filter (fun q => distance3 p q≤r)).card : ℝ)≤K*r^2*P.card) :
    (∑ x∈S,∑ y∈S,inverseSquareKernel rho (distance3 x y))≤
      4*((N:ℝ)+1)*K*P.card*S.card := by
  calc
    _ ≤ ∑ x∈S,∑ y∈P,inverseSquareKernel rho (distance3 x y) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact Finset.sum_le_sum_of_subset_of_nonneg hSP (fun y _hy _hyS => inverse_square_kernel_nonneg rho _)
    _ ≤ ∑ _x∈S,4*((N:ℝ)+1)*K*P.card := by
      apply Finset.sum_le_sum
      intro x hx
      exact original_point_inverse_square_energy P x delta rho K N hd hquery hK hterminal (hSP hx) hfrostman
    _ = _ := by simp [mul_comm]

/-- The physical tube family can be localized to an original subset
without replacing the ambient point mass in the energy bound. -/
theorem original_localized_tube_square_energy (P S : Finset Point3) (R : Finset Pair3)
    (delta rho K : ℝ) (N : ℕ) (i : Fin 3)
    (hSP : S⊆P) (hd : 0<delta) (hquery : delta≤rho) (hK : 1≤K)
    (hrho1 : rho≤1) (hterminal : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta≤r → r≤1 →
      ((P.filter (fun q => distance3 p q≤r)).card : ℝ)≤K*r^2*P.card) :
    (∑ z∈R,((physicalPairTube3 S (8*rho) z).card : ℝ)^2)≤
      4000000000*((N:ℝ)+1)*K*P.card*S.card := by
  have hrho := hd.trans_le hquery
  rw [original_tube_square_sum_swap]
  calc
    _ ≤ ∑ x∈S,∑ y∈S,1000000000*inverseSquareKernel rho (distance3 x y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hh := original_tubes_through_pair_card R rho i x y hrho hrho1
        (hbox x (hSP hx)) (hbox y (hSP hy)) hne hmax hcell
      simpa only [inverseSquareKernel,mul_one_div] using hh
    _ = 1000000000*(∑ x∈S,∑ y∈S,inverseSquareKernel rho (distance3 x y)) := by
      simp only [Finset.mul_sum]
    _ ≤ 1000000000*(4*((N:ℝ)+1)*K*P.card*S.card) :=
      mul_le_mul_of_nonneg_left (original_localized_pair_energy P S delta rho K N hSP hd hquery hK hterminal hfrostman) (by norm_num)
    _ = _ := by ring

/-- When actual original tube populations lie in one geometric source
subset, their ORIGINAL square mass is paid by that subset's original mass. -/
theorem original_supported_tube_square_energy (P S : Finset Point3) (R : Finset Pair3)
    (delta rho K : ℝ) (N : ℕ) (i : Fin 3)
    (hSP : S⊆P) (hd : 0<delta) (hquery : delta≤rho) (hK : 1≤K)
    (hrho1 : rho≤1) (hterminal : 1≤2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j|≤1)
    (hne : ∀ z∈R, z.2 i-z.1 i≠0)
    (hmax : ∀ z∈R, ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hcell : Set.InjOn (parameterCell rho i) R)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta≤r → r≤1 →
      ((P.filter (fun q => distance3 p q≤r)).card : ℝ)≤K*r^2*P.card)
    (hsupport : ∀ z∈R,physicalPairTube3 P (8*rho) z⊆S) :
    (∑ z∈R,((physicalPairTube3 P (8*rho) z).card : ℝ)^2)≤
      4000000000*((N:ℝ)+1)*K*P.card*S.card := by
  have heq (z : Pair3) (hz : z∈R) : physicalPairTube3 P (8*rho) z=physicalPairTube3 S (8*rho) z := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_filter.mpr ⟨hsupport z hz hx,(Finset.mem_filter.mp hx).2⟩
    · intro hx
      exact Finset.mem_filter.mpr ⟨hSP (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  have hsum : (∑ z∈R,((physicalPairTube3 P (8*rho) z).card : ℝ)^2)=
      ∑ z∈R,((physicalPairTube3 S (8*rho) z).card : ℝ)^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [heq z hz]
  rw [hsum]
  exact original_localized_tube_square_energy P S R delta rho K N i hSP hd hquery hK
    hrho1 hterminal hbox hne hmax hcell hfrostman

end OriginalThreeDimensionalLocalizedEnergy
