import Theorems.Thm_StickyKakeya4_asymmetric_original_subset_assembly
import Theorems.Thm_StickyKakeya4_rounded_iterated_cover_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped Pointwise BigOperators
noncomputable section

namespace OriginalRealAsymmetricConstruction
open ActualRoundedAdditiveEnergy SymmetryDifferenceGrowthChain

/-- The exact finite asymmetric construction on ORIGINAL separated real
points, starting from literal approximate difference energy. All selected
sets consist of original points, and the output is the actual floor-grid
cover of every original iterated sum-difference set. -/
theorem original_real_subsets
    (X Y : Finset ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    {delta nu : ℝ} (hdelta : 0<delta) (hnu : 0<nu)
    (hXsep : ∀ x∈X, ∀ y∈X, x≠y → delta≤|x-y|)
    (hYsep : ∀ x∈Y, ∀ y∈Y, x≠y → delta≤|x-y|)
    (he : nu*(X.card : ℝ)^2*(Y.card : ℝ) ≤ (nearDifferenceEnergy X Y delta : ℝ))
    {J : ℕ} (hJ : 0<J) :
    ∃ j X' Y', 1≤j ∧ j≤J ∧ X'⊆X ∧ Y'⊆Y ∧
      let Xbar := X.image (rounded delta)
      let Ybar := Y.image (rounded delta)
      let kappa := (density Ybar Xbar (nu/10) j)^2 / slowFactor Ybar Xbar (nu/10) J
      let K := BalancedBSGIterationCore.growthConstant kappa
      let theta := threshold (nu/10) (j-1)/(2*K)
      0<kappa ∧ kappa≤1 ∧ 1≤K ∧ 0<theta ∧ K*kappa^58≤2^192 ∧
      (kappa/16)*(∏ i∈Finset.range j, density Ybar Xbar (nu/10) i/2)*
        (X.card : ℝ) ≤ X'.card ∧
      (theta^2/K^4)*(Y.card : ℝ) ≤ Y'.card ∧
      ∀ n m : ℕ, (((Y'+n•X'-m•X').image (rounded delta)).card : ℝ) ≤
        (2*(n+m+1)+1 : ℕ)*(K^(2*(n+m+1))/theta)*(Y.card : ℝ) := by
  classical
  let Xbar := X.image (rounded delta)
  let Ybar := Y.image (rounded delta)
  have hXbar : Xbar.Nonempty := hX.image _
  have hYbar : Ybar.Nonempty := hY.image _
  have hXC : Xbar.card=X.card := rounded_card X hdelta hXsep
  have hYC : Ybar.card=Y.card := rounded_card Y hdelta hYsep
  have hround := rounded_energy_density X Y hdelta hXsep hYsep he
  have he' : 2*(nu/10)*(Ybar.card : ℝ)*(Xbar.card : ℝ)^2 ≤
      (Finset.addEnergy Ybar Xbar : ℝ) := by
    calc
      _ = (nu/5)*(Xbar.card : ℝ)^2*(Ybar.card : ℝ) := by ring
      _ ≤ (Finset.addEnergy Xbar Ybar : ℝ) := hround
      _ = _ := by rw [Finset.addEnergy_comm]
  obtain ⟨j,U,V,hj1,hjJ,hU,hV,hkap,hkap1,hK1,htheta,hKcost,hUsize,hVsize,hsums⟩ :=
    AsymmetricOriginalSubsetAssembly.finite_asymmetric_original_subsets Ybar Xbar
      (div_pos hnu (by norm_num)) hYbar hXbar he' hJ
  obtain ⟨X',hXX,hXim,hXcard⟩ := RoundedIteratedCoverTransfer.original_preimage X hdelta hXsep U hU
  obtain ⟨Y',hYY,hYim,hYcard⟩ := RoundedIteratedCoverTransfer.original_preimage Y hdelta hYsep V hV
  refine ⟨j,X',Y',hj1,hjJ,hXX,hYY,hkap,hkap1,hK1,htheta,hKcost,?_,?_,?_⟩
  · simpa only [hXC,hXcard] using hUsize
  · simpa only [hYC,hYcard] using hVsize
  · intro n m
    have hcover := RoundedIteratedCoverTransfer.iterated_grid_cover_bound X' Y' hdelta n m
    rw [hXim,hYim] at hcover
    have hcoverR : (((Y'+n•X'-m•X').image (rounded delta)).card : ℝ) ≤
        (2*(n+m+1)+1 : ℕ)*((V+n•U-m•U).card : ℝ) := by exact_mod_cast hcover
    have hfinal := hcoverR.trans (mul_le_mul_of_nonneg_left (hsums n m) (Nat.cast_nonneg _))
    simpa only [hYC,mul_assoc] using hfinal

end OriginalRealAsymmetricConstruction
