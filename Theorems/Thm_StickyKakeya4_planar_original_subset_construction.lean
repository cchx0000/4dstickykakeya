import Theorems.Thm_StickyKakeya4_planar_rounded_sumset_cover
import Theorems.Thm_StickyKakeya4_asymmetric_original_subset_assembly
import Theorems.Thm_StickyKakeya4_separated_dyadic_cardinality

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open scoped Pointwise BigOperators
noncomputable section
namespace PlanarOriginalSubsetConstruction
open PlanarShiftedNearEnergy ActualPlanarRoundedEnergy SymmetryDifferenceGrowthChain

lemma half_mesh (n : ℕ) : ((2:ℝ)^n)⁻¹/2 = ((2:ℝ)^(n+1))⁻¹ := by
  rw [pow_succ, mul_inv_rev]
  ring

/-- The coupled floor image is bounded using the original coordinate support. -/
theorem rounded_cardinality_bound (X : Finset (ℝ×ℝ)) (n B : ℕ)
    (hbound : ∀ x∈X, |x.1|≤(B:ℝ) ∧ |x.2|≤(B:ℝ)) :
    (X.image (roundPoint (((2:ℝ)^n)⁻¹/2))).card ≤ (4*B+1)^2*2^(2*n) := by
  classical
  let I := Finset.Icc (-(B:ℤ)*2^(n+1)) ((B:ℤ)*2^(n+1))
  have hsub : X.image (roundPoint (((2:ℝ)^n)⁻¹/2)) ⊆ I.product I := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [half_mesh]
    exact Finset.mem_product.mpr ⟨
      SeparatedDyadicCardinality.original_rounded_label_bounds (n+1) B (hbound x hx).1,
      SeparatedDyadicCardinality.original_rounded_label_bounds (n+1) B (hbound x hx).2⟩
  have hi : I.card = 4*B*2^n+1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have h : (B:ℤ)*2^(n+1)+1-(-(B:ℤ)*2^(n+1)) = ((4*B*2^n+1 : ℕ):ℤ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [h]
    exact Int.toNat_natCast _
  have hbd : I.card ≤ (4*B+1)*2^n := by
    rw [hi]
    have hp : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
    nlinarith
  calc
    _ ≤ (I.product I).card := Finset.card_le_card hsub
    _ = I.card*I.card := Finset.card_product _ _
    _ ≤ ((4*B+1)*2^n)*((4*B+1)*2^n) := Nat.mul_le_mul hbd hbd
    _ = _ := by
      rw [show 2*n = n*2 by omega, pow_mul]
      ring

/-- Pullback keeps both coordinates attached to the same original point. -/
theorem original_preimage (X : Finset (ℝ×ℝ)) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖)
    (S : Finset (ℤ×ℤ)) (hS : S ⊆ X.image (roundPoint (delta/2))) :
    ∃ X'⊆X, X'.image (roundPoint (delta/2)) = S ∧ X'.card = S.card := by
  classical
  let X' := X.filter (fun x => roundPoint (delta/2) x ∈ S)
  have hsub : X'⊆X := Finset.filter_subset _ _
  have him : X'.image (roundPoint (delta/2)) = S := by
    ext k
    constructor
    · intro hk
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp hx).2
    · intro hk
      obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp (hS hk)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,by simpa only [heq] using hk⟩,heq⟩
  have hinj := (planar_rounding_injOn X hdelta hsep).mono hsub
  exact ⟨X',hsub,him,(Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card him)⟩

/-- Original planar points, exact coupled integer BSG, and every physical sumset. -/
theorem original_planar_subsets
    (X Y : Finset (ℝ×ℝ)) (hX : X.Nonempty) (hY : Y.Nonempty)
    {delta nu : ℝ} (hdelta : 0 < delta) (hnu : 0 < nu)
    (hXsep : ∀ x∈X, ∀ y∈X, x≠y → delta/2 ≤ ‖x-y‖)
    (hYsep : ∀ x∈Y, ∀ y∈Y, x≠y → delta/2 ≤ ‖x-y‖)
    (he : nu*(X.card:ℝ)^2*(Y.card:ℝ) ≤
      ((coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card:ℝ))
    {J : ℕ} (hJ : 0 < J) :
    ∃ j X' Y', 1≤j ∧ j≤J ∧ X'⊆X ∧ Y'⊆Y ∧
      let Xbar := X.image (roundPoint (delta/2))
      let Ybar := Y.image (roundPoint (delta/2))
      let a := (5*nu/49)/10
      let kappa := (density Ybar Xbar a j)^2 / slowFactor Ybar Xbar a J
      let K := BalancedBSGIterationCore.growthConstant kappa
      let theta := threshold a (j-1)/(2*K)
      0<kappa ∧ kappa≤1 ∧ 1≤K ∧ 0<theta ∧ K*kappa^58≤2^192 ∧
      (kappa/16)*(∏ i∈Finset.range j, density Ybar Xbar a i/2)*
        (X.card:ℝ) ≤ X'.card ∧
      (theta^2/K^4)*(Y.card:ℝ) ≤ Y'.card ∧
      ∀ n m : ℕ, (((Y'+n•X'-m•X').image (roundPoint (delta/2))).card:ℝ) ≤
        ((2*(n+m+1)+1 : ℕ):ℝ)^2*(K^(2*(n+m+1))/theta)*(Y.card:ℝ) := by
  classical
  let Xbar := X.image (roundPoint (delta/2))
  let Ybar := Y.image (roundPoint (delta/2))
  have hXbar : Xbar.Nonempty := hX.image _
  have hYbar : Ybar.Nonempty := hY.image _
  have hXC : Xbar.card=X.card := planar_rounded_card X hdelta hXsep
  have hYC : Ybar.card=Y.card := planar_rounded_card Y hdelta hYsep
  have hround := original_planar_near_energy X Y hdelta hXsep hYsep
  have he' : 2*((5*nu/49)/10)*(Ybar.card:ℝ)*(Xbar.card:ℝ)^2 ≤
      (Finset.addEnergy Ybar Xbar:ℝ) := by
    have hc : ((coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card:ℝ) ≤
        49*(Finset.addEnergy Xbar Ybar:ℝ) := by exact_mod_cast hround
    rw [Finset.addEnergy_comm, hXC, hYC]
    nlinarith
  obtain ⟨j,U,V,hj1,hjJ,hU,hV,hkap,hkap1,hK1,htheta,hKcost,hUsize,hVsize,hsums⟩ :=
    AsymmetricOriginalSubsetAssembly.finite_asymmetric_original_subsets Ybar Xbar
      (by positivity : 0 < (5*nu/49)/10) hYbar hXbar he' hJ
  obtain ⟨X',hXX,hXim,hXcard⟩ := original_preimage X hdelta hXsep U hU
  obtain ⟨Y',hYY,hYim,hYcard⟩ := original_preimage Y hdelta hYsep V hV
  refine ⟨j,X',Y',hj1,hjJ,hXX,hYY,hkap,hkap1,hK1,htheta,hKcost,?_,?_,?_⟩
  · simpa only [hXC,hXcard] using hUsize
  · simpa only [hYC,hYcard] using hVsize
  · intro n m
    have hcover := PlanarRoundedSumsetCover.actual_planar_iterated_cover X' Y'
      (by positivity : 0 < delta/2) n m
    rw [hXim,hYim] at hcover
    have hcoverR : (((Y'+n•X'-m•X').image (roundPoint (delta/2))).card:ℝ) ≤
        ((2*(n+m+1)+1 : ℕ):ℝ)^2*((V+n•U-m•U).card:ℝ) := by exact_mod_cast hcover
    have hfinal := hcoverR.trans (mul_le_mul_of_nonneg_left (hsums n m) (by positivity))
    simpa only [hYC,mul_assoc] using hfinal

end PlanarOriginalSubsetConstruction
