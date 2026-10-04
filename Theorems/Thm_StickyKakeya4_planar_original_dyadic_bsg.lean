import Theorems.Thm_StickyKakeya4_planar_dyadic_numerics
import Theorems.Thm_StickyKakeya4_planar_original_subset_construction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open scoped Pointwise BigOperators
noncomputable section
namespace PlanarOriginalDyadicBSG
open PlanarShiftedNearEnergy ActualPlanarRoundedEnergy SymmetryDifferenceGrowthChain PlanarDyadicNumerics

/-- Native dyadic asymmetric BSG on coupled ORIGINAL planar points.
Support, separation, and literal coordinate-near energy construct all
cardinality and density estimates. The cutoff is uniform in nu and all
iterated sumset multiplicities. -/
theorem coordinate_planar_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ X Y : Finset (ℝ×ℝ), X.Nonempty → Y.Nonempty →
      (∀ x ∈ X, |x.1| ≤ 4 ∧ |x.2| ≤ 4) → (∀ y ∈ Y, |y.1| ≤ 1 ∧ |y.2| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ((2 : ℝ)^n)⁻¹/2 ≤ ‖x-y‖) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → ((2 : ℝ)^n)⁻¹/2 ≤ ‖x-y‖) →
      nu*(X.card : ℝ)^2*(Y.card : ℝ) ≤
        ((coordinateNearPairs (X.product Y) (fun p => p.1+p.2) (((2 : ℝ)^n)⁻¹)).card : ℝ) →
      ∃ X' Y' : Finset (ℝ×ℝ), X' ⊆ X ∧ Y' ⊆ Y ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (X.card : ℝ) ≤ X'.card ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (Y.card : ℝ) ≤ Y'.card ∧
        ∀ u v : ℕ,
          (((Y'+u•X'-v•X').image (roundPoint (((2 : ℝ)^n)⁻¹/2))).card : ℝ) ≤
            ((((2 : ℝ)^n)⁻¹)^(-epsilon*((u+v : ℕ) : ℝ))/nu^(K*(u+v)))*
              (Y.card : ℝ) := by
  classical
  obtain ⟨J, K, n0, hJ, hK, habs⟩ := native_dyadic_absorption hepsilon
  refine ⟨K, n0, hK, ?_⟩
  intro n hn nu hnu hnu1 X Y hX hY hXbound hYbound hXsep hYsep he
  let delta : ℝ := ((2 : ℝ)^n)⁻¹
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let Xbar := X.image (roundPoint (delta/2))
  let Ybar := Y.image (roundPoint (delta/2))
  have hXbar : Xbar.Nonempty := hX.image _
  have hYbar : Ybar.Nonempty := hY.image _
  have hXC : Xbar.card = X.card := planar_rounded_card X hdelta hXsep
  have hYC : Ybar.card = Y.card := planar_rounded_card Y hdelta hYsep
  have hXcard := PlanarOriginalSubsetConstruction.rounded_cardinality_bound X n 4 hXbound
  have hYcard := PlanarOriginalSubsetConstruction.rounded_cardinality_bound Y n 1
    (by simpa only [Nat.cast_one] using hYbound)
  change Xbar.card ≤ 289*2^(2*n) at hXcard
  change Ybar.card ≤ 25*2^(2*n) at hYcard
  have hXCbudget : (Xbar.card : ℝ) ≤ 289*(2 : ℝ)^(2*n) := by exact_mod_cast hXcard
  have hYCbudget : (Ybar.card : ℝ) ≤ 25*(2 : ℝ)^(2*n) := by exact_mod_cast hYcard
  have hXbudget : (Xbar.card : ℝ) ≤ 9*(2 : ℝ)^(2*n+6) := by
    rw [pow_add]
    norm_num
    nlinarith [show 0 ≤ (2 : ℝ)^(2*n) by positivity]
  have hYbudget : (Ybar.card : ℝ) ≤ 3*(2 : ℝ)^(2*n+6) := by
    rw [pow_add]
    norm_num
    nlinarith [show 0 ≤ (2 : ℝ)^(2*n) by positivity]
  let nu' : ℝ := 5*nu/49
  have hnu' : 0 < nu' := by dsimp [nu']; positivity
  let R := NativeAsymmetricScaleBudget.budget (2*n+6) J nu'
  let p := nativeDensity n J nu
  let L := sizeRatio Ybar Xbar
  let H := L^((J : ℝ)⁻¹)
  have hb := NativeAsymmetricScaleBudget.native_card_budget (2*n+6) J hnu' hXbudget hYbudget
  have hXB : Xbar.card ≤ 2^R := by exact_mod_cast hb.1
  have hYB : (Ybar.card : ℝ)/threshold (nu'/10) J ≤ (2 : ℝ)^R := hb.2
  have ha : 0 < nu'/10 := div_pos hnu' (by norm_num)
  have hround := original_planar_near_energy X Y hdelta hXsep hYsep
  have he' : 2*(nu'/10)*(Ybar.card : ℝ)*(Xbar.card : ℝ)^2 ≤
      (Finset.addEnergy Ybar Xbar : ℝ) := by
    have hc : ((coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card:ℝ) ≤
        49*(Finset.addEnergy Xbar Ybar:ℝ) := by exact_mod_cast hround
    rw [Finset.addEnergy_comm, hXC, hYC]
    dsimp [nu']
    nlinarith
  have hr := SymmetryChainUniformDensity.common_threshold_range Ybar Xbar ha hYbar hXbar he' J R
  have hp0 : 0 < p := hr.1
  have hp1 : p ≤ 1 := hr.2.1
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hH : 0 < H := Real.rpow_pos_of_pos hLpos _
  have hXone : 1 ≤ (Xbar.card : ℝ) := by exact_mod_cast hXbar.card_pos
  have hXpos : 0 < (Xbar.card : ℝ) := zero_lt_one.trans_le hXone
  have hLbudget : L ≤ 192*(2 : ℝ)^(2*n) := by
    apply max_le
    · have hpw := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := 2*n)
      linarith
    · apply (div_le_iff₀ hXpos).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hXone) (by positivity : 0 ≤ 192*(2 : ℝ)^(2*n))]
  obtain ⟨hnumX, hnumY, hnumC⟩ := habs n hn nu L hnu hnu1 hL1 hLbudget
  simp only [one_div] at hnumX hnumY hnumC
  obtain ⟨j, X', Y', hj1, hjJ, hXX, hYY, hkap, hkap1, hC1, htheta,
      _hCcost, hXsize, hYsize, hcover⟩ :=
    PlanarOriginalSubsetConstruction.original_planar_subsets X Y hX hY
      hdelta hnu hXsep hYsep he hJ
  let kappa := (density Ybar Xbar (nu'/10) j)^2 / slowFactor Ybar Xbar (nu'/10) J
  let C := BalancedBSGIterationCore.growthConstant kappa
  let t := threshold (nu'/10) (j-1)
  let theta := t/(2*C)
  have hkaplower : p^4/H ≤ kappa :=
    SymmetrySlowFactorBudget.chain_balanced_density_lower Ybar Xbar ha hYbar hXbar he'
      J R hJ hXB hYB j hjJ
  have hcost : C*p^232 ≤ (2 : ℝ)^192*H^58 :=
    SymmetrySlowFactorBudget.growth_cost_budget hp0 hLpos hkap hkap1 hkaplower
  have hpt : p ≤ t := hr.2.2 (j-1) (by omega)
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have ht : 0 < t := hp0.trans_le hpt
  have hproduct : ∀ i < j, p ≤ density Ybar Xbar (nu'/10) i := by
    intro i hi
    exact SymmetryChainUniformDensity.common_density_lower Ybar Xbar ha hYbar hXbar he'
      J R hXB hYB i (by omega)
  have hretX := NativeAsymmetricPolynomialRetention.original_x_retention hp0 hp1 hH
    hkaplower (density Ybar Xbar (nu'/10)) hjJ hproduct
  have hdenX : (16 : ℝ)*2^J*H = (2 : ℝ)^(J+4)*H := by
    rw [pow_add, show (2 : ℝ)^4 = 16 by norm_num]
    ring
  rw [hdenX] at hretX
  have hretY := NativeAsymmetricPolynomialRetention.original_y_retention hp0 hH
    (by positivity : 0 < (2 : ℝ)^192) hCpos hpt hcost
  have hdenY : 4*((2 : ℝ)^192)^6*H^348 = (2 : ℝ)^1154*H^348 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ)^2 by norm_num, ← pow_add]
  rw [hdenY] at hretY
  refine ⟨X', Y', hXX, hYY, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (hnumX.trans hretX) (Nat.cast_nonneg _)).trans hXsize
  · exact (mul_le_mul_of_nonneg_right (hnumY.trans hretY) (Nat.cast_nonneg _)).trans hYsize
  intro u v
  by_cases hs0 : u+v = 0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hs0
    simp only [zero_nsmul, add_zero, sub_zero, Nat.cast_zero, mul_zero,
      Real.rpow_zero, pow_zero, div_one, one_mul]
    exact Nat.cast_le.mpr ((Finset.card_image_le).trans (Finset.card_le_card hYY))
  have hs : 1 ≤ u+v := by omega
  have hiter := NativeAsymmetricPolynomialRetention.iterated_cost_budget hp0 hp1 hC1 hpt hcost (u+v) hs
  have hconst : 2*((2 : ℝ)^192)^(5*(u+v)) ≤ (2 : ℝ)^(961*(u+v)) := by
    calc
      _ = (2 : ℝ)^(960*(u+v)+1) := by
        rw [← pow_mul, show 192*(5*(u+v)) = 960*(u+v) by omega, pow_succ]
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hiter' : 2*C^(2*(u+v)+3)/t ≤
      (2 : ℝ)^(961*(u+v))*H^(290*(u+v))/p^(1161*(u+v)) :=
    hiter.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity))
  have hcosteq : C^(2*(u+v+1))/theta = 2*C^(2*(u+v)+3)/t := by
    have heq : C^(2*(u+v)+3) = C^(2*(u+v+1))*C := by
      rw [← pow_succ]
      congr 1
    rw [heq]
    dsimp [theta]
    field_simp
  have hfloor : ((2*(u+v+1)+1 : ℕ) : ℝ) = 2*((u+v : ℕ) : ℝ)+3 := by
    push_cast
    ring
  have hcover' : (((Y'+u•X'-v•X').image (roundPoint (delta/2))).card : ℝ) ≤
      (2*((u+v : ℕ) : ℝ)+3)^2*(2*C^(2*(u+v)+3)/t)*(Y.card : ℝ) := by
    have hh := hcover u v
    change _ ≤ ((2*(u+v+1)+1 : ℕ) : ℝ)^2*(C^(2*(u+v+1))/theta)*(Y.card : ℝ) at hh
    rw [hcosteq, hfloor] at hh
    exact hh
  calc
    _ ≤ (2*((u+v : ℕ) : ℝ)+3)^2*(2*C^(2*(u+v)+3)/t)*(Y.card : ℝ) := hcover'
    _ ≤ ((2*((u+v : ℕ) : ℝ)+3)^2*(2 : ℝ)^(961*(u+v))*H^(290*(u+v))/p^(1161*(u+v)))*
        (Y.card : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiter' (by positivity : 0 ≤ (2*((u+v : ℕ) : ℝ)+3)^2))
        (Nat.cast_nonneg Y.card)
      simpa only [mul_div_assoc, mul_assoc] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_right (hnumC (u+v) hs) (Nat.cast_nonneg _)

/-- Literal Euclidean closed near-sum energy, with each quadruple counted once. -/
def euclideanNearSumEnergy (X Y : Finset (ℝ×ℝ)) (delta : ℝ) : ℕ :=
  (((X.product Y).product (X.product Y)).filter (fun p =>
    ((p.1.1+p.1.2).1-(p.2.1+p.2.2).1)^2+
      ((p.1.1+p.1.2).2-(p.2.1+p.2.2).2)^2 ≤ delta^2)).card

lemma euclidean_near_energy_le_coordinate (X Y : Finset (ℝ×ℝ)) {delta : ℝ}
    (hdelta : 0 < delta) :
    euclideanNearSumEnergy X Y delta ≤
      (coordinateNearPairs (X.product Y) (fun p => p.1+p.2) delta).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hclose⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_,?_⟩
  · have hh := sq_nonneg ((p.1.1+p.1.2).2-(p.2.1+p.2.2).2)
    have ha := sq_abs ((p.1.1+p.1.2).1-(p.2.1+p.2.2).1)
    have hb := abs_nonneg ((p.1.1+p.1.2).1-(p.2.1+p.2.2).1)
    dsimp only at *
    nlinarith
  · have hh := sq_nonneg ((p.1.1+p.1.2).1-(p.2.1+p.2.2).1)
    have ha := sq_abs ((p.1.1+p.1.2).2-(p.2.1+p.2.2).2)
    have hb := abs_nonneg ((p.1.1+p.1.2).2-(p.2.1+p.2.2).2)
    dsimp only at *
    nlinarith

/-- Genuine original-set planar dyadic asymmetric BSG. The only geometric
inputs are bounded coordinate support, Euclidean separation and actual
Euclidean near-sum energy. It constructs original subsets of both sources
and controls the half-mesh cover of every coupled iterated sum-difference.
K and the mesh threshold are chosen before the energy parameter nu. -/
theorem original_planar_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ X Y : Finset (ℝ×ℝ), X.Nonempty → Y.Nonempty →
      (∀ x ∈ X, |x.1| ≤ 4 ∧ |x.2| ≤ 4) →
      (∀ y ∈ Y, |y.1| ≤ 1 ∧ |y.2| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        (((2 : ℝ)^n)⁻¹)^2 ≤ (x.1-y.1)^2+(x.2-y.2)^2) →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
        (((2 : ℝ)^n)⁻¹)^2 ≤ (x.1-y.1)^2+(x.2-y.2)^2) →
      nu*(X.card : ℝ)^2*(Y.card : ℝ) ≤
        (euclideanNearSumEnergy X Y (((2 : ℝ)^n)⁻¹) : ℝ) →
      ∃ X' Y' : Finset (ℝ×ℝ), X' ⊆ X ∧ Y' ⊆ Y ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (X.card : ℝ) ≤ X'.card ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (Y.card : ℝ) ≤ Y'.card ∧
        ∀ u v : ℕ,
          (((Y'+u•X'-v•X').image (roundPoint (((2 : ℝ)^n)⁻¹/2))).card : ℝ) ≤
            ((((2 : ℝ)^n)⁻¹)^(-epsilon*((u+v : ℕ) : ℝ))/nu^(K*(u+v)))*
              (Y.card : ℝ) := by
  obtain ⟨K,n0,hK,hmain⟩ := coordinate_planar_dyadic_bsg hepsilon
  refine ⟨K,n0,hK,?_⟩
  intro n hn nu hnu hnu1 X Y hX hY hXbound hYbound hXsep hYsep he
  have hdelta : 0 < ((2 : ℝ)^n)⁻¹ := by positivity
  apply hmain n hn nu hnu hnu1 X Y hX hY hXbound hYbound
  · exact fun x hx y hy hne => max_norm_separation_of_euclidean_squared hdelta (hXsep x hx y hy hne)
  · exact fun x hx y hy hne => max_norm_separation_of_euclidean_squared hdelta (hYsep x hx y hy hne)
  · exact he.trans (Nat.cast_le.mpr (euclidean_near_energy_le_coordinate X Y hdelta))

end PlanarOriginalDyadicBSG
