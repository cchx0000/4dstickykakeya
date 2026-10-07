import Theorems.Thm_StickyKakeya4_native_all_dyadic_reference_angular_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeAngularBottomEndpoint
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeAngularDyadicInterpolation NativeAllDyadicReferenceAngularUpper NativeConditionalGridPowerCost

/-- The true lower spatial mesh is mu=Rho/64. Truncating both depth
parameters at m keeps their ratio no larger; exactly64^3 angular descendants
pay the whole missing bottom interval, with no additional source menu. -/
theorem extend_bottom {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (hm : 6≤ m)
    (p : Parent) (E : Finset (Fin n × Index)) (C kappa : ℝ) (hC : 0≤ C) (hk : 0≤ kappa)
    (H : ∀s t : ℕ,6≤ t → t≤ s → s≤ m →
      ∀(cell : Index) (center : EuclideanSpace ℝ (Fin 3)),
        (∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell) →
        (∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) →
        ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          C*((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^kappa)
    (s t : ℕ) (ht : 6≤ t) (hts : t≤ s) (hsm : s≤ m+6)
    (cell : Index) (center : EuclideanSpace ℝ (Fin 3))
    (hCell : ∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell)
    (hBall : ∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t:ℕ):ℝ)) :
    ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
      (64:ℝ)^3*C*((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^kappa := by
  let s0 := min s m
  let t0 := min t m
  have hs0 : s0≤ s := min_le_left _ _
  have ht0 : t0≤ t := min_le_left _ _
  let cell0 : Index := fun j => cell j/(2^(s-s0):ℕ)
  have hCell0 : ∀z∈E,physicalCell D a (2^m) (2^s0) p z.2=cell0 := by
    intro z hz
    exact (physical_ancestor D a (2^m) p hs0 z.2).symm.trans
      (congrArg (fun v : Index => fun j => v j/(2^(s-s0):ℕ)) (hCell z hz))
  have hBall0 : ∀z∈E,dist (localSlope D (2^m) p z.1) center≤ 64/((2^t0:ℕ):ℝ) :=
    fun z hz => (hBall z hz).trans (width_mono ht0)
  have hts0 : t0≤ s0 := min_le_min hts le_rfl
  have hCoarse := H s0 t0 (by dsimp [t0]; omega) hts0 (min_le_right _ _) cell0 center hCell0 hBall0
  have hFine := bottom_angular_interpolation D (2^m) p E hs0 (by dsimp [s0]; omega)
  have hRatio : ((64:ℝ)/((2^t0:ℕ):ℝ))/(64/((2^s0:ℕ):ℝ))≤
      (64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)) := by
    rw [dyadic_width_ratio hts0,dyadic_width_ratio hts]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ))
      (show s0-t0≤ s-t by dsimp [s0,t0]; omega)
  have hPow := Real.rpow_le_rpow (by positivity : 0≤
      ((64:ℝ)/((2^t0:ℕ):ℝ))/(64/((2^s0:ℕ):ℝ))) hRatio hk
  exact hFine.trans (by
    have hh := mul_le_mul_of_nonneg_left
      (hCoarse.trans (mul_le_mul_of_nonneg_left hPow hC)) (by norm_num : (0:ℝ)≤ 64^3)
    simpa only [mul_assoc] using hh)

end NativeAngularBottomEndpoint
