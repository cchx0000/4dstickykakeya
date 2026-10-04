import Theorems.Thm_StickyKakeya4_native_literal_scalar_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace NativeUniformOutputBounds
open NativeNormalizedParentOutput NativeLiteralScalarBounds NativeDyadicTubeStopping
open ShearedGridADReference ShearedGridTubeReference SmallFiberAlignment FractionalFiberAlignment
open LiteralAffineFiberCoordinates ActualScalarADProfiles RealScalarADInterpolation
open NormalizedQuantizedPatches NativeAmbientADGeometry

noncomputable section

/-- Convert an actual lower counting estimate using one proved reciprocal-density
majorant. No normalization of the underlying finite point family is performed. -/
lemma lower_count_absorption {d A J X C x n : ℝ}
    (hA : 0 < A) (hX : 0 ≤ X) (hC : 0 < C)
    (hx : 0 ≤ x) (hn : 0 ≤ n) (hrec : 1 ≤ X*d)
    (hcost : J*A*X ≤ C) (hcount : (d/A)*x ≤ J*n) : x/C ≤ n := by
  have hc : d*x ≤ (J*n)*A := by
    rw [div_mul_eq_mul_div] at hcount
    exact (div_le_iff₀ hA).mp hcount
  apply (div_le_iff₀ hC).mpr
  calc
    x = 1*x := by ring
    _ ≤ (X*d)*x := mul_le_mul_of_nonneg_right hrec hx
    _ = X*(d*x) := by ring
    _ ≤ X*((J*n)*A) := mul_le_mul_of_nonneg_left hc hX
    _ = (J*A*X)*n := by ring
    _ ≤ C*n := mul_le_mul_of_nonneg_right hcost hn
    _ = n*C := by ring

/-- The raw fiber grid is 64 times finer than the separated output mesh. -/
lemma raw_power_eq {mu b r : ℝ} (hmu : 0 < mu) (hb : 0 < b) (hr : 0 ≤ r) (s : ℝ) :
    (r/(mu/(64*b)))^s = (64:ℝ)^s*(r/(64*(mu/(64*b))))^s := by
  have he : r/(mu/(64*b)) = 64*(r/(64*(mu/(64*b)))) := by field_simp
  rw [he, Real.mul_rpow (by norm_num) (by positivity)]

/-- Uniform real-radius bounds on the literal normalized point family and
scalar fibers. The mesh is the actual separated mesh, in every clause. -/
structure UniformBounds (P : Finset Vertex) (mu angle b t s C : ℝ) (c : Plane) : Prop where
  ambient : ∀ p ∈ P, ∀ r, 64*(mu/(64*b)) ≤ r → r ≤ 1 →
    (r/(64*(mu/(64*b))))^t/C ≤
      ballCount (P.image (actualPoint mu angle (64*b) c)) (actualPoint mu angle (64*b) c p) r ∧
    ballCount (P.image (actualPoint mu angle (64*b) c)) (actualPoint mu angle (64*b) c p) r ≤
      C*(r/(64*(mu/(64*b))))^t
  fibers : ∀ y x r, x ∈ fiberAt P mu angle (64*b) c y → 64*(mu/(64*b)) ≤ r → r ≤ 1 →
    (r/(64*(mu/(64*b))))^s/C ≤ ballCount (fiberAt P mu angle (64*b) c y) x r ∧
    ballCount (fiberAt P mu angle (64*b) c y) x r ≤ C*(r/(64*(mu/(64*b))))^s
  quotient : ∀ y r, y ∈ quotientCoordinates P mu angle (64*b) c →
    64*(mu/(64*b)) ≤ r → r ≤ 1 →
    (r/(64*(mu/(64*b))))^(t-s)/C ≤ ballCount (quotientCoordinates P mu angle (64*b) c) y r ∧
    ballCount (quotientCoordinates P mu angle (64*b) c) y r ≤ C*(r/(64*(mu/(64*b))))^(t-s)
  tubes : ∀ rho tau, 64*(mu/(64*b)) ≤ rho → rho ≤ tau →
    TraceBound (P.image (fun k => affine c (64*b) (realized mu angle k))) rho tau (C*(tau/rho)^s)

/-- All explicit costs can be absorbed into a single loss on the same original
quantizer image. The hypotheses are numerical bounds on existing coefficients. -/
theorem AllRealBounds.to_uniform {P : Finset Vertex} {M H Q L : ℕ}
    {mu angle b t s d Bad Bcol Btube Htube C X : ℝ} {c : Plane}
    (B : AllRealBounds P M H Q L mu angle b t s d Bad Bcol Btube Htube c)
    (hmu : 0 < mu) (hb : 0 < b) (_hd : 0 < d) (hC : 0 < C) (hX : 0 ≤ X)
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hCmp : 0 < comparisonCost (H+1) L Q) (hBad : 0 < Bad)
    (hBcol : 0 < Bcol) (hBtube : 0 < Btube) (hrec : 1 ≤ X*d)
    (hlA : realInterpolationLoss M H t * (comparisonCost (H+1) L Q*Bad)*X ≤ C)
    (hlF : fullInterpolationLoss M H s * (comparisonCost (H+1) L Q*Bcol*Btube)*X ≤ C)
    (hlQ : fullInterpolationLoss M H (t-s) * (comparisonCost (H+1) L Q*Bad*Btube)*X ≤ C)
    (huA : realInterpolationLoss M H t*(9*Bad)*(128:ℝ)^t ≤ C)
    (huF : fullInterpolationLoss M H s*Btube*(64:ℝ)^s ≤ C)
    (huQ : fullInterpolationLoss M H (t-s) *
      max ((comparisonCost (H+1) L Q*Bcol*Bad*Btube)/d)
        ((comparisonCost (H+1) L Q*Bcol*Bad)/d) * (64:ℝ)^(t-s) ≤ C)
    (huT : 170100*Htube*(2:ℝ)^s ≤ C) :
    UniformBounds P mu angle b t s C c := by
  have hmesh : 0 < 64*(mu/(64*b)) := by positivity
  have hpow {r e : ℝ} (hr : 64*(mu/(64*b)) ≤ r) :
      0 ≤ (r/(64*(mu/(64*b))))^e := by
    have hr0 : 0 ≤ r := hmesh.le.trans hr
    positivity
  have hraw {r e : ℝ} (hr : 64*(mu/(64*b)) ≤ r) (he : 0 ≤ e) :
      (r/(64*(mu/(64*b))))^e ≤ (r/(mu/(64*b)))^e := by
    rw [raw_power_eq hmu hb (le_trans hmesh.le hr)]
    exact le_mul_of_one_le_left (hpow hr) (Real.one_le_rpow (by norm_num) he)
  refine ⟨?_,?_,?_,?_⟩
  · intro p hp r hrlo hrhi
    have hh := B.ambient p hp r hrlo hrhi
    constructor
    · exact lower_count_absorption (mul_pos hCmp hBad) hX hC (hpow hrlo)
        (by unfold ballCount; positivity) hrec hlA hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right huA (hpow hrlo))
  · intro y x r hx hrlo hrhi
    have hr0 : 0 ≤ r := hmesh.le.trans hrlo
    have hh := NativeLiteralScalarBounds.AllRealBounds.scalar_fibers B hmu hb hx hrlo hrhi
    constructor
    · have hc := lower_count_absorption (mul_pos (mul_pos hCmp hBcol) hBtube) hX hC
        (show 0 ≤ (r/(mu/(64*b)))^s by positivity)
        (show 0 ≤ ballCount (fiberAt P mu angle (64*b) c y) x r by unfold ballCount; positivity)
        hrec hlF hh.1
      exact (div_le_div_of_nonneg_right (hraw hrlo hs) hC.le).trans hc
    · rw [raw_power_eq hmu hb (le_trans hmesh.le hrlo)] at hh
      calc
        _ ≤ fullInterpolationLoss M H s*Btube*((64:ℝ)^s*(r/(64*(mu/(64*b))))^s) := hh.2
        _ = (fullInterpolationLoss M H s*Btube*(64:ℝ)^s)*(r/(64*(mu/(64*b))))^s := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right huF (hpow hrlo)
  · intro y r hy hrlo hrhi
    have hr0 : 0 ≤ r := hmesh.le.trans hrlo
    have hh := NativeLiteralScalarBounds.AllRealBounds.scalar_quotient B hy hrlo hrhi
    constructor
    · have hc := lower_count_absorption (mul_pos (mul_pos hCmp hBad) hBtube) hX hC
        (show 0 ≤ (r/(mu/(64*b)))^(t-s) by positivity)
        (show 0 ≤ ballCount (quotientCoordinates P mu angle (64*b) c) y r by unfold ballCount; positivity)
        hrec hlQ hh.1
      exact (div_le_div_of_nonneg_right (hraw hrlo (sub_nonneg.mpr hst)) hC.le).trans hc
    · rw [raw_power_eq hmu hb (le_trans hmesh.le hrlo)] at hh
      calc
        _ ≤ fullInterpolationLoss M H (t-s)*
          max ((comparisonCost (H+1) L Q*Bcol*Bad*Btube)/d)
            ((comparisonCost (H+1) L Q*Bcol*Bad)/d)*
              ((64:ℝ)^(t-s)*(r/(64*(mu/(64*b))))^(t-s)) := hh.2
        _ = (fullInterpolationLoss M H (t-s)*
          max ((comparisonCost (H+1) L Q*Bcol*Bad*Btube)/d)
            ((comparisonCost (H+1) L Q*Bcol*Bad)/d)*(64:ℝ)^(t-s))*
              (r/(64*(mu/(64*b))))^(t-s) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right huQ (hpow hrlo)
  · intro rho tau hrho hrt T
    have hr0 : 0 < rho := hmesh.trans_le hrho
    have ht0 : 0 ≤ tau := hr0.le.trans hrt
    exact (B.tubes rho tau hrho hrt T).trans
      (mul_le_mul_of_nonneg_right huT (by positivity))


lemma majorant_products {J P B A T X : ℝ}
    (hJ : 1 ≤ J) (hP : 1 ≤ P) (hB : 1 ≤ B) (hA : 1 ≤ A)
    (hT : 1 ≤ T) (hX : 1 ≤ X) :
    J*P*A*X ≤ J*P*B*A*T*X ∧
    J*P*B*T*X ≤ J*P*B*A*T*X ∧
    J*P*A*T*X ≤ J*P*B*A*T*X ∧
    J*A ≤ J*P*B*A*T*X ∧ J*T ≤ J*P*B*A*T*X := by
  have hJ0 := zero_le_one.trans hJ
  have hP0 := zero_le_one.trans hP
  have hB0 := zero_le_one.trans hB
  have hA0 := zero_le_one.trans hA
  have hT0 := zero_le_one.trans hT
  have hX0 := zero_le_one.trans hX
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      _ = J*P*1*A*1*X := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = J*P*B*1*T*X := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = J*P*1*A*T*X := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = J*1*1*A*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = J*1*1*1*T*1 := by ring
      _ ≤ _ := by gcongr

/-- A single common majorant absorbs the literal six coefficients, including
both 64-fold scalar mesh conversions. -/
theorem AllRealBounds.to_uniform_majorants {P : Finset Vertex} {M H Q L : ℕ}
    {mu angle b t s d Bad Bcol Btube Htube J0 Cmp0 A0 B0 T0 X : ℝ} {c : Plane}
    (B : AllRealBounds P M H Q L mu angle b t s d Bad Bcol Btube Htube c)
    (hmu : 0 < mu) (hb : 0 < b) (hd : 0 < d) (hs : 0 ≤ s) (hst : s ≤ t) (ht2 : t ≤ 2)
    (hCmp : 0 < comparisonCost (H+1) L Q) (hBad : 0 < Bad)
    (hBcol : 0 < Bcol) (hBtube : 0 < Btube)
    (hJ0 : 1 ≤ J0) (hCmp0 : 1 ≤ Cmp0) (hA0 : 1 ≤ A0) (hB0 : 1 ≤ B0)
    (hT0 : 1 ≤ T0) (hX : 1 ≤ X) (hrec : 1 ≤ X*d)
    (hCt : comparisonCost (H+1) L Q ≤ Cmp0) (hAt : Bad ≤ A0)
    (hBt : Bcol ≤ B0) (hTt : Btube ≤ T0)
    (hJt : realInterpolationLoss M H t ≤ J0)
    (hJs : fullInterpolationLoss M H s ≤ J0)
    (hJq : fullInterpolationLoss M H (t-s) ≤ J0)
    (huT : 170100*Htube*(2:ℝ)^s ≤ (9*128^2:ℝ)*J0*Cmp0*B0*A0*T0*X) :
    UniformBounds P mu angle b t s ((9*128^2:ℝ)*J0*Cmp0*B0*A0*T0*X) c := by
  let E := J0*Cmp0*B0*A0*T0*X
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 < (9*128^2:ℝ)*J0*Cmp0*B0*A0*T0*X := by positivity
  have hEbig : E ≤ (9*128^2:ℝ)*E := by nlinarith only [hE]
  have hE64 : (64:ℝ)^2*E ≤ (9*128^2:ℝ)*E := by nlinarith only [hE]
  have hproducts := majorant_products hJ0 hCmp0 hB0 hA0 hT0 hX
  have hJt0 : 0 ≤ realInterpolationLoss M H t :=
    zero_le_one.trans (FullNormalizedAmbientAD.realInterpolationLoss_ge_one M H (hs.trans hst))
  have hJs0 : 0 ≤ fullInterpolationLoss M H s :=
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 64) s).trans (le_max_right _ _)
  have hJq0 : 0 ≤ fullInterpolationLoss M H (t-s) :=
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 64) (t-s)).trans (le_max_right _ _)
  have hrecip : 1/d ≤ X := (div_le_iff₀ hd).mpr (by nlinarith only [hrec])
  have hcoef : max ((comparisonCost (H+1) L Q*Bcol*Bad*Btube)/d)
      ((comparisonCost (H+1) L Q*Bcol*Bad)/d) ≤ Cmp0*B0*A0*T0*X := by
    have hi : d⁻¹ ≤ X := by simpa only [one_div] using hrecip
    apply max_le
    · rw [div_eq_mul_inv]
      apply mul_le_mul _ hi (inv_nonneg.mpr hd.le) (by positivity)
      gcongr
    · rw [div_eq_mul_inv]
      apply mul_le_mul _ hi (inv_nonneg.mpr hd.le) (by positivity)
      calc
        _ = comparisonCost (H+1) L Q*Bcol*Bad*1 := by ring
        _ ≤ Cmp0*B0*A0*T0 := by gcongr
  apply AllRealBounds.to_uniform B hmu hb hd hC (zero_le_one.trans hX) hs hst hCmp hBad hBcol hBtube hrec
  · calc
      _ ≤ J0*(Cmp0*A0)*X := by gcongr
      _ = J0*Cmp0*A0*X := by ring
      _ ≤ E := hproducts.1
      _ ≤ _ := by simpa only [E, mul_assoc] using hEbig
  · calc
      _ ≤ J0*(Cmp0*B0*T0)*X := by gcongr
      _ = J0*Cmp0*B0*T0*X := by ring
      _ ≤ E := hproducts.2.1
      _ ≤ _ := by simpa only [E, mul_assoc] using hEbig
  · calc
      _ ≤ J0*(Cmp0*A0*T0)*X := by gcongr
      _ = J0*Cmp0*A0*T0*X := by ring
      _ ≤ E := hproducts.2.2.1
      _ ≤ _ := by simpa only [E, mul_assoc] using hEbig
  · have hp : (128:ℝ)^t ≤ (128:ℝ)^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 128) ht2
    calc
      _ ≤ J0*(9*A0)*(128:ℝ)^2 := by gcongr
      _ = (9*128^2:ℝ)*(J0*A0) := by norm_num; ring
      _ ≤ (9*128^2:ℝ)*E := mul_le_mul_of_nonneg_left hproducts.2.2.2.1 (by norm_num)
      _ = _ := by dsimp [E]; ring
  · have hp : (64:ℝ)^s ≤ (64:ℝ)^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 64) (hst.trans ht2)
    calc
      _ ≤ J0*T0*(64:ℝ)^2 := by gcongr
      _ = (64:ℝ)^2*(J0*T0) := by ring
      _ ≤ (64:ℝ)^2*E := mul_le_mul_of_nonneg_left hproducts.2.2.2.2 (by norm_num)
      _ ≤ _ := by simpa only [E, mul_assoc] using hE64
  · have hp : (64:ℝ)^(t-s) ≤ (64:ℝ)^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 64) (show t-s ≤ 2 by linarith)
    calc
      _ ≤ J0*(Cmp0*B0*A0*T0*X)*(64:ℝ)^2 := by gcongr
      _ = (64:ℝ)^2*E := by dsimp [E]; ring
      _ ≤ _ := by simpa only [E, mul_assoc] using hE64
  · exact huT


/-- Enlarge the proved common loss without changing the original image. -/
theorem UniformBounds.mono {P : Finset Vertex} {mu angle b t s C C' : ℝ} {c : Plane}
    (B : UniformBounds P mu angle b t s C c)
    (hmu : 0 < mu) (hb : 0 < b) (hC : 0 < C) (hCC : C ≤ C') :
    UniformBounds P mu angle b t s C' c := by
  have hmesh : 0 < 64*(mu/(64*b)) := by positivity
  have hp {r e : ℝ} (hr : 64*(mu/(64*b)) ≤ r) : 0 ≤ (r/(64*(mu/(64*b))))^e := by
    have hr0 : 0 ≤ r := hmesh.le.trans hr
    positivity
  refine ⟨?_,?_,?_,?_⟩
  · intro p hx r hrlo hrhi
    have h := B.ambient p hx r hrlo hrhi
    exact ⟨(div_le_div_of_nonneg_left (hp hrlo) hC hCC).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right hCC (hp hrlo))⟩
  · intro y x r hx hrlo hrhi
    have h := B.fibers y x r hx hrlo hrhi
    exact ⟨(div_le_div_of_nonneg_left (hp hrlo) hC hCC).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right hCC (hp hrlo))⟩
  · intro y r hy hrlo hrhi
    have h := B.quotient y r hy hrlo hrhi
    exact ⟨(div_le_div_of_nonneg_left (hp hrlo) hC hCC).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right hCC (hp hrlo))⟩
  · intro rho tau hrho hrt T
    have hr0 : 0 < rho := hmesh.trans_le hrho
    have ht0 : 0 ≤ tau := hr0.le.trans hrt
    exact (B.tubes rho tau hrho hrt T).trans (mul_le_mul_of_nonneg_right hCC (by positivity))


end
end NativeUniformOutputBounds
