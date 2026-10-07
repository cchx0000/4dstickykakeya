/- UNVERIFIED actual coefficient reader. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_paid_third_record
import Theorems.Thm_StickyKakeya4_native_new_cut_output_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativeThirdXYUnionBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeJointUniformCoarseRelations NativeSquaredGrainQueries NativeRetainedSliceCore
open NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry NativeHorizontalGrainSlice
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers
open NativeGrainQuotientFibers NativeReferenceXYGridField NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeThirdXYData NativeQuotientLatticeTransport NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent
open FiniteVoronoiRealADCoarsening
open scoped Matrix.Norms.Elementwise

open NativeThirdXYSourceData NativeTwoMapRetainedSliceActualCaps NativeSliceClassBalls

open NativePaidThirdRecord NativePaidThirdData NativeActualNewCutBudget NativeNewCutOutputBudget
open NativeSharpXPowerAlgebra NativeRetainedSliceBudgetAlgebra

theorem exists_raw_XY_square_cutoff (Kcoh Ksupport g : ℕ)
    (meshConstant row eta53 : ℝ) (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row)
    (heta53 : 0 < eta53) :
    ∃ D0 : ℝ, 0 < D0 ∧ D0 ≤ 1 ∧
    ∀ (n d J ell : ℕ) (D : FiniteScaleSource n) (zeta a : ℝ) (m R0 : ℕ)
      (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
      (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
      (hdim : Module.finrank ℝ P = ell - 1)
      (Fraw : ℤ → Matrix (Fin (4 - ell)) (Fin (ell - 1)) ℝ)
      (p : Parent) (population PL PU : ℝ) (Qref : ℕ)
      (lambda G Cpre t : ℝ) (L3 : ℕ)
      (Rel3 : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
      (CX epsilonPaid r loss rankLoss metric epsilonGeom q Delta deltaY : ℝ)
      (depths : Fin Kcoh → ℕ),
      0 < r → r ≤ 1 → 0 ≤ loss → 0 ≤ rankLoss → 0 ≤ metric →
      0 ≤ epsilonGeom → epsilonGeom ≤ 1 / 4 → 0 ≤ epsilonPaid →
      metric ≤ r ^ (-2 * epsilonGeom) →
      (64 : ℝ) / ((2 ^ m : ℕ) : ℝ) ≤ 1 →
      3072 * r ≤ ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ 2 →
      ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ 2 ≤ 6144 * r →
      ((8 * R0 : ℕ) : ℝ) ≤
        1280 * (((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) / 64) ^ (-2 * epsilonGeom) →
      0 < q → 0 < Cpre →
      Cpre = quotientCost q *
        (newCutCharge Kcoh Ksupport (4 - ell) g R0 meshConstant row r loss rankLoss metric
          NativeFixedCompactKakeyaExponent.extremalExponent
          (fun j => 64 / ((2 ^ (depths j) : ℕ) : ℝ)) : ℝ) →
      0 < deltaY → deltaY ≤ Delta → Delta ≤ D0 →
      64 * Delta ≤ 2 * max
        ((5 / 4 : ℝ) * ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ (1 - 2 * epsilonGeom))
        ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) →
      newExponent Kcoh epsilonGeom loss rankLoss ≤ 1 / 2 →
      8 * newExponent Kcoh epsilonGeom loss rankLoss + 2 * epsilonPaid ≤ eta53 / 2 →
      HasPaidThirdXYSourceData (J := J) D zeta a m plane E Hgraph S T P hP hell hell4 hdim Fraw p
        population PL PU Qref lambda G Cpre t L3 Rel3 CX epsilonPaid (max 1 (Cpre / quotientCost q)) →
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let F3 := refinementCost (d + 2) (J + 1) L3
      let KXY := xyConstant D.thickness zeta population PL PU lambda (G * Cpre * (F3 : ℝ)) Qref Q3 J m
      KXY^2 ≤ deltaY^(-eta53) := by
  obtain ⟨D0, hD0, hD01, Hcut⟩ := exists_Y_output_cutoff Kcoh Ksupport g
    meshConstant row eta53 hC hrow heta53
  refine ⟨D0, hD0, hD01, ?_⟩
  intro n d J ell D zeta a m R0 plane E Hgraph S T P hP hell hell4 hdim Fraw p
    population PL PU Qref lambda G Cpre t L3 Rel3 CX epsilonPaid r loss rankLoss metric epsilonGeom
    q Delta deltaY depths hr hr1 hloss hd hmetric he0 he4 hPaid hLip hsmall hstopLo hstopHi hHeight
    hq hCpre hidentity hY hYD hDsmall hbase hnu hmargin Hdata Q3 F3 KXY
  have hD : 0 < Delta := hY.trans_le hYD
  have hpayment := paid_Y_constant_at_output Kcoh Ksupport (4 - ell) g R0 m (by omega)
    meshConstant row r loss rankLoss metric epsilonGeom extremalExponent epsilonPaid Delta
    depths (quotientCost q) Cpre hC hrow hr hr1 hloss hd hmetric he0 he4 hPaid hLip
    hsmall hstopLo hstopHi hHeight (quotientCost_pos hq) hCpre hidentity hD hbase hnu
  have hbound := Hcut Delta deltaY
    ((max 1 (Cpre / quotientCost q)) ^ 2 * ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ (-epsilonPaid))
    (newExponent Kcoh epsilonGeom loss rankLoss) epsilonPaid hY hYD hDsmall hmargin hpayment
  have hKXY : KXY ≤ (max 1 (Cpre / quotientCost q))*
      (NativeReferenceXYGridPoints.rho m)^(-(epsilonPaid/2)) := Hdata.2.2.1
  have hKXY0 : 0 ≤ KXY := (by norm_num : (0:ℝ)≤1).trans (xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _)
  have hsq := pow_le_pow_left₀ hKXY0 hKXY 2
  have hpower : ((NativeReferenceXYGridPoints.rho m)^(-(epsilonPaid/2)))^(2:ℕ)=
      (NativeReferenceXYGridPoints.rho m)^(-epsilonPaid) := by
    rw [←Real.rpow_mul_natCast (NativeReferenceXYGridPoints.rho_pos m).le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [mul_pow,hpower] at hsq
  exact hsq.trans hbound

/-- Transport the actual raw XY-square bound to the final relative sigma.
This never infers a coefficient upper from an AD assertion. -/
theorem raw_square_at_sigma {eps sigma KXY chi etaUnion Eunion : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hsigma : 0 < sigma)
    (_hchi : 0 < chi) (hE : 0 < Eunion)
    (hscale : sigma ≤ eps^(chi/2)) (heta : etaUnion ≤ chi*Eunion/8)
    (hRaw : KXY^2 ≤ eps^(-etaUnion)) :
    KXY^2 ≤ sigma^(-(Eunion/4)) := by
  have hExponent : eps^(-etaUnion) ≤ eps^(-(chi*Eunion/8)) :=
    Real.rpow_le_rpow_of_exponent_ge heps heps1 (neg_le_neg heta)
  have hPower : eps^(-(chi*Eunion/8))=(eps^(chi/2))^(-(Eunion/4)) := by
    rw [←Real.rpow_mul heps.le]
    congr 1
    ring
  have hScale := Real.rpow_le_rpow_of_nonpos hsigma hscale
    (show -(Eunion/4) ≤ 0 by positivity)
  exact hRaw.trans (hExponent.trans (hPower.trans_le hScale))

end NativeThirdXYUnionBudget
