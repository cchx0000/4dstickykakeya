import Theorems.Thm_StickyKakeya4_native_paid_third_record
import Theorems.Thm_StickyKakeya4_native_new_cut_output_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section
namespace NativePaidThirdOutput
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

/-- The existing same-T paid record supplies the Y constant, including the
square of the NEW cuts. Its full third relation count d and the actual S.card
are retained in F3 and Q3. The caller obtains this record from
paid_record_from_budget using HasBudget at those identical parameters.
The cutoff below is chosen before D, T, the rank and the prepared depths.
The AD carrier and mesh remain the ORIGINAL quotient centers and mu m.
Only the constant is paid here; configured coarse-Y recoding is a later reader. -/
theorem exists_paid_record_output_cutoff (Kcoh Ksupport g : ℕ)
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
      let mu := physicalMesh m (phaseDepth m) / 8
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hdim mu
      let field := fixedField D a m ell plane Sq Fraw
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let F3 := refinementCost (d + 2) (J + 1) L3
      let KXY := xyConstant D.thickness zeta population PL PU lambda (G * Cpre * (F3 : ℝ)) Qref Q3 J m
      let KY := quotientConstant (ell - 1) (4 - ell) (1 / ((32 : ℝ) ^ (ell - 1) * CX)) KXY
        (3 - extremalExponent)
      KY ≤ deltaY ^ (-eta53) ∧
        ∀ height : ℤ, ADBounds
          (((productSlice (T.image (fun z => pxy D a m ell p P hP hell hell4 hdim field z.2)) height).image
            Prod.snd).image (NativeQuotientGridCenters.center (NativeReferenceXYGridPoints.mu m)))
          (NativeReferenceXYGridPoints.mu m) (deltaY ^ (-eta53)) (4 - (ell : ℝ) - extremalExponent) := by
  obtain ⟨D0, hD0, hD01, Hcut⟩ := exists_Y_output_cutoff Kcoh Ksupport g
    meshConstant row eta53 hC hrow heta53
  refine ⟨D0, hD0, hD01, ?_⟩
  intro n d J ell D zeta a m R0 plane E Hgraph S T P hP hell hell4 hdim Fraw p
    population PL PU Qref lambda G Cpre t L3 Rel3 CX epsilonPaid r loss rankLoss metric epsilonGeom
    q Delta deltaY depths hr hr1 hloss hd hmetric he0 he4 hPaid hLip hsmall hstopLo hstopHi hHeight
    hq hCpre hidentity hY hYD hDsmall hbase hnu hmargin Hdata mu Sq field Q3 F3 KXY KY
  have hD : 0 < Delta := hY.trans_le hYD
  have hpayment := paid_Y_constant_at_output Kcoh Ksupport (4 - ell) g R0 m (by omega)
    meshConstant row r loss rankLoss metric epsilonGeom extremalExponent epsilonPaid Delta
    depths (quotientCost q) Cpre hC hrow hr hr1 hloss hd hmetric he0 he4 hPaid hLip
    hsmall hstopLo hstopHi hHeight (quotientCost_pos hq) hCpre hidentity hD hbase hnu
  have hbound := Hcut Delta deltaY
    ((max 1 (Cpre / quotientCost q)) ^ 2 * ((64 : ℝ) / ((2 ^ m : ℕ) : ℝ)) ^ (-epsilonPaid))
    (newExponent Kcoh epsilonGeom loss rankLoss) epsilonPaid hY hYD hDsmall hmargin hpayment
  have hKY : KY ≤ (max 1 (Cpre / quotientCost q)) ^ 2 *
      (NativeReferenceXYGridPoints.rho m) ^ (-epsilonPaid) := Hdata.2.2.2.1
  refine ⟨hKY.trans hbound, ?_⟩
  intro height
  have hM : 0 < max 1 (Cpre / quotientCost q) := lt_of_lt_of_le (by norm_num) Hdata.2.1
  exact ADBounds_mono_constant _ (NativeReferenceXYGridPoints.mu_pos m)
    (by have hrho := NativeReferenceXYGridPoints.rho_pos m; positivity) hbound
    (Hdata.2.2.2.2.2.1 height)

end NativePaidThirdOutput
