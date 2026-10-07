import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_final

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeReferenceSliceBudgetReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCombinedParentProfiles NativeReferenceSliceClassBounds NativeColumnPopulationBounds
open NativeReferenceSliceBudgetAlgebra NativeActivePhasePopulation NativeAllTwoScaleConfiguration

/-- The normalized history fraction is only an algebraic abbreviation of
the literal original E2 weight used by the actual parent selector. -/
lemma population_mass_ratio (delta eta lambda W N F G : ℝ) :
    population delta eta lambda (W/N) F G = (lambda*W/(2*F*G*N))*delta^eta := by
  unfold population
  ring

/-- Read the already-derived same-R parent profile into the exact scalar
coefficients paid by the source budget. No profile inequality is added. -/
theorem parent_profiles_readback {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (level m f : ℕ) (p : Parent)
    (mu lambda tau seed c2 : ℝ)
    (HP : HasParentProfiles h R E1 E2 a level m f p (mu/rowConstant) lambda tau seed c2) :
    HasColumnPowerProfile D a m f E2 p
      (profileLower D.thickness mu (columnEpsilon D.thickness lambda (seed/8) c2)
        tau (seed/8) (min (boundaryWindow tau) ((tau/16)/1000)))
      (profileUpper D.thickness (columnEpsilon D.thickness lambda (seed/8) c2) tau) := by
  have hh := HP.2.2.2.2.2.2
  dsimp only [HasColumnPowerProfile,profileLower,profileUpper,columnEpsilon,relativeWidth]
  simpa only [mul_assoc,neg_mul] using hh

end NativeReferenceSliceBudgetReadback
