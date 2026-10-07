/- UNVERIFIED same-third history coefficient readback. No strict check has run. -/
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_reference_slice_budget_readback
import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeActualThirdHistoryReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeThirdXYSourceData NativeRetainedSliceCore NativeReferenceSliceBudgetAlgebra
open NativeReferenceSliceBudgetReadback NativeActivePhasePopulation NativeAllTwoScaleConfiguration
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints NativeSquaredGrainQueries
open NativeSharpXPowerAlgebra NativeParentHeightGraphCore

/-- The actual history mass inequality gives the scalar b used by the
raw budget on that same E2, without replacing its original point weights. -/
theorem fraction_lower {n : ℕ} (E2 : Finset (Fin n × Index)) (hE2 : E2.Nonempty)
    (r rankLoss W : ℝ) (H : r^(5*rankLoss)*(E2.card:ℝ) ≤ W) :
    r^(5*rankLoss) ≤ W/(E2.card:ℝ) := by
  have hcard : (0:ℝ)<E2.card := by exact_mod_cast card_pos.mpr hE2
  exact (le_div_iff₀ hcard).mpr H

/-- The selected-parent population and the scalar budget population are
literally equal by population_mass_ratio. Every set, raw label, final radix,
field, and full third relation count stays identical in this readback. -/
theorem source_record {n d J : ℕ} (D : FiniteScaleSource n)
    (eta zeta a : ℝ) (m : ℕ) (plane : Index → Submodule ℝ E4)
    (E2 Hgraph U T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (f : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (p : Parent)
    (lambda W tau seed c2 q Cpre threshold : ℝ) (F1 G Q2 K L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    let b := W/(E2.card:ℝ)
    let pop := (lambda*W/(2*(F1:ℝ)*(G:ℝ)*(E2.card:ℝ)))*D.thickness^eta
    let popBudget := population D.thickness eta lambda b F1 G
    let col := columnEpsilon D.thickness lambda (seed/8) c2
    let window := min (boundaryWindow tau) ((tau/16)/1000)
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix U.card L3
    let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
      lambda b F1 G Q2 F3 Q3 q 2
    HasThirdXYSourceData (J:=J) D zeta a m plane E2 Hgraph U T P hP
      (by norm_num) (by norm_num) hd f p pop
      (profileLower D.thickness pop col tau (seed/8) window) (profileUpper D.thickness col tau)
      Q2 (pop/rowConstant) (selectionCost K) Cpre threshold L3 Rel CX →
    HasThirdXYSourceData (J:=J) D zeta a m plane E2 Hgraph U T P hP
      (by norm_num) (by norm_num) hd f p popBudget
      (profileLower D.thickness popBudget col tau (seed/8) window) (profileUpper D.thickness col tau)
      Q2 (popBudget/rowConstant) (selectionCost K) Cpre threshold L3 Rel CX := by
  intro b pop popBudget col window F3 Q3 CX H
  have hpop : popBudget=pop := population_mass_ratio D.thickness eta lambda W E2.card F1 G
  simpa only [hpop] using H

end NativeActualThirdHistoryReadback
