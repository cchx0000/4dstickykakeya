import Theorems.Thm_StickyKakeya4_native_phase_window_menu_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativePhaseWindowCoarseMenu
open Classical NativePhaseWindowScaleBudget NativePhaseWindowMenuBudget
open NativeMiddleGrainParentBudget

/-- A coarse final physical cell has width at most rho, so its tangent and
height diameters fit the original window. Its old coherence width is sixty-
four times larger, and the actual analytic base inequality supplies the guard. -/
theorem coarse_depth_of_base (u : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1/64) (hbase : (2:ℝ)⁻¹^u/8 ≤ rho^2) :
    ∃d : ℕ, 6 ≤ d ∧ d ≤ u+6 ∧ rho/2 ≤ 1/((2^d:ℕ):ℝ) ∧
      1/((2^d:ℕ):ℝ) ≤ rho ∧ (2:ℝ)⁻¹^u ≤ 64/((2^d:ℕ):ℝ) := by
  have hrho1 : rho ≤ 1 := hrhoSmall.trans (by norm_num)
  have hsquare : rho^2 ≤ rho := by nlinarith only [hrho.le,hrho1]
  obtain ⟨d,hd6,hdu,hlo,hhi,hguard⟩ := exists_prepared_depth u
    (show 0 < rho/2 by positivity) (show rho/2 ≤ 1/128 by linarith only [hrhoSmall])
    (show (2:ℝ)⁻¹^u/64 ≤ rho/2 by nlinarith only [hbase,hsquare,hrho.le])
  exact ⟨d,hd6,hdu,hlo,by nlinarith only [hhi],hguard⟩

/-- A fixed finite exponent menu obtains both actual scales before any
coherence selection: the fine query for local phase population and the
coarse query for a whole-window offset bound. One pre-source cutoff serves
both menus, without a second source or a new scale certificate. -/
theorem exists_source_bilevel_menu_cutoff (K : ℕ) (amin rhoBound : ℝ) (b : Fin K → ℝ)
    (ha : 0 < amin) (hBound : 0 < rhoBound)
    (hb : ∀j, 0 < b j) (hb8 : ∀j, b j ≤ 1/8) :
    ∃delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta r power : ℝ, 0 < delta → delta ≤ delta0 → 0 < r →
      amin ≤ power → r ≤ delta^power →
      ∀epsilon : ℝ, 0 ≤ epsilon → (∀j, epsilon ≤ b j/2) →
      ∀stop u : ℕ, 6 ≤ stop → 48*((2^stop:ℕ):ℝ)*r=1 →
      (2:ℝ)⁻¹^u ≤ 2*max ((5/4:ℝ)*
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon))
        ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ)) →
      ∃fine coarse : Fin K → ℕ, ∀j,
        PreparedWindow r (b j) epsilon rhoBound u (fine j) ∧
        6 ≤ coarse j ∧ coarse j ≤ u+6 ∧
        phaseRho r (b j)/2 ≤ 1/((2^(coarse j):ℕ):ℝ) ∧
        1/((2^(coarse j):ℕ):ℝ) ≤ phaseRho r (b j) ∧
        (2:ℝ)⁻¹^u ≤ 64/((2^(coarse j):ℕ):ℝ) := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_source_menu_cutoff K amin (min rhoBound (1/64)) b
    ha (lt_min hBound (by norm_num)) hb hb8
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta r power hd hsmall hr hpower hrdelta epsilon he0 he stop u hs hid hbase
  obtain ⟨fine,hFine⟩ := H delta r power hd hsmall hr hpower hrdelta
    epsilon he0 he stop u hs hid hbase
  have hCoarse : ∀j, ∃d : ℕ, 6 ≤ d ∧ d ≤ u+6 ∧
      phaseRho r (b j)/2 ≤ 1/((2^d:ℕ):ℝ) ∧
      1/((2^d:ℕ):ℝ) ≤ phaseRho r (b j) ∧ (2:ℝ)⁻¹^u ≤ 64/((2^d:ℕ):ℝ) := by
    intro j
    exact coarse_depth_of_base u (hFine j).2.2.1
      ((hFine j).2.2.2.1.trans (min_le_right _ _)) (hFine j).2.2.2.2.1
  choose coarse hCoarse using hCoarse
  refine ⟨fine,coarse,?_⟩
  intro j
  refine ⟨?_,hCoarse j⟩
  obtain ⟨hd6,hdu,hRho,hBound,hRest⟩ := hFine j
  exact ⟨hd6,hdu,hRho,hBound.trans (min_le_left _ _),hRest⟩

end NativePhaseWindowCoarseMenu
