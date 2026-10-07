/- UNVERIFIED source draft. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_actual_baseline_scale_guards
import Theorems.Thm_StickyKakeya4_native_actual_configured_base
import Theorems.Thm_StickyKakeya4_native_common_Y_total_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeSourceBaselineBase
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeReferenceXYGridPoints NativeMiddleGrainParentBudget
open NativeActualBaselineScaleGuards NativeActualConfiguredBase NativeCommonYTotalBudget

/-- All baseline scale obligations are imposed through ONE original-source
cutoff, before D. finalBound can be the intersection of the actual g-dependent
retention/planar cutoffs. The base u/R0 is then constructed once from the
actual middle parent and works for its unchanged source at every Eref,p. -/
theorem exists_source_baseline_base (amin finalBound rBound : ℝ)
    (ha : 0 < amin) (hFinal : 0 < finalBound) (hBound : 0 < rBound) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (p : Parent)
        (level stop : ℕ) (rStop power epsilonGeom : ℝ),
      D.thickness ≤ delta0 → D.thickness=(2:ℝ)⁻¹^level →
      6 ≤ stop → stop ≤ level/4 →
      amin ≤ power → rStop ≤ D.thickness^power →
      (rho (middleDepth stop))^2 ≤ 6144*rStop →
      D.thickness ≤ (rho (middleDepth stop))^2 →
      0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      let m := middleDepth stop
      ∃u : ℕ,6 ≤ u ∧ u+6 ≤ m ∧
      let R0 : ℕ := 2^(m-u)
      let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
      0 < R0 ∧ mu m*(R0:ℝ)=(2:ℝ)⁻¹^u ∧
      rho m ≤ mu m*(R0:ℝ) ∧
      (5/4:ℝ)*(rho m)^(1-2*epsilonGeom) ≤ mu m*(R0:ℝ) ∧
      mu m*(R0:ℝ) ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) ∧
      mu m*(R0:ℝ) ≤ 1 ∧
      ((8*R0:ℕ):ℝ) ≤ 1280*(mu m)^(-2*epsilonGeom) ∧
      mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ) ∧
      0 < eps ∧ eps < finalBound ∧ m+(u+12) ≤ level ∧
      64*(source h R Eref a m p).thickness ≤ eps ∧
      eps ≤ (source h R Eref a m p).thickness^(amin/8) ∧
      (source h R Eref a m p).thickness ≤ rBound := by
  obtain ⟨deltaBase,hdBase,hdBase1,Hbase⟩ := exists_source_base amin finalBound ha hFinal
  obtain ⟨deltaWindow,hdWindow,_hdWindow1,Hwindow⟩ := exists_source_mesh_window amin ha
  let delta0 := min deltaBase (min deltaWindow (rBound^2))
  have hd0 : 0 < delta0 := lt_min hdBase (lt_min hdWindow (sq_pos_of_pos hBound))
  refine ⟨delta0,hd0,(min_le_left _ _).trans hdBase1,?_⟩
  intro n D eta a h R Eref p level stop rStop power epsilonGeom
    hsmall hdy hstop hstopCap hpower hStop hRhoStop hscale heGeom heGeom4 m
  have hBaseSmall : D.thickness ≤ deltaBase := hsmall.trans (min_le_left _ _)
  have hWindowSmall : D.thickness ≤ deltaWindow :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hBoundSmall : D.thickness ≤ rBound^2 :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨u,hu6,huM,hR0,hbaseEq,hRho,hError,hHigh,hBase1,hHeight,hFinalSmall⟩ :=
    Hbase D.thickness rStop power h.1.2.1 hBaseSmall hpower hStop m hRhoStop
      epsilonGeom heGeom heGeom4
  let R0 : ℕ := 2^(m-u)
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hmesh : (mu m*(R0:ℝ))/64=eps := by
    rw [hbaseEq,fine_mesh_eq]
    rw [pow_add]
    norm_num <;> ring
  have hmatch : mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ) := by
    have hh := congrArg (fun x : ℝ => 64*x) hmesh
    dsimp [eps] at hh
    linarith only [hh]
  have hdepth := depth_guard stop level u hstop hstopCap huM
  have hLower := source_mesh_lower (a:=a) h R Eref level m u p hdy hdepth
  have hRho1 : rho m ≤ 1 := hRho.trans hBase1
  have hshapeBound : 64*eps ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) := by
    have he : 64*eps=mu m*(R0:ℝ) := by rw [←hmesh]; ring
    rwa [he]
  have hUpper := Hwindow n D eta a h R Eref m p rStop power epsilonGeom eps
    hWindowSmall hpower hStop hRhoStop hRho1 heps heGeom heGeom4 hshapeBound
  have hSq := source_thickness_sq_le_original (a:=a) h R Eref m p hscale
  have hSource0 : 0 ≤ (source h R Eref a m p).thickness := by
    rw [source_thickness]
    have hh := h.1.2.1
    positivity
  have hSourceBound : (source h R Eref a m p).thickness ≤ rBound := by
    nlinarith only [hSq,hBoundSmall,hSource0,hBound]
  refine ⟨u,hu6,huM,hR0,hbaseEq,hRho,hError,hHigh,hBase1,hHeight,hmatch,heps,?_,
    hdepth,hLower,hUpper,hSourceBound⟩
  rwa [hmesh] at hFinalSmall

end NativeSourceBaselineBase
