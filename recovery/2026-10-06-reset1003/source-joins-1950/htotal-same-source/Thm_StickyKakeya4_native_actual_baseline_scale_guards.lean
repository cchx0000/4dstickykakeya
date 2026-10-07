/- UNVERIFIED source draft. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_retention_output_power

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeActualBaselineScaleGuards
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMiddleGrainParentBudget NativeSquaredGrainQueries NativeGenericReferenceData
open NativeLocalParentSource NativeReferenceXYGridPoints NativeSameReferenceChartBounds
open NativeRetentionOutputPower NativeQuarterScaleParameters

/-- The actual stopping-depth cap and the actual base chooser give the
strong guard required by baseline sparse admission. The square guard alone
is not used to infer this inequality. -/
theorem depth_guard (stop level u : ℕ) (hstop : 6 ≤ stop) (hcap : stop ≤ level/4)
    (hu : u+6 ≤ middleDepth stop) : middleDepth stop+(u+12) ≤ level := by
  dsimp only [middleDepth] at hu ⊢
  omega

theorem reference_depth_guard {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0 < tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (j : Fin (g+1))
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu
      (NativeActualMesoscopicRankConfiguration.rankWindow tau)
      (NativeActualMesoscopicRankConfiguration.rankWindow_pos htau).le g ref.level)
    (hstop : 6 ≤ (ref.schedule j).val) (u : ℕ)
    (hu : u+6 ≤ middleDepth (ref.schedule j).val) :
    middleDepth (ref.schedule j).val+(u+12) ≤ ref.level :=
  depth_guard _ _ _ hstop (stopping_depth_cap htau g ref.level ref.schedule ref.schedule_eq j hj) hu

/-- In literal source units the stronger depth guard gives eps>=64r.
Here r is the E1-parent source thickness, not the rank stopping radius. -/
theorem source_mesh_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (level m u : ℕ) (p : Parent)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hdepth : m+(u+12) ≤ level) :
    64*(source h R Eref a m p).thickness ≤ 64/((2^(u+12):ℕ):ℝ) := by
  have hh := source_scale_guard (a:=a) h R Eref level m (u+12) p hdy hdepth
  apply (le_div_iff₀ (show (0:ℝ)<((2^(u+12):ℕ):ℝ) by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤64)
  nlinarith only [hm]

lemma source_thickness_ge_original {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent) (hRho : rho m ≤ 1) :
    D.thickness ≤ (source h R Eref a m p).thickness := by
  have hr : 0 ≤ (source h R Eref a m p).thickness := by
    rw [source_thickness]
    have hd := h.1.2.1
    positivity
  have hid : (source h R Eref a m p).thickness*rho m=D.thickness := by
    rw [source_thickness]
    unfold rho
    field_simp
    ring
  have hh := mul_le_mul_of_nonneg_left hRho hr
  simpa only [hid,mul_one] using hh

/-- The actual configured base envelope also supplies its UPPER power
window, after one cutoff chosen from amin before the original source.
Together with depth_guard this proves both distinct baseline scale guards. -/
theorem exists_source_mesh_window (amin : ℝ) (hamin : 0 < amin) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
        (rStop power epsilonGeom eps : ℝ),
      D.thickness ≤ delta0 → amin ≤ power → rStop ≤ D.thickness^power →
      (rho m)^2 ≤ 6144*rStop → rho m ≤ 1 → 0 < eps →
      0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      64*eps ≤ 2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m) →
      eps ≤ (source h R Eref a m p).thickness^(amin/8) := by
  obtain ⟨delta0,hd0,hd01,Hcut⟩ := exists_small_power_cutoff
    (show 0 < amin/2 by positivity) (by norm_num : (0:ℝ)<1/6144)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro n D eta a h R Eref m p rStop power epsilonGeom eps
    hsmall hpower hstop hRhoStop hRho1 heps heGeom heGeom4 hbase
  have hd := h.1.2.1
  have hd1 := hsmall.trans hd01
  have hRho := rho_pos m
  have hshape := configured_square_le_reference hRho hRho1 heps.le heGeom heGeom4 hbase
  have hfour := output_fourth_le_stop hRho.le hshape hRhoStop
  have hstop' : rStop ≤ D.thickness^amin :=
    hstop.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hpower)
  have hpay := Hcut D.thickness hd hsmall
  have hpositive := Real.rpow_nonneg hd.le (amin/2)
  have hsplit : D.thickness^amin=D.thickness^(amin/2)*D.thickness^(amin/2) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hfour' : eps^4 ≤ D.thickness^(amin/2) := by
    rw [hsplit] at hstop'
    have hpaidMultiply := mul_le_mul_of_nonneg_left hpay hpositive
    nlinarith only [hfour,hstop',hpaidMultiply]
  have hpow : (D.thickness^(amin/8))^(4:ℕ)=D.thickness^(amin/2) := by
    rw [←Real.rpow_mul_natCast hd.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hepsDelta : eps ≤ D.thickness^(amin/8) :=
    (pow_le_pow_iff_left₀ heps.le (Real.rpow_nonneg hd.le _) (by norm_num : (4:ℕ)≠0)).mp
      (hfour'.trans_eq hpow.symm)
  exact hepsDelta.trans (Real.rpow_le_rpow hd.le
    (source_thickness_ge_original (a:=a) h R Eref m p hRho1) (by positivity))

end NativeActualBaselineScaleGuards
