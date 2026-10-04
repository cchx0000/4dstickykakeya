import Theorems.Thm_StickyKakeya4_native_compact_dyadic_source
import Theorems.Thm_StickyKakeya4_native_pruned_power_constants
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeCompactPrunedParameters
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCompactAncestorBudget NativeOriginalPrunedMass NativeCompactDyadicSource
open NativePrunedPowerConstants
open scoped ENNReal

/-- Source-quantified pruning with the requested power in genuine original
ancestor populations, original retained shading density, and original retained
CW counts. The finite source is chosen only after the compact-source cutoff. -/
theorem compact_pruned_parameter_source (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0<zeta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      D.thickness≤delta0 → eta≤zeta/16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀ i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ n≤2*R.card ∧
        wzTotalShadingVolume D≤2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R≤ shadingMass D R ∧
        (∀ U : Set E4,Convex ℝ U →
          ((R.filter (fun i=>markedUnitTube (D.line i) D.thickness⊆U)).card:ℝ≥0∞)≤
            (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
        ∀ (ell : Fin (level+1)) (p : Parent),
          (R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).Nonempty →
            target D.thickness zeta (2^ell.val)≤
              ((R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).card:ℝ) := by
  obtain ⟨db,hdb,hbase⟩ := compact_original_dyadic_source K hK hzeta
  obtain ⟨dc,hdc,hdc1,hco⟩ := exists_positive_rpow_absorption_threshold
    (show 0<zeta/2 by positivity) (show (0:ℝ)≤2 by norm_num) (show (0:ℝ)<1 by norm_num)
  refine ⟨min db dc,lt_min hdb hdc,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,_hCW,hlower⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) heta
  have hd := h.1.2.1
  have hsmallc := hsmall.trans (min_le_right db dc)
  have hcoef : 2*D.thickness^(zeta-eta)≤1 := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hd (hsmallc.trans hdc1)
      (show zeta/2≤zeta-eta by linarith)
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans (hco D.thickness hd hsmallc)
  exact ⟨a,level,R,hdy,ha,hR,hhalf,hshade,retained_density_power D R hd hcoef hden,
    fun U hU=>retained_CW_power h R hhalf hcoef U hU,hlower⟩

end NativeCompactPrunedParameters
