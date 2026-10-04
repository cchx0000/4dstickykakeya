import Theorems.Thm_StickyKakeya4_native_compact_pruned_parameters
import Theorems.Thm_StickyKakeya4_native_original_slope_cube_packing
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeCompactAncestorRegularity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCompactAncestorBudget NativeOriginalPrunedMass NativeCompactPrunedParameters
open NativeOriginalSlopeCubePacking
open scoped ENNReal

lemma dyadic_parent_scale {delta : ℝ} {level : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (ell : Fin (level+1)) :
    ((2^ell.val:ℕ):ℝ)*delta≤1 := by
  have he : delta=((2:ℝ)^level)⁻¹ := by rw [hdy,inv_pow]
  have hle : ell.val≤level := by omega
  have hp : ((2^ell.val:ℕ):ℝ)≤(2:ℝ)^level := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hle
  rw [he,←div_eq_mul_inv]
  exact (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^level)).mpr hp

/-- Actual bounded compact-source metric AD is converted into true dyadic
ancestor AD on ONE retained set of original tube labels. The same labels
retain original shading density and convex-Wolff with the requested exponent.
No ancestor lower population or shading profile is assumed. -/
theorem compact_original_ancestor_regularization (K : Set MarkedLine) (hK : IsCompact K)
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
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3≤
              ((R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i=>parentLabel D a (2^ell.val) i=p)).card:ℝ)≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 := by
  obtain ⟨db,hdb,hbase⟩ := compact_pruned_parameter_source K hK hzeta
  obtain ⟨dc,hdc,_hdc1,hco⟩ := exists_positive_rpow_absorption_threshold
    hzeta (show (0:ℝ)≤5832 by norm_num) (show (0:ℝ)<1 by norm_num)
  refine ⟨min db dc,lt_min hdb hdc,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,hCW,hlower⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) heta
  have hd := h.1.2.1
  have hcoeff : 5832≤D.thickness^(-zeta) := by
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd zeta)).mpr
      (hco D.thickness hd (hsmall.trans (min_le_right _ _)))
  refine ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,hCW,?_⟩
  intro ell p hne
  refine ⟨hlower ell p hne,?_⟩
  have hu := native_retained_parent_card_le h R a (2^ell.val) (by positivity)
    (dyadic_parent_scale hdy ell) p
  have hp := mul_le_mul_of_nonneg_right hcoeff
    (show 0≤((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 by positivity)
  apply le_trans _ hp
  simpa only [div_div] using hu

end NativeCompactAncestorRegularity
