import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeCompactOccupiedAncestors
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalPrunedMass NativeCompactAncestorRegularity NativeDyadicParentCells
open scoped ENNReal

/-- Convert the same original retained family to the actual SET of occupied
fine dyadic parameter cells. Exact nesting and the derived finest-cell
occupancy bound supply true covering counts at every dyadic ancestor.
The additional exponent slack is visible as source eta<=zeta/32. -/
theorem compact_original_occupied_ancestors (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i, D.line i ∈ K) →
      D.thickness ≤ delta0 → eta ≤ zeta/32 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness = (2:ℝ)⁻¹^level ∧
        (∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ (fineParents D R a level).Nonempty ∧ n ≤ 2*R.card ∧
        wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R ∧
        (∀ U : Set E4, Convex ℝ U →
          ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
            (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
        ∀ (ell : Fin (level+1)) (p : Parent),
          (descendants D R a level ell.val p).Nonempty →
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((descendants D R a level ell.val p).card:ℝ) ∧
            ((descendants D R a level ell.val p).card:ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 := by
  obtain ⟨db,hdb,hbase⟩ := compact_original_ancestor_regularization K hK (half_pos hzeta)
  obtain ⟨dc,hdc,_hdc1,hco⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hzeta) (show (0:ℝ) ≤ 5832 by norm_num) (show (0:ℝ) < 1 by norm_num)
  refine ⟨min db dc,lt_min hdb hdc,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,hCW,hAD⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) (by linarith)
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have he1 : ENNReal.ofReal D.thickness ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hd1
  have hden' : (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R :=
    (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge he1 (by linarith : zeta/2 ≤ zeta)) le_rfl).trans hden
  have hCW' (U : Set E4) (hU : Convex ℝ U) :
      ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
        (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card :=
    (hCW U hU).trans (mul_le_mul' (mul_le_mul'
      (ENNReal.rpow_le_rpow_of_exponent_ge he1 (by linarith : -zeta ≤ -(zeta/2))) le_rfl) le_rfl)
  refine ⟨a,level,R,hdy,ha,hR,hR.image _,hhalf,hshade,hden',hCW',?_⟩
  intro ell p hne
  have hle : ell.val ≤ level := by omega
  obtain ⟨hcUpper,hcLower⟩ := descendants_card_comparison h R a hle hdy p
  have hparent : (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty :=
    card_pos.mp ((card_pos.mpr hne).trans_le hcUpper)
  obtain ⟨hlo,hup⟩ := hAD ell p hparent
  have hcUpperR : ((descendants D R a level ell.val p).card:ℝ) ≤
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card := by exact_mod_cast hcUpper
  have hcLowerR : ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
      5832*(descendants D R a level ell.val p).card := by exact_mod_cast hcLower
  constructor
  · calc
      _ = D.thickness^(zeta/2)*(D.thickness^(zeta/2)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) := by
        rw [←mul_assoc,←Real.rpow_add hd]
        congr 2
        ring
      _ ≤ D.thickness^(zeta/2)*(5832*(descendants D R a level ell.val p).card) :=
        mul_le_mul_of_nonneg_left (hlo.trans hcLowerR) (Real.rpow_pos_of_pos hd _).le
      _ = (5832*D.thickness^(zeta/2))*(descendants D R a level ell.val p).card := by ring
      _ ≤ 1*(descendants D R a level ell.val p).card := mul_le_mul_of_nonneg_right
        (hco D.thickness hd (hsmall.trans (min_le_right _ _))) (by positivity)
      _ = _ := one_mul _
  · exact (hcUpperR.trans hup).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -zeta ≤ -(zeta/2))) (by positivity))

end NativeCompactOccupiedAncestors
