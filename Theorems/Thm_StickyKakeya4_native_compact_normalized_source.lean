import Theorems.Thm_StickyKakeya4_native_padded_source_admissibility
import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeCompactNormalizedSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativePaddedCellSource NativePaddedSourceADLower NativePaddedSourceCountBudget NativePaddedSourceMass
open NativePaddedSourceDensity NativePaddedSourceAdmissibility NativePaddedSourcePowerBudget
open NativeDenseRetainedUnitParent NativeOriginalPrunedMass NativeUnitParentNormalization
open scoped ENNReal

/-- Actual compact original sources produce actual bounded marked sources,
with dyadic cube shadings, at the explicitly smaller thickness delta/64.
The original carrier AD, CW and density are the only input profiles. The
whole-parent selection, true ancestor pruning, actual tube transformation,
and cubical-shading reconstruction are all consumed here. -/
theorem compact_original_normalized_source (K : Set MarkedLine) (hK : IsCompact K)
    {e : ℝ} (he : 0 < e) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta),
      (∀i,D.line i∈K) → D.thickness ≤ delta0 → eta ≤ e/64 →
      ∃ (original : Fin n → Finset Index) (a : ℝ) (R : Finset (Fin n)) (p : Parent),
        (∀i,D.shading i=wzCellShading (mesh D) original i) ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        (parentSubset D R a p).Nonempty ∧
        let S := rootSource h original R a p
        IsWangZakharovNativeFiniteInput S e ∧ S.thickness=D.thickness/64 ∧
        (∀i,S.shading i=wzCellShading (D.thickness/128)
          (NativeOriginalPaddedCells.cells D original a p) (originalLabel (parentSubset D R a p) i)) ∧
        (∀i,S.line i∈fixedCompactClass) ∧
        volume (sourceUnion S) ≤ 625*volume (sourceUnion D) ∧
        (n:ℝ) ≤ D.thickness^(-e)*(parentSubset D R a p).card ∧
        wzTotalShadingVolume D ≤ (ENNReal.ofReal D.thickness).rpow (-e)*wzTotalShadingVolume S := by
  let zeta := e/4
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  obtain ⟨db,hdb,hbase⟩ := NativeCompactAncestorRegularity.compact_original_ancestor_regularization K hK hzeta
  obtain ⟨dc,hdc,hdcsmall,hmaster⟩ := exists_master_cutoff he
  refine ⟨min db dc,lt_min hdb hdc,?_⟩
  intro n D eta h hDK hsmall heta
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hdcD : D.thickness ≤ dc := hsmall.trans (min_le_right _ _)
  have hsmallD : D.thickness ≤ 1/8 := hdcD.trans hdcsmall
  have hm := hmaster D.thickness hd hdcD
  obtain ⟨a,level,R,hdy,ha,hR,_hhalf,hshade,hden,_hCW,H⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) (by dsimp [zeta]; linarith)
  obtain ⟨original,horiginal⟩ := input_exists_common_cells h
  obtain ⟨p,_hp,hQ,hret,hQden⟩ := exists_dense_parent_enn (a:=a) h R hR hsmallD hden
  let Q := parentSubset D R a p
  let S := rootSource h original R a p
  have hpQ : ∀i∈Q,parentLabel D a 1 i=p := fun _ hi => (mem_filter.mp hi).2
  have hlow := fun ell q hne => (H ell q hne).1
  have hunit := unit_lower_of_ancestors D R a zeta level hlow
  have hcount := selected_parent_card_retention h R hunit p hQ
  have hparents := unit_parent_count_bound h R hunit
  obtain ⟨hcL,hcU,hcD,hcCW,hcM,hcN,_hcV⟩ := fixed_cost_bounds
  have hbL : (2048:ℝ)^3*D.thickness^(e-zeta) ≤ 1 :=
    cost_of_master hd hd1 hm hcL (by dsimp [zeta]; linarith)
  have hbU : (10077696:ℝ)*D.thickness^e ≤ 1 := cost_of_master hd hd1 hm hcU (by linarith)
  have hbD : (512*175616*64^4:ℝ)*D.thickness^(e-zeta) ≤ 1 :=
    cost_of_master hd hd1 hm hcD (by dsimp [zeta]; linarith)
  have hbCW : (373248*512^4:ℝ)*D.thickness^(e-(eta+zeta)) ≤ 1 :=
    cost_of_master hd hd1 hm hcCW (by dsimp [zeta]; linarith)
  have hbM : (4*373248*175616*64^4:ℝ)*D.thickness^(e-zeta) ≤ 1 :=
    cost_of_master hd hd1 hm hcM (by dsimp [zeta]; linarith)
  have hbN : (373248:ℝ)*D.thickness^(e-zeta) ≤ 1 :=
    cost_of_master hd hd1 hm hcN (by dsimp [zeta]; linarith)
  obtain ⟨hdS,hdS1,hdyS,hvS,hKS,hmS,hcubS,hsubS,hsepS,hslabS,hfixS⟩ :=
    source_geometric_fields h original horiginal ha Q p hpQ
  have hnative : IsWangZakharovNativeFiniteInput S e := by
    refine ⟨⟨card_pos.mpr hQ,hdS,hdS1,hdyS,hvS,?_,hmS,hcubS,hsubS,hsepS,?_,?_,?_⟩,hslabS,hfixS⟩
    · intro i
      exact (source_weights h original Q a p hpQ i).1
    · intro i radius hrad hrad1
      exact source_AD h hzeta.le he.le original R p level hdy hlow hbL hbU i hrad hrad1
    · intro U hU
      exact source_CW h he.le original ha Q p hpQ hcount hbCW U hU
    · exact source_density h he.le hsmallD original horiginal ha Q p hpQ hQden hbD
  refine ⟨original,a,R,p,horiginal,ha,hQ,hnative,rfl,
    fun i => source_shading h original Q a p hpQ i,hKS,
    source_union_volume_le h original horiginal ha Q p hpQ,?_,?_⟩
  · have hp := Real.rpow_pos_of_pos hd e
    have hc : 373248*D.thickness^(-zeta) ≤ D.thickness^(-e) := by
      apply (mul_le_mul_iff_left₀ hp).mp
      have hl : (373248*D.thickness^(-zeta))*D.thickness^e=373248*D.thickness^(e-zeta) := by
        rw [mul_assoc,←Real.rpow_add hd]
        congr 2
        ring
      have hu : D.thickness^(-e)*D.thickness^e=1 := by rw [←Real.rpow_add hd]; simp
      rw [hl,hu]
      exact hbN
    exact hcount.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
  · let d := ENNReal.ofReal D.thickness
    have hpc : ((R.image (parentLabel D a 1)).card:ℝ≥0∞) ≤ 373248*d.rpow (-zeta) := by
      simpa only [d,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 373248),ENNReal.ofReal_ofNat,
        ENNReal.ofReal_natCast,ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow] using
        ENNReal.ofReal_le_ofReal hparents
    have hsm := original_shadingMass_le_source h original horiginal ha Q p hpQ
    have hco := old_exponent_coefficient hd (4*373248*175616*64^4)
      (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hbM)
    calc
      _ ≤ 2*shadingMass D R := hshade
      _ ≤ 2*(2*(R.image (parentLabel D a 1)).card*shadingMass D Q) := mul_le_mul' le_rfl hret
      _ ≤ 2*(2*(373248*d.rpow (-zeta))*((175616:ℝ≥0∞)*64^4*wzTotalShadingVolume S)) :=
        mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hpc) hsm)
      _ = ((4*373248*175616*64^4:ℝ≥0∞)*d.rpow (-zeta))*wzTotalShadingVolume S := by ring
      _ ≤ _ := mul_le_mul' (by simpa only [d,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hco) le_rfl
end NativeCompactNormalizedSource
