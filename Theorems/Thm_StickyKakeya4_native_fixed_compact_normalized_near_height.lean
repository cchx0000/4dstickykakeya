import Theorems.Thm_StickyKakeya4_native_fixed_compact_normalized_near
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeFixedCompactNormalizedNearHeight
open Classical Finset MeasureTheory StickyKakeya4 NativeUnitParentNormalization NativeCommonCubicalMesh
open NativeFixedCompactKakeyaExponent NativeCompactNormalizedSource NativePaddedSourcePowerBudget
open NativeDenseRetainedUnitParent NativePaddedCellSource NativePaddedSourceADLower NativeFiniteKakeyaCounts
open NativeFixedCompactNormalizedNear
open scoped ENNReal

/-- An actual near-extremizer in the literal fixed compact class is passed
through the constructed whole-parent normalization. The resulting source is
still in that same class; its multiplicity is recovered from actual new counts
and shading volumes, rather than assumed to survive the transformation. -/
theorem exists_normalized_near_extremizer_with_height (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0) :
    ∃theta : ℝ,0 < theta ∧ theta < theta0 ∧
      ∃ (nu : ℝ) (n : ℕ) (D : FiniteScaleSource n) (hD : IsWangZakharovNativeFiniteInput D nu)
        (original : Fin n → Finset Index) (a : ℝ) (R : Finset (Fin n)) (p : NativeOriginalParentSelection.Parent),
        0 < nu ∧ nu < theta/512 ∧ D.thickness < delta0 ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        (∀i,D.shading i=wzCellShading (NativeOriginalParentSelection.mesh D) original i) ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-nu) ∧
        let S := rootSource hD original R a p
        0 < S.thickness ∧ S.thickness < delta0 ∧ IsWangZakharovNativeFiniteInput S theta ∧
        S.thickness=D.thickness/64 ∧ (∀i,S.line i∈fixedCompactClass) ∧
        (∀i,S.shading i=wzCellShading (D.thickness/128)
          (NativeOriginalPaddedCells.cells D original a p) (originalLabel (parentSubset D R a p) i)) ∧
        volume (sourceUnion S) ≤ (ENNReal.ofReal S.thickness).rpow (extremalExponent-theta) ∧
        (ENNReal.ofReal S.thickness).rpow (-extremalExponent+theta) ≤ NativeFiniteKakeyaCounts.multiplicity S := by
  let theta := theta0/2
  have htheta : 0 < theta := by dsimp [theta]; positivity
  have htau : 0 < theta/8 := by positivity
  obtain ⟨dn,hdn,hnormalize⟩ := compact_original_normalized_source fixedCompactClass fixedCompactClass_compact htau
  obtain ⟨dm,hdm,_hdmSmall,hmaster⟩ := exists_master_cutoff (half_pos htheta)
  obtain ⟨dt,hdt,htube⟩ := exists_markedUnitTube_admissible_scale htau
  let cutoff := min delta0 (min dn (min dm dt))
  have hcutoff : 0 < cutoff := lt_min hdelta0 (lt_min hdn (lt_min hdm hdt))
  obtain ⟨nu,hnu,hnuSmall,n,D,hd,hsmall,hD,hDK,hvol,_hmu⟩ :=
    NativeFixedCompactKakeyaExponent.exists_near_extremizer hk
      (show 0 < theta/512 by positivity) hcutoff
  have hdDelta : D.thickness < delta0 := hsmall.trans_le (min_le_left _ _)
  have hdRest : D.thickness ≤ min dn (min dm dt) := hsmall.le.trans (min_le_right _ _)
  have hdNorm : D.thickness ≤ dn := hdRest.trans (min_le_left _ _)
  have hdMore : D.thickness ≤ min dm dt := hdRest.trans (min_le_right _ _)
  obtain ⟨original,a,R,p,horiginal,ha,_hQ,hS,hscale,hcells,hSK,hunion,_hcount,_hshadeRet⟩ :=
    hnormalize n D nu hD hDK hdNorm (by linarith)
  let S := rootSource hD original R a p
  have hdS : 0 < S.thickness := hS.1.2.1
  have hdSle : S.thickness ≤ D.thickness := by rw [hscale]; linarith
  have hdSTube : S.thickness ≤ dt := hdSle.trans (hdMore.trans (min_le_right _ _))
  have hm := hmaster D.thickness hd (hdMore.trans (min_le_left _ _))
  have hco := fixed_cost_bounds.2.2.2.2.2.2
  have hbudget : (625*64^3:ℝ)*D.thickness^(theta/2-nu) ≤ 1 :=
    cost_of_master hd hD.1.2.2.1 hm hco (by linarith)
  have hvolHalf : volume (sourceUnion S) ≤ (ENNReal.ofReal S.thickness).rpow (extremalExponent-theta/2) := by
    rw [hscale]
    exact (hunion.trans (mul_le_mul' le_rfl hvol)).trans
      (near_volume_scale hd htheta.le extremalExponent_le_three hbudget)
  have hshade : (ENNReal.ofReal S.thickness).rpow (3*theta/8) ≤ wzTotalShadingVolume S := by
    have hh := total_shading_lower hS (fun i => htube (S.line i) (hS.1.2.2.2.2.1 i) S.thickness hdS hdSTube)
    convert hh using 1
    congr 1
    ring
  let d := ENNReal.ofReal S.thickness
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdT : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd1 : d ≤ 1 := by simpa only [d,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hS.1.2.2.1
  have hST : volume (sourceUnion S) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_ne_zero hd0 hdT) hvolHalf
  have hM0 : wzTotalShadingVolume S ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hdS) hdT) hshade).ne'
  refine ⟨theta,htheta,by dsimp [theta]; linarith,nu,n,D,hD,original,a,R,p,hnu,hnuSmall,
    hdDelta,hDK,horiginal,ha,hvol,hdS,hdSle.trans_lt hdDelta,input_mono hS (by linarith),hscale,hSK,hcells,?_,?_⟩
  · exact hvolHalf.trans (ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith))
  · unfold NativeFiniteKakeyaCounts.multiplicity
    apply (ENNReal.le_div_iff_mul_le (Or.inr hM0) (Or.inl hST)).mpr
    calc
      _ ≤ d.rpow (-extremalExponent+theta)*d.rpow (extremalExponent-theta/2) := mul_le_mul' le_rfl hvolHalf
      _ = d.rpow (theta/2) := by
        simp only [ENNReal.rpow_eq_pow]
        rw [←ENNReal.rpow_add _ _ hd0 hdT]
        congr 1
        ring
      _ ≤ d.rpow (3*theta/8) := ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ ≤ _ := hshade

end NativeFixedCompactNormalizedNearHeight
