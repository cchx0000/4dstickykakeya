import Theorems.Thm_StickyKakeya4_native_full_coarse_power_consumer
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeNearExtremalCoarseFamily
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseShadingCapacity NativeFullCoarseShadow NativeOriginalPrunedMass
open NativeFixedCompactKakeyaExponent
open scoped BigOperators ENNReal

/-- An ACTUAL fixed-K0 near-extremizer supplies the original fine lower
multiplicity and every full coarse upper multiplicity on ONE retained original
family R. All shadings and representatives are the constructed original ones.
This proves the global part of the Section18 comparison; it does not assert
local-parent upper bounds or the local/global product. -/
theorem exists_near_extremal_coarse_family (hk : 0 < extremalExponent)
    {epsilon window : ℝ} (heps : 0 < epsilon) (hw : 0 < window) :
    ∃e : ℝ,0 < e ∧ ∀theta0 delta0 : ℝ,0 < theta0 → 0 < delta0 →
      ∃ (theta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D theta),
        0 < theta ∧ theta < theta0 ∧ D.thickness < delta0 ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-theta) ∧
        ∃ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
          (∀i,D.shading i=wzCellShading (mesh D) original i) ∧ D.thickness=(2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
          D.thickness^(-extremalExponent+theta+window*e/32) ≤
            NativeIncidenceMultiplicityTower.multiplicity (retained original R) ∧
          ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
            D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
              NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m (retained original R)) ≤
                (ENNReal.ofReal (1/((2^m:ℕ):ℝ))).rpow (-extremalExponent-epsilon) := by
  obtain ⟨e,eta0,dc,he,heta0,hdc,hcoarse⟩ :=
    NativeFullCoarsePowerConsumer.original_full_coarse_power_bounds heps hw
  refine ⟨e,he,?_⟩
  intro theta0 delta0 ht0 hd0
  obtain ⟨theta,ht,htSmall,n,D,hd,hsmall,h,hK,hvol,hnear,hupper⟩ :=
    NativeFixedCompactMultiplicity.exists_matched_normalized_source hk
      (lt_min ht0 heta0) (lt_min hd0 hdc) heps
  obtain ⟨original,a,level,R,horiginal,hdy,ha,hR,hRshade,hretain,hfamily⟩ :=
    hcoarse n D theta h hK (hsmall.le.trans (min_le_right _ _))
      (htSmall.le.trans (min_le_right _ _))
  have hfinite : NativeFiniteKakeyaCounts.multiplicity D≠⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top) hupper
  have hnreal : D.thickness^(-extremalExponent+theta) ≤
      (NativeFiniteKakeyaCounts.multiplicity D).toReal := by
    have hh := ENNReal.toReal_mono hfinite hnear
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] using hh
  have hretained : D.thickness^(-extremalExponent+theta+window*e/32) ≤
      NativeIncidenceMultiplicityTower.multiplicity (retained original R) := by
    calc
      _ = D.thickness^(window*e/32)*D.thickness^(-extremalExponent+theta) := by
        rw [←Real.rpow_add hd]
        congr 1
        ring
      _ ≤ D.thickness^(window*e/32)*(NativeFiniteKakeyaCounts.multiplicity D).toReal :=
        mul_le_mul_of_nonneg_left hnreal (Real.rpow_pos_of_pos hd _).le
      _ ≤ _ := hretain
  exact ⟨theta,n,D,h,ht,htSmall.trans_le (min_le_left _ _),hsmall.trans_le (min_le_left _ _),
    hK,hvol,original,a,level,R,horiginal,hdy,ha,hR,hRshade,hretained,hfamily⟩
end NativeNearExtremalCoarseFamily
