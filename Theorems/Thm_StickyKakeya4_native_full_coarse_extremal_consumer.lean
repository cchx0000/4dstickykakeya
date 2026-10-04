import Theorems.Thm_StickyKakeya4_native_original_coarse_admission_with_retention
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_native_coarse_fine_multiplicity
import Theorems.Thm_StickyKakeya4_native_fixed_compact_multiplicity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeFullCoarseExtremalConsumer
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseShadingCapacity NativeCoarseCellSource NativeCoarseDirectionThinning
open NativeCoarseFineMultiplicity NativeFullCoarseShadow NativeOriginalPrunedMass NativeCoarsePowerWindow
open scoped BigOperators ENNReal

/-- One ORIGINAL retained family R works at every scale in the explicit power
window. Actual admitted angular cores transfer the fixed-K0 extremal upper
bound back to the FULL coarse shadow; original fine multiplicity is retained
on the same R. This consumes the coarse native construction in the extremal
law, without postulating a matching profile or equating the two kappas. -/
theorem original_full_coarse_multiplicity_bounds {epsilon window : ℝ}
    (heps : 0 < epsilon) (hw : 0 < window) :
    ∃e eta0 delta0 : ℝ,0 < e ∧ 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ) (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∃ (original : Fin n → Finset Index) (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
          (∀i,D.shading i=wzCellShading (mesh D) original i) ∧ D.thickness=(2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧ R.Nonempty ∧
          wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
          D.thickness^(window*e/32)*(NativeFiniteKakeyaCounts.multiplicity D).toReal ≤
            NativeIncidenceMultiplicityTower.multiplicity (retained original R) ∧
          ∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
            D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
            (ENNReal.ofReal D.thickness).rpow (7*(window*e/32))*
              NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m (retained original R)) ≤
                (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow
                  (-NativeFixedCompactKakeyaExponent.extremalExponent-epsilon) := by
  obtain ⟨e,he,dv,hdv,hupper⟩ := NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper heps
  obtain ⟨da,hda,hadmit⟩ := NativeOriginalCoarseAdmissionWithRetention.original_coarse_admission_with_retention he hw
  let zeta := window*e/32
  have hz : 0 < zeta := by dsimp [zeta]; positivity
  obtain ⟨dc,hdc,_hdc1,hcost⟩ := exists_positive_rpow_absorption_threshold hz
    (show 0 ≤ max densityCost 2 by positivity) (by norm_num : (0:ℝ)<1)
  obtain ⟨ds,hds,_hds1,hscale⟩ := exists_positive_rpow_absorption_threshold hw
    (show 0 ≤ 64/dv by positivity) (by norm_num : (0:ℝ)<1)
  refine ⟨e,window*e/512,min da (min dc ds),he,by positivity,lt_min hda (lt_min hdc hds),?_⟩
  intro n D eta h hK hsmall heta
  obtain ⟨original,a,level,R,horiginal,hdy,ha,hR,hRshade,Horiginal,hfamily⟩ :=
    hadmit n D eta h hK (hsmall.trans (min_le_left _ _)) heta
  have hd:=h.1.2.1
  have hrest := hsmall.trans (min_le_right _ _)
  have hc := hcost D.thickness hd (hrest.trans (min_le_left _ _))
  have hden : densityCost*D.thickness^zeta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left densityCost 2) (Real.rpow_pos_of_pos hd _).le).trans hc
  have htwo : (2:ℝ) ≤ D.thickness^(-zeta) := by
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
      ((mul_le_mul_of_nonneg_right (le_max_right densityCost 2) (Real.rpow_pos_of_pos hd _).le).trans hc)
  have hRreal : (wzTotalShadingVolume D).toReal ≤ D.thickness^(-zeta)*
      NativeDenseRetainedUnitParent.realShadingMass D R := by
    have ht : (2:ℝ≥0∞)*shadingMass D R≠⊤ := ENNReal.mul_ne_top (by norm_num) (shadingMass_ne_top h R)
    have hh := ENNReal.toReal_mono ht hRshade
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,←NativeDenseRetainedUnitParent.realShadingMass_eq_toReal h R] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)))
  refine ⟨original,a,level,R,horiginal,hdy,ha,hR,hRshade,
    original_fine_multiplicity_retention h original horiginal R hRreal,?_⟩
  intro m hcoarse hfine
  obtain ⟨Q,hsep,hQP,_hQne,_hQrep,hS,hthick,hSK,_hline,_hcubes,hshade⟩ := hfamily m hcoarse hfine
  let rep := representative h R a (2^m)
  let S := source h a level m Q rep (retained original R) hsep
  have h6 : 6 ≤ m := by
    have hh := hS.1.2.2.1
    rw [hthick] at hh
    have hp : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := (div_le_one (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mp hh
    by_contra hn
    have hm5 : m ≤ 5 := by omega
    have hu : ((2^m:ℕ):ℝ) ≤ 32 := by
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm5).trans_eq (by norm_num)
    linarith
  have hm : m ≤ level := by
    have hd1 := h.1.2.2.1
    have hdPow : D.thickness^window ≤ 1 := Real.rpow_le_one hd.le hd1 hw.le
    have hle : D.thickness ≤ 1/((2^m:ℕ):ℝ) :=
      (div_le_one (by positivity : 0 < 1/((2^m:ℕ):ℝ))).mp (hfine.trans hdPow)
    have hh : (1/2:ℝ)^level ≤ (1/2:ℝ)^m := by
      simpa only [hdy,one_div,inv_pow,Nat.cast_pow,Nat.cast_ofNat] using hle
    exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hh
  have hsmallS : S.thickness ≤ dv := by
    have hh := hscale D.thickness hd (hrest.trans (min_le_right _ _))
    have heq : (64/dv)*D.thickness^window=(64*D.thickness^window)/dv := by ring
    rw [heq] at hh
    rw [hthick]
    calc
      _ = 64*(1/((2^m:ℕ):ℝ)) := by ring
      _ ≤ 64*D.thickness^window := mul_le_mul_of_nonneg_left hcoarse (by norm_num)
      _ ≤ _ := (div_le_one hdv).mp hh
  have hE : ∀x∈retained original R,x.2∈original x.1 :=
    fun x hx => ((retained_spec original R x).mp hx).2
  have hshade' : D.thickness^(5*zeta) ≤ ∑p∈Q,NativeCoarseShadingPruning.weight D a level m rep (retained original R) p := by
    rwa [NativeCoarseSourceMass.source_total_shading_real] at hshade
  have hfull := full_multiplicity_le_core h original horiginal ha R level m hdy hm h6
    (retained original R) hE (fun p hp => (Horiginal ⟨m,by omega⟩ p hp).1) Q hQP hsep hshade' hden
  exact hfull.trans (by simpa only [S,source_thickness] using hupper Q.card S hsmallS hS hSK)

end NativeFullCoarseExtremalConsumer
