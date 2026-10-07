import Theorems.Thm_StickyKakeya4_native_conditional_coarse_bounds
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_joint_local_coarse_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeConditionalRelativeUpper
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeLocalParentSource
open NativeRelativeCoarseReadback NativeJointUniformCoarseRelations NativePairScaleBudget
open NativeActualRelativeCoarseAdmission NativeUnitParentNormalization NativeFixedCompactKakeyaExponent
open NativeJointLocalCoarseUpper NativeNearTargetLoss
open scoped ENNReal BigOperators

/-- Fix the relative admission exponent and both relative extremal cutoffs
before the original near source is chosen. The conditional physical upper
then follows on its unchanged old incidences using only the forward bridge. -/
theorem exists_relative_upper_engine (tau w : ℝ) (htau : 0 < tau) (hw : 0 < w) :
    ∃ eC d0 : ℝ,0 < eC ∧ eC ≤ tau/(128*w) ∧ 0 < d0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),D.thickness ≤ d0 →
        ∀ (original : Fin n → Finset Index),
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀ (a : ℝ),(∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
          ∀ (R : Finset (Fin n)) (E : Finset (Fin n × Index)),E⊆incidences original →
          ∀ (level m f : ℕ),D.thickness=(2:ℝ)⁻¹^level → m ≤ f → f ≤ level →
          ∀ (p : Parent) (hQ : (parentLabels D R a (2^m) p).Nonempty),
            (∀z∈E,z.1∈parentLabels D R a (2^m) p) →
            ∀ (zeta localEta seed : ℝ),0 ≤ zeta → seed ≤ tau/64 →
              OriginalPopulationLaw D R a zeta level →
              ∀ (_hS : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta),
                (∀i,(source h R E a m p).line i∈fixedCompactClass) →
                localEta ≤ (w/2)*eC/512 →
                (64:ℝ)^3*(source h R E a m p).thickness^((w/2)*eC/32)  ≤  D.thickness^zeta →
                D.thickness ≤ (source h R E a m p).thickness →
                ((2^m:ℕ):ℝ)*D.thickness ≤ D.thickness^w →
                ((2^f:ℕ):ℝ)*D.thickness ≤ D.thickness^w →
                ((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ) ≤ D.thickness^w →
                ∀ rad : ℕ,
                  HasUniformFibers E rad (doublePair h R a m p hQ (2^(f-m+6))) →
                  HasUniformFibers E rad (fun z => (doublePair h R a m p hQ (2^(f-m+6)) z).2) →
                  (41472:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-(seed/4)) →
                  (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level f E)).toReal  ≤ 
                    D.thickness^(-tau)*(64/((2^(f-m+6):ℕ):ℝ))^(-extremalExponent) := by
  have hError : 0 < tau/16 := by positivity
  obtain ⟨eUpper,heUpper,dUpper,hdUpper,hupper⟩ := NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper hError
  let eC := min eUpper (tau/(128*w))
  have heC : 0 < eC := lt_min heUpper (by positivity)
  have heCU : eC ≤ eUpper := min_le_left _ _
  have heSmall : eC ≤ tau/(128*w) := min_le_right _ _
  obtain ⟨eps0,heps0,hadmit⟩ := actual_local_relative_coarse_admission heC (half_pos hw)
  obtain ⟨d0,hd0,_hd01,hcut⟩ := exists_positive_rpow_absorption_threshold hw
    (by norm_num : (0:ℝ) ≤ 1) (lt_min heps0 hdUpper)
  refine ⟨eC,d0,heC,heSmall,hd0,?_⟩
  intro n D eta h hsmall original horiginal a ha R E hE level m f hdy hmf hf p hQ hlabels
    zeta localEta seed hzeta hseed H hS hSK hLocalEta hProfile hDeltaLocal hmwindow hfwindow hgap
    rad hpair hpoint hCost
  let S := source h R E a m p
  let ell := f-m+6
  let theta := 64/((2^ell:ℕ):ℝ)
  let aRel := 7*((w/2)*eC/32)
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have heps : 0 < S.thickness := hS.1.2.1
  have heps1 : S.thickness ≤ 1 := hS.1.2.2.1
  have hTheta : 0 < theta := by dsimp [theta]; positivity
  have hPower : D.thickness^w ≤ min eps0 dUpper := by
    simpa only [one_mul] using hcut D.thickness hd hsmall
  have hSmallS : S.thickness ≤ eps0 := by
    have hs : S.thickness ≤ D.thickness^w := by
      change ((2^m:ℕ):ℝ)*D.thickness/64 ≤ D.thickness^w
      have hp := Real.rpow_pos_of_pos hd w
      linarith
    exact hs.trans (hPower.trans (min_le_left _ _))
  have hSmallTheta : theta ≤ dUpper :=
    ((relative_scale_eq hmf).1.trans_le hgap).trans (hPower.trans (min_le_right _ _))
  have hWin := relative_power_window hd hd1 hw hmf hDeltaLocal hfwindow hgap
  obtain ⟨Q,hsep,_hQP,_hQne,hC,hCK,hThick,hTransfer,_hShade⟩ :=
    hadmit n D eta h R E a zeta hzeta level hdy H m (hmf.trans hf) p localEta hS
      hSK hSmallS hLocalEta hProfile ell hWin.1 hWin.2
  let cells := sourceCells D R E a (2^m) p
  let Eall := incidences cells
  let rep := NativeCoarseDirectionThinning.representative hS univ 0 (2^ell)
  let C := NativeCoarseCellSource.source hS 0 (level-m+6) ell Q rep Eall hsep
  let Rel := NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) ell Eall
  have hSmallC : C.thickness ≤ dUpper := by rw [hThick]; exact hSmallTheta
  have hMuC := hupper Q.card C hSmallC (NativeFiniteKakeyaCounts.input_mono hC heCU) hCK
  have hMuC' : NativeFiniteKakeyaCounts.multiplicity C  ≤ 
      (ENNReal.ofReal theta).rpow (-extremalExponent-tau/16) := hMuC
  have hCross : (ENNReal.ofReal S.thickness).rpow aRel*NativeFiniteKakeyaCounts.multiplicity Rel  ≤ 
      (ENNReal.ofReal theta).rpow (-extremalExponent-tau/16) := hTransfer.trans hMuC'
  have hMuRel := remove_small_power heps heps1 (le_refl aRel) hCross
  have hFinite : (ENNReal.ofReal S.thickness).rpow (-aRel)*
      (ENNReal.ofReal theta).rpow (-extremalExponent-tau/16) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hTheta) ENNReal.ofReal_ne_top)
  have hRelReal : (NativeFiniteKakeyaCounts.multiplicity Rel).toReal  ≤ 
      S.thickness^(-aRel)*theta^(-extremalExponent-tau/16) := by
    have hh := ENNReal.toReal_mono hFinite hMuRel
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal heps.le,ENNReal.toReal_ofReal hTheta.le] using hh
  have haRel : 0 ≤ aRel := by dsimp [aRel]; positivity
  have hRelPower : (NativeFiniteKakeyaCounts.multiplicity Rel).toReal  ≤ 
      D.thickness^(-aRel)*theta^(-extremalExponent-tau/16) :=
    hRelReal.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hd hDeltaLocal (neg_nonpos.mpr haRel))
      (Real.rpow_pos_of_pos hTheta _).le)
  have hBridge := NativeConditionalCoarseBounds.physical_to_relative h original horiginal ha
    R E hE level m f hdy hmf hf p hQ hlabels hS rad hpair hpoint
  have hGlobal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level f E)).toReal  ≤ 
        D.thickness^(-(seed/4+aRel))*theta^(-extremalExponent-tau/16) := by
    calc
      _  ≤  (41472:ℝ)*(rad:ℝ)^4*(NativeFiniteKakeyaCounts.multiplicity Rel).toReal := hBridge
      _  ≤  D.thickness^(-(seed/4))*(D.thickness^(-aRel)*theta^(-extremalExponent-tau/16)) :=
        mul_le_mul hCost hRelPower ENNReal.toReal_nonneg (Real.rpow_pos_of_pos hd _).le
      _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring
  have hDeltaTheta : D.thickness ≤ theta := by
    have hp : S.thickness^(w/2) ≤ 1 := Real.rpow_le_one heps.le heps1 (half_pos hw).le
    have hh := (div_le_one (by positivity : (0:ℝ)<1/((2^ell:ℕ):ℝ))).mp (hWin.2.trans hp)
    exact hDeltaLocal.trans (hh.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  apply upper_with_target_loss (gamma:=seed/4+aRel) (loss:=tau/16)
    hd hd1 hTheta hDeltaTheta hError.le _ hGlobal
  have heScale := (le_div_iff₀ (by positivity : (0:ℝ)<128*w)).mp heSmall
  dsimp [aRel]
  nlinarith

end NativeConditionalRelativeUpper
