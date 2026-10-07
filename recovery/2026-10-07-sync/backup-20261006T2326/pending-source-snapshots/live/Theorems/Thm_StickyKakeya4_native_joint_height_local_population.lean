import Theorems.Thm_StickyKakeya4_native_joint_height_spatial_population
import Theorems.Thm_StickyKakeya4_native_joint_local_xy_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeJointHeightLocalPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeSquaredGrainQueries NativeHorizontalGrainSlice NativeThirdXYData NativeJointLocalXYGeometry
open NativeTranslatedGrainHeightOverlap NativeGrainQuotientFibers NativeRetainedSliceCore
open NativeFixedCompactKakeyaExponent NativeNormalizedCellRelativeMenu NativeJointHeightSpatialPopulation
open NativeJointXYSupportCount
open scoped Matrix.Norms.Elementwise

/-- The same third source gives the local base-key reference population at
all valid joint depths. The target scale is DeltaOut=mu*R0/64, and the entire
fine-to-base ratio cancels in the coarse-grid AD population argument. -/
theorem from_third_data {n d J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell u : ℕ) (hu : 6 ≤ u) (hbase : u+6 ≤ m)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (zeta : ℝ) (plane : Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hS : S⊆parentEdges D a (2^m) E p)
    (Hdata : HasThirdXYData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre threshold L3 Rel)
    (Hsingle : ∀x∈T,∀y∈T,
      translatedHeight D a m x.2/((8*2^(m-u):ℕ):ℤ)=
        translatedHeight D a m y.2/((8*2^(m-u):ℕ):ℤ) →
      translatedHeight D a m x.2=translatedHeight D a m y.2) :
    let Q3:=NativeSourceSizeBounds.radix S.card L3
    let F3:=refinementCost (d+2) (J+1) L3
    let KXY:=xyConstant D.thickness zeta population profileLower profileUpper lambda
      (G*Cpre*(F3:ℝ)) Qref Q3 J m
    let Sq:=NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
      (physicalMesh m (phaseDepth m)/8)
    let F:=fixedField D a m ell plane Sq Fraw
    let R0:=2^(m-u)
    let DeltaOut:=(mu m*(R0:ℝ))/64
    ∀depth : ℕ,6 ≤ depth → depth ≤ u+3 → ∀height : ℤ,∀cell : Index,
      (((T.filter (fun z => translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=height ∧
        physicalCell D a (2^m) (2^depth) p z.2=cell)).image
          (fun z => coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ) ≤
      ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2*(288:ℝ)^(3-extremalExponent)*
        (((64/((2^depth:ℕ):ℝ))/512)/DeltaOut)^(3-extremalExponent) := by
  intro Q3 F3 KXY Sq F R0 DeltaOut depth hdepth hdu height cell
  have Hcopy:=Hdata
  rcases Hcopy with ⟨hTS,_hTn,_hCost,_hTH,_hFinal,_HExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,
    _hThreshold,_hRet,hAD,_hRead,hNorm⟩
  have hTI : T⊆incidences original := hTS.trans (hS.trans ((filter_subset _ _).trans hE))
  have hp : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => (mem_filter.mp (hS (hTS hx))).2
  let I := T.filter (fun z => translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=height ∧
    physicalCell D a (2^m) (2^depth) p z.2=cell)
  have hIT : I⊆T := filter_subset _ _
  have hmu := mu_pos m
  have hR0 : 0 < R0 := by dsimp [R0]; positivity
  by_cases hI : I.Nonempty
  · obtain ⟨x,hx⟩ := hI
    have ht : ∀z∈I,translatedHeight D a m z.2=translatedHeight D a m x.2 := by
      intro z hz
      exact Hsingle z (mem_filter.mp hz).1 x (mem_filter.mp hx).1
        ((mem_filter.mp hz).2.1.trans (mem_filter.mp hx).2.1.symm)
    have hcell : ∀z∈I,physicalCell D a (2^m) (2^depth) p z.2=
        physicalCell D a (2^m) (2^depth) p x.2 := by
      intro z hz
      exact (mem_filter.mp hz).2.2.trans (mem_filter.mp hx).2.2.symm
    have hK : 1 ≤ KXY := xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
    have hR := joint_ratio m u depth hbase hdu
    have hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ) := by
      rw [←hR.2]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hR.1) hmu.le
    have hRle : (R0:ℝ) ≤ ((2^(m+6-depth):ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ))
        (show m-u ≤ m+6-depth by omega)
    have hbaseSmall : (R0:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ) := by
      rw [←hR.2]
      exact mul_le_mul_of_nonneg_right hRle hmu.le
    have ht0 : 0 ≤ 3-extremalExponent := sub_nonneg.mpr extremalExponent_le_three
    have hh := source_height_cell_base_keys h original horiginal ha m level ell (by omega) hdy hf p I T
      hIT hTI hp P hP hell hell4 hd F hNorm R0 depth hR0 hdepth hsmall hbaseSmall x hx ht hcell
      hK ht0 (hAD (translatedHeight D a m x.2))
    have hratio : (6*(64/((2^depth:ℕ):ℝ)))/((R0:ℝ)*mu m)=
        48*(((64/((2^depth:ℕ):ℝ))/512)/DeltaOut) := by
      dsimp only [DeltaOut]
      field_simp
      ring
    have hpower : (6:ℝ)^(3-extremalExponent)*
        ((6*(64/((2^depth:ℕ):ℝ)))/((R0:ℝ)*mu m))^(3-extremalExponent)=
        (288:ℝ)^(3-extremalExponent)*
          (((64/((2^depth:ℕ):ℝ))/512)/DeltaOut)^(3-extremalExponent) := by
      rw [hratio,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 48) (by positivity)]
      rw [show (288:ℝ)=6*48 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
      ring
    calc
      _ ≤ ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2*(6:ℝ)^(3-extremalExponent)*
          ((6*(64/((2^depth:ℕ):ℝ)))/((R0:ℝ)*mu m))^(3-extremalExponent) := hh
      _ = _ := by
        simpa only [mul_assoc] using congrArg
          (fun b : ℝ => (((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2)*b) hpower
  · have hIe : I=∅ := not_nonempty_iff_eq_empty.mp hI
    change ((I.image _).card:ℝ) ≤ _
    simp only [hIe,image_empty,card_empty,Nat.cast_zero]
    positivity

/-- The fixed top interval uses the global occupied BASE keys. It keeps
the same constant as the local denominator and the same original Y input. -/
theorem global_base_keys_from_third_data {n d J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level ell u : ℕ) (hu : 6 ≤ u) (hbase : u+6 ≤ m)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (zeta : ℝ) (plane : Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (p : Parent) (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hS : S⊆parentEdges D a (2^m) E p)
    (Hdata : HasThirdXYData (J:=J) D zeta a m plane E Hgraph S T P hP hell hell4 hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre threshold L3 Rel)
    (Hsingle : ∀x∈T,∀y∈T,
      translatedHeight D a m x.2/((8*2^(m-u):ℕ):ℤ)=
        translatedHeight D a m y.2/((8*2^(m-u):ℕ):ℤ) →
      translatedHeight D a m x.2=translatedHeight D a m y.2) :
    let Q3:=NativeSourceSizeBounds.radix S.card L3
    let F3:=refinementCost (d+2) (J+1) L3
    let KXY:=xyConstant D.thickness zeta population profileLower profileUpper lambda
      (G*Cpre*(F3:ℝ)) Qref Q3 J m
    let Sq:=NativeWeightedGrainQuotientGeometry.retained D a m ell plane Hgraph P hP hell hell4 hd
      (physicalMesh m (phaseDepth m)/8)
    let F:=fixedField D a m ell plane Sq Fraw
    let R0:=2^(m-u)
    let DeltaOut:=(mu m*(R0:ℝ))/64
    ∀tau : ℝ,(1/512:ℝ) ≤ tau → ∀height : ℤ,
      (((T.filter (fun z => translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=height)).image
        (fun z => coarseXY ell R0 (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ) ≤
      ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2*(288:ℝ)^(3-extremalExponent)*
        (tau/DeltaOut)^(3-extremalExponent) := by
  intro Q3 F3 KXY Sq F R0 DeltaOut tau htau height
  have Hcopy:=Hdata
  rcases Hcopy with ⟨hTS,_hTn,_hCost,_hTH,_hFinal,_HExtra,_hOld,_hXY,_hClass,_hGrain,_hKey,
    _hThreshold,_hRet,hAD,_hRead,hNorm⟩
  have hTI : T⊆incidences original := hTS.trans (hS.trans ((filter_subset _ _).trans hE))
  have hp : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => (mem_filter.mp (hS (hTS hx))).2
  let I := T.filter (fun z => translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=height)
  have hIT : I⊆T := filter_subset _ _
  have hmu := mu_pos m
  have hR0 : 0 < R0 := by dsimp [R0]; positivity
  have hbasep : 0 < (R0:ℝ)*mu m := by positivity
  have hDp : 0 < DeltaOut := by dsimp [DeltaOut]; positivity
  have htp : 0 < tau := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/512) htau
  by_cases hI : I.Nonempty
  · obtain ⟨x,hx⟩ := hI
    have ht : ∀z∈I,translatedHeight D a m z.2=translatedHeight D a m x.2 := by
      intro z hz
      exact Hsingle z (mem_filter.mp hz).1 x (mem_filter.mp hx).1
        ((mem_filter.mp hz).2.trans (mem_filter.mp hx).2.symm)
    have hK : 0 < KXY := zero_lt_one.trans_le (xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _)
    have hRle : (R0:ℝ) ≤ ((2^m:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (Nat.sub_le m u)
    have hunit : ((2^m:ℕ):ℝ)*mu m=1 := by
      dsimp [mu,rho]
      field_simp
    have hbase1 : (R0:ℝ)*mu m ≤ 1 :=
      (mul_le_mul_of_nonneg_right hRle hmu.le).trans_eq hunit
    have hg := source_height_base_keys_global h original horiginal ha m level ell (by omega) hdy hf p I T
      hIT hTI hp P hP hell hell4 hd F hNorm (translatedHeight D a m x.2) ht R0 hR0 hbase1 hK
      (hAD (translatedHeight D a m x.2))
    have ht0 : 0 ≤ 3-extremalExponent := sub_nonneg.mpr extremalExponent_le_three
    have hmul : 1 ≤ 512*tau := by linarith only [htau]
    have hid : 8*(tau/DeltaOut)=(512*tau)/((R0:ℝ)*mu m) := by
      dsimp only [DeltaOut]
      field_simp
      ring
    have hrat : 1/((R0:ℝ)*mu m) ≤ 8*(tau/DeltaOut) := by
      rw [hid]
      exact div_le_div_of_nonneg_right hmul hbasep.le
    have hpow : ((R0:ℝ)*mu m)^(-(3-extremalExponent)) ≤
        (8:ℝ)^(3-extremalExponent)*(tau/DeltaOut)^(3-extremalExponent) := by
      have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/((R0:ℝ)*mu m)) hrat ht0
      rw [Real.div_rpow (by norm_num) hbasep.le,Real.one_rpow,
        Real.mul_rpow (by norm_num) (by positivity)] at hh
      simpa only [Real.rpow_neg hbasep.le,one_div] using hh
    have hC : ((9^3:ℕ):ℝ)*((13^3:ℕ):ℝ)*KXY^2 ≤
        ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg KXY)
    have h8 := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 8) (by norm_num : (8:ℝ) ≤ 288) ht0
    have hconstant := mul_le_mul hC h8 (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 8) _)
      (by positivity : 0 ≤ ((9^3:ℕ):ℝ)*(((13^3:ℕ):ℝ))^2*KXY^2)
    calc
      _ ≤ ((9^3:ℕ):ℝ)*((13^3:ℕ):ℝ)*KXY^2*((R0:ℝ)*mu m)^(-(3-extremalExponent)) := hg
      _ ≤ ((9^3:ℕ):ℝ)*((13^3:ℕ):ℝ)*KXY^2*
          ((8:ℝ)^(3-extremalExponent)*(tau/DeltaOut)^(3-extremalExponent)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (((9^3:ℕ):ℝ)*((13^3:ℕ):ℝ)*KXY^2*(8:ℝ)^(3-extremalExponent))*
          (tau/DeltaOut)^(3-extremalExponent) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (by positivity) _)
  · have hIe : I=∅ := not_nonempty_iff_eq_empty.mp hI
    change ((I.image _).card:ℝ) ≤ _
    simp only [hIe,image_empty,card_empty,Nat.cast_zero]
    positivity

end NativeJointHeightLocalPopulation
