import Theorems.Thm_StickyKakeya4_native_coarse_source_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarseRelativeCW
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseCellSource NativeCoarseSourceProfiles NativeCoarseShadingPruning
open NativeCoarseCWTransfer NativeOriginalPrunedMass
open scoped BigOperators ENNReal

def cwCost : ℝ := 373248*512^4*volumeConstant*64^3
lemma cwCost_pos : 0 < cwCost := by
  have hv := volumeConstant_pos
  dsimp [cwCost]
  positivity

/-- Positive retained ACTUAL coarse shading forces a lower count of the SAME
selected labels. Only their true unit-tube volume upper bound is used. -/
theorem selected_count_scale {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (h6 : 6 ≤ m)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.2∈original e.1)
    (hshade : D.thickness^(5*zeta) ≤ ∑p∈Q,weight D a level m rep E p) :
    ((2^m:ℕ):ℝ)^3 ≤ (volumeConstant*64^3)*D.thickness^(-5*zeta)*(Q.card:ℝ) := by
  have hd:=h.1.2.1
  have hz:=Real.rpow_pos_of_pos hd (5*zeta)
  have hsum : (∑p∈Q,weight D a level m rep E p) ≤
      (Q.card:ℝ)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) := by
    calc
      _ ≤ ∑_p∈Q,volumeConstant*(64/((2^m:ℕ):ℝ))^3 :=
        sum_le_sum (fun p _hp => actual_weight_upper h original horiginal ha level m hdy hm h6 rep E hE p)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_right (hshade.trans hsum) (show (0:ℝ) ≤ ((2^m:ℕ):ℝ)^3 by positivity)
  have he : ((Q.card:ℝ)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3))*((2^m:ℕ):ℝ)^3=
      (volumeConstant*64^3)*(Q.card:ℝ) := by field_simp
  rw [he] at hh
  apply (mul_le_mul_iff_right₀ hz).mp
  have hid : D.thickness^(5*zeta)*((volumeConstant*64^3)*D.thickness^(-5*zeta)*(Q.card:ℝ))=
      (volumeConstant*64^3)*(Q.card:ℝ) := by
    rw [show -5*zeta=-(5*zeta) by ring,Real.rpow_neg hd.le]
    field_simp [hz.ne']
  rw [hid]
  exact hh

/-- Relative CW is normalized by that actual same-set shading-derived count.
No matching multiplicity or coarse AD/CW certificate occurs among the inputs. -/
theorem source_CW_original_power {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m))) (rep : Parent → Fin n)
    (hrep : ∀p∈Q,parentLabel D a (2^m) (rep p)=p)
    (E : Finset (Fin n × Index)) (hE : ∀e∈E,e.2∈original e.1)
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (H : ∀p∈Q,D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
      ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ))
    (hshade : D.thickness^(5*zeta) ≤ ∑p∈Q,weight D a level m rep E p)
    (U : Set E4) (hU : Convex ℝ U) (hfin : volume U≠⊤) :
    (wzContainedTubeCount (source h a level m Q rep E hsep) U:ℝ) ≤
      cwCost*D.thickness^(-eta-6*zeta)*(volume U).toReal*(Q.card:ℝ) := by
  have hd:=h.1.2.1
  rw [source_contained_count]
  have hcw := original_coarse_CW_real h ha R (2^m) (by positivity) hscale Q hQ rep hrep H U hU hfin
  have hcount := selected_count_scale h original horiginal ha level m hdy hm h6 Q rep E hE hshade
  calc
    _ ≤ (373248*512^4:ℝ)*D.thickness^(-eta-zeta)*((2^m:ℕ):ℝ)^3*(volume U).toReal := hcw
    _ ≤ (373248*512^4:ℝ)*D.thickness^(-eta-zeta)*
        ((volumeConstant*64^3)*D.thickness^(-5*zeta)*(Q.card:ℝ))*(volume U).toReal :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (by positivity)) ENNReal.toReal_nonneg
    _ = _ := by
      have he : D.thickness^(-eta-zeta)*D.thickness^(-5*zeta)=D.thickness^(-eta-6*zeta) := by
        rw [←Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (373248*512^4*volumeConstant*64^3)*
          (D.thickness^(-eta-zeta)*D.thickness^(-5*zeta))*(volume U).toReal*(Q.card:ℝ) := by ring
        _ = _ := by rw [he]; rfl

end NativeCoarseRelativeCW
