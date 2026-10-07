import Theorems.Thm_StickyKakeya4_native_actual_local_admission
import Theorems.Thm_StickyKakeya4_native_third_XY_data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeCurrentRetainedSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeActualLocalAdmission NativeOriginalPrunedMass NativeUnitParentNormalization
open scoped ENNReal BigOperators

/-- The current incidence cut pays its actual cardinal retention in the
already selected parent's original average. No source is selected again. -/
lemma retained_parent_average {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 ≤ D.thickness) (R : Finset (Fin n))
    (H T : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (population C : ℝ)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card)
    (hretain : (H.card:ℝ) ≤ C*T.card) :
    population*(parentLabels D R a (2^m) p).card ≤ D.thickness*C*T.card := by
  exact hparent.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hretain hd)

/-- Density of the literal current-T local source follows from the old
parent average and the explicit total retention cost. The sole new budget
is scalar: K*C*epsilon^e <= population. -/
theorem source_density_of_retention {n : ℕ} {D : FiniteScaleSource n} {eta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (H T : Finset (Fin n × Index)) (hT : T⊆incidences original)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (p : Parent)
    (hQ : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (population C : ℝ) (hpopulation : 0 < population) (hC : 0 < C)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card)
    (hretain : (H.card:ℝ) ≤ C*T.card)
    (hbudget : (1024*175616*volumeConstant)*C*
      (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ population) :
    (ENNReal.ofReal (source h R T a m p).thickness).rpow e*
      wzTotalTubeVolume (source h R T a m p) ≤ wzTotalShadingVolume (source h R T a m p) := by
  have hd := h.1.2.1
  let F := D.thickness^eta*C/population
  have hF : 0 < F := by dsimp [F]; positivity
  have havg := retained_parent_average D hd.le R H T a m p population C hparent hretain
  have hparent' : D.thickness^(eta+2*0)*(parentLabels D R a (2^m) p).card ≤
      D.thickness*F*(1:ℝ)^2*T.card := by
    have hh := mul_le_mul_of_nonneg_left havg
      (show 0 ≤ D.thickness^eta/population by positivity)
    convert hh using 1 <;> field_simp [hpopulation.ne'] <;> ring
  have hbudget' : (1024*175616*volumeConstant)*F*(1:ℝ)^2*
      (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^(eta+2*0) := by
    have hh := mul_le_mul_of_nonneg_left hbudget
      (show 0 ≤ D.thickness^eta/population by positivity)
    convert hh using 1 <;> field_simp [hpopulation.ne'] <;> ring
  exact NativeActualLocalDensity.source_density (zeta:=0) h original horiginal ha R T hT
    level m hdy hm p hQ F 1 hF (by norm_num) hparent' hbudget'

/-- Complete native admission for the current original-incidence T. AD and
CW use the unchanged full R-parent; density is derived above from the
actual prior parent average, not supplied as a certificate. -/
theorem native_input_of_retention {n : ℕ} {D : FiniteScaleSource n} {eta zeta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (H T : Finset (Fin n × Index))
    (hT : T⊆incidences original) (hTne : T.Nonempty)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (p : Parent)
    (hQ : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Hpopulation : ∀b : Fin (level+1),∀q : Parent,
      (R.filter (fun i => parentLabel D a (2^b.val) i=q)).Nonempty →
        D.thickness^zeta*((1/((2^b.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^b.val) i=q)).card:ℝ))
    (population C : ℝ) (hpopulation : 0 < population) (hC : 0 < C)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card)
    (hretain : (H.card:ℝ) ≤ C*T.card)
    (had : (2048:ℝ)^3*(((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^zeta)
    (hcw : (373248*512^4:ℝ)*(((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^(eta+zeta))
    (hden : (1024*175616*volumeConstant)*C*
      (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ population) :
    IsWangZakharovNativeFiniteInput (source h R T a m p) e ∧
      (∀i,(source h R T a m p).line i∈fixedCompactClass) ∧
      HasExactTrace h R T a m p := by
  obtain ⟨z,hz⟩ := hTne
  have hne : (parentLabels D R a (2^m) p).Nonempty := ⟨z.1,hQ z hz⟩
  obtain ⟨hdS,hdS1,hdyS,hvalid,hSK,hweights,_hfibre,hmeas,hcub,hsub,hsep,hslab,hfixed⟩ :=
    source_geometric_fields h original horiginal ha R T hT level m hdy hm p
  refine ⟨⟨⟨card_pos.mpr hne,hdS,hdS1,hdyS,hvalid,hweights,hmeas,hcub,hsub,hsep,?_,?_,?_⟩,
    hslab,hfixed⟩,hSK,source_exact_trace h R T a m p hQ⟩
  · exact source_AD h hzeta R T level m hdy p Hpopulation had
  · exact source_CW h ha R T m p (Hpopulation ⟨m,by omega⟩ p hne) hcw
  · exact source_density_of_retention h original horiginal ha R H T hT level m hdy hm p
      hQ population C hpopulation hC hparent hretain hden

end NativeCurrentRetainedSource
