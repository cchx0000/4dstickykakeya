/- RECONSTRUCTED 2026-10-06 from visible conversation context. UNVERIFIED.
This file was drafted after Oct 5 21:00 and had not been submitted for Lean checking.
It includes the actual current-T cell budget and the sparse-reference admission route. -/
import Theorems.Thm_StickyKakeya4_native_sparse_coarse_selection
import Theorems.Thm_StickyKakeya4_native_current_reference_shading

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeSparseCoarseAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeCoarseShadingCapacity NativeCoarseDyadicShading NativeCoarseShadingPruning
open NativeCoarseDirectionThinning NativeCoarseMassBudget NativeDyadicParentCells
open NativeSparseCoarseSelection NativeUnitParentNormalization NativeCoarsePowerWindow
open NativeCoarseRelativeCW
open scoped BigOperators

/-- Discharge the sparse selection's cell-mass input from the original T
parent average and a scalar payment at the chosen output power. The native
reference source Eref is used only for its actual common mesh here. -/
theorem current_selected_cell_budget {n : ℕ} {D : FiniteScaleSource n}
    {eta a zetaOriginal zetaCoarse : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref H T : Finset (Fin n × Index))
    (hT : T⊆incidences original) (m : ℕ) (p : Parent)
    (hQT : ∀z∈T,z.1∈NativeLocalParentSource.parentLabels D R a (2^m) p)
    (population C : ℝ) (hpopulation : 0 ≤ population) (hC : 0 < C)
    (hparent : population*(NativeLocalParentSource.parentLabels D R a (2^m) p).card ≤ D.thickness*H.card)
    (hretain : (H.card:ℝ) ≤ C*T.card)
    (hpop : D.thickness^zetaOriginal*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
      ((NativeLocalParentSource.parentLabels D R a (2^m) p).card:ℝ))
    (hbudget : (16*175616*64^4:ℝ)*C*((43*colorCost)*
      (NativeLocalParentSource.source h R Eref a m p).thickness^(2*zetaCoarse)) ≤
        population*D.thickness^zetaOriginal) :
    (43*colorCost)*(NativeLocalParentSource.source h R Eref a m p).thickness^(2*zetaCoarse) ≤
      ((incidences (NativeLocalParentSource.sourceCells D R T a (2^m) p)).card:ℝ)*
        ((NativeLocalParentSource.source h R Eref a m p).thickness/2)^4 := by
  rw [NativeCurrentReferenceShading.current_local_mass_readback h R T Eref a m p hQT]
  have hh := hbudget.trans (NativeCurrentReferenceShading.current_local_mass_lower h original
    horiginal ha R H T hT m p hQT population C hpopulation hC.le hparent hretain hpop)
  exact (mul_le_mul_iff_right₀ (show 0 < (16*175616*64^4:ℝ)*C by positivity)).mp hh

/-- Admit a coarse source from a native reference and arbitrary literal
selected incidences. Only the actual selected-cell count and explicit
coarse-scale scalar payments are needed; sparse E is never required to be
a native input at the reference thickness. -/
theorem native_sparse_coarse_source {n : ℕ} {D : FiniteScaleSource n} {eta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (hzeta : 0 ≤ zeta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (hR : R.Nonempty) (E : Finset (Fin n × Index))
    (hE : E⊆retained original R) (level b : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hb : b ≤ level) (h6 : 6 ≤ b)
    (H : ∀j : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (hselected : (43*colorCost)*D.thickness^(2*zeta) ≤ (E.card:ℝ)*(D.thickness/2)^4)
    (hlog : 2*pruneCost*((b:ℝ)+1) ≤ D.thickness^(-zeta))
    (hsmall : 2*D.thickness^zeta ≤ 1)
    (hpower : (64/((2^b:ℕ):ℝ))^e ≤ D.thickness^(8*zeta))
    (hupper : 10077696*D.thickness^(8*zeta) ≤ 1)
    (hdensity : densityCost*D.thickness^zeta ≤ 1)
    (hcw : cwCost*D.thickness^(8*zeta-(eta+6*zeta)) ≤ 1) :
    let rep := representative h R a (2^b)
    ∃(Q : Finset Parent)
      (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
        dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
      Q⊆R.image (parentLabel D a (2^b)) ∧ Q.Nonempty ∧
      let C := NativeCoarseCellSource.source h a level b Q rep E hsep
      IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
      C.thickness=64/((2^b:ℕ):ℝ) ∧
      D.thickness^(5*zeta) ≤ (wzTotalShadingVolume C).toReal := by
  obtain ⟨Q,hQP,hQne,hrep,hsep,hshade,Hpruned⟩ := sparse_coarse_selection h hzeta original
    horiginal ha R hR E hE level b hdy hb h6 H hselected hlog hsmall
  have hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hb]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨Q,hsep,hQP,hQne,?_,?_,rfl,?_⟩
  · exact NativeCoarseNativeAdmissibility.native_input h hK hzeta original horiginal ha R
      level b hdy hb h6 hscale Q hQP hQne (representative h R a (2^b))
      (fun p hp => (hrep p hp).2) E
      (fun z hz => ((retained_spec original R z).mp (hE hz)).2) hsep
      (fun p hp => (H ⟨b,by omega⟩ p hp).1) Hpruned hshade hpower hupper hdensity hcw
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass h hK ha _
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    exact hshade

end NativeSparseCoarseAdmission
