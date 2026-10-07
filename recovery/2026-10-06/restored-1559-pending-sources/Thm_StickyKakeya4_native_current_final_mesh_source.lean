import Theorems.Thm_StickyKakeya4_native_current_retained_source
import Theorems.Thm_StickyKakeya4_native_current_source_geometry
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeCurrentFinalMeshSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeActualRelativeCoarseAdmission NativeCurrentRetainedSource
open NativeRelativeCoarseReadback NativeReferenceXYGridPoints NativeCurrentSourceGeometry
open NativeOriginalPrunedMass NativeUnitParentNormalization
open scoped ENNReal BigOperators

/-- The current retained original incidences construct a genuine final-mu
native source after explicit scalar payments. The full relative coarse
image is exactly the double image of T; the selected source shades only
rows of that same image, with full-backbone representatives. No local or
coarse native-input or dense-shading certificate is an input. -/
theorem exists_final_mesh_source {e window : ℝ} (he : 0 < e) (hw : 0 < window) :
    ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (original : Fin n → Finset Index)
        (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
        (a : ℝ)
        (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
        (R : Finset (Fin n)) (H T : Finset (Fin n × Index)),
        T⊆incidences original → T.Nonempty →
        ∀ (zeta : ℝ), 0 ≤ zeta → ∀ (level m : ℕ),
        D.thickness=(2:ℝ)⁻¹^level → 2*m≤level →
        ∀p : Parent,(∀z∈T,z.1∈parentLabels D R a (2^m) p) →
        OriginalPopulationLaw D R a zeta level →
        ∀ (population C localEta : ℝ),0 < population → 0 < C →
        population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card →
        (H.card:ℝ) ≤ C*T.card →
        (2048:ℝ)^3*(((2^m:ℕ):ℝ)*D.thickness/64)^localEta ≤ D.thickness^zeta →
        (373248*512^4:ℝ)*(((2^m:ℕ):ℝ)*D.thickness/64)^localEta ≤ D.thickness^(eta+zeta) →
        (1024*175616*volumeConstant)*C*(((2^m:ℕ):ℝ)*D.thickness/64)^localEta ≤ population →
        (((2^m:ℕ):ℝ)*D.thickness/64)≤eps0 → localEta≤window*e/512 →
        (64:ℝ)^3*(((2^m:ℕ):ℝ)*D.thickness/64)^(window*e/32) ≤ D.thickness^zeta →
        mu m/64 ≤ (((2^m:ℕ):ℝ)*D.thickness/64)^window →
        (((2^m:ℕ):ℝ)*D.thickness/64)/(mu m/64) ≤
          (((2^m:ℕ):ℝ)*D.thickness/64)^window →
        ∃hQ : (parentLabels D R a (2^m) p).Nonempty,
        ∃hlocal : IsWangZakharovNativeFiniteInput (source h R T a m p) localEta,
        let S := source h R T a m p
        let Eall := incidences (sourceCells D R T a (2^m) p)
        let rep := NativeCoarseDirectionThinning.representative hlocal univ 0 (2^(m+6))
        ∃(Q : Finset Parent)
          (hsep : ∀u∈Q,∀v∈Q,u≠v → mu m ≤
            dist (direction (S.line (rep u))) (direction (S.line (rep v)))),
          Q⊆NativeRelativeParentProfiles.relativeParents D R a (2^m) p (2^(m+6)) ∧
          Q.Nonempty ∧
          let Cfinal := NativeCoarseCellSource.source hlocal 0 (level-m+6) (m+6) Q rep Eall
            (by simpa only [final_scale] using hsep)
          IsWangZakharovNativeFiniteInput Cfinal e ∧
          (∀i,Cfinal.line i∈fixedCompactClass) ∧ Cfinal.thickness=mu m ∧
          S.thickness^(5*(window*e/32)) ≤ (wzTotalShadingVolume Cfinal).toReal ∧
          (NativeCoarseShadingCapacity.coarse S 0 (2^(m+6))
            (NativeCoarseDyadicShading.block (level-m+6) (m+6)) rep Eall=
              T.image (doublePair h R a m p hQ (2^(m+6)))) ∧
          ∀i,Cfinal.shading i=wzCellShading (mu m/2)
            (fun _ : Fin 1 =>
              (((T.image (doublePair h R a m p hQ (2^(m+6)))).filter
                (fun z => z.1=NativeCoarseCellSource.parentIndex Q i)).image Prod.snd)) 0 := by
  obtain ⟨eps0,heps0,hadmit⟩ := actual_local_relative_coarse_admission he hw
  refine ⟨eps0,heps0,?_⟩
  intro n D eta h original horiginal a ha R H T hT hTne zeta hzeta level m hdy htwom
    p hQT Hpopulation population C localEta hpopulation hC hparent hretain had hcw hden
    hsmall hlocalEta hpopBudget hcoarse hfine
  have hm : m≤level := by omega
  obtain ⟨hlocal,hfixed,_htrace⟩ := native_input_of_retention h hzeta original horiginal ha
    R H T hT hTne level m hdy hm p hQT (fun b q hq => (Hpopulation b q hq).1)
    population C hpopulation hC hparent hretain had hcw hden
  have hQ : (parentLabels D R a (2^m) p).Nonempty := by
    obtain ⟨z,hz⟩ := hTne
    exact ⟨z.1,hQT z hz⟩
  have hscale : 1/((2^(m+6):ℕ):ℝ)=mu m/64 := by rw [←final_scale m]; ring
  obtain ⟨Q,hsep,hQP,hQne,hfinal,hfinalK,hthickness,_htransfer,hshade⟩ :=
    hadmit n D eta h R T a zeta hzeta level hdy Hpopulation m hm p localEta hlocal
      hfixed hsmall hlocalEta hpopBudget (m+6)
      (by simpa only [hscale,source_thickness] using hcoarse)
      (by simpa only [hscale,source_thickness] using hfine)
  refine ⟨hQ,hlocal,Q,?_,?_,hQne,hfinal,hfinalK,?_,hshade,?_,?_⟩
  · simpa only [final_scale] using hsep
  · simpa only [NativeRelativeParentProfiles.source_parents_eq] using hQP
  · exact hthickness.trans (final_scale m)
  · exact relative_incidence_image h R T a m p hQ (2^(m+6))
      (NativeCoarseDyadicShading.block (level-m+6) (m+6)) hQT hlocal
      (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h R T a level m p hdy hm)
        (by omega))
  · intro i
    rw [NativeCoarseCellSource.source_shading,final_mesh]
    congr 2
    funext v
    rw [NativeCoarseShadingCapacity.rows,
      relative_incidence_image h R T a m p hQ (2^(m+6))
        (NativeCoarseDyadicShading.block (level-m+6) (m+6)) hQT hlocal
        (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h R T a level m p hdy hm)
          (by omega))]

end NativeCurrentFinalMeshSource
