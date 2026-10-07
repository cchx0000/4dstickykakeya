import Theorems.Thm_StickyKakeya4_native_output_scale_coarse_admission
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_retention
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_subset
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeActualSparseReferenceAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeActualRelativeCoarseAdmission
open NativeCurrentReferenceIncidenceRetention NativeCurrentReferenceIncidenceSubset
open NativeSameReferenceChartBounds NativeOutputScaleCoarseAdmission
open scoped ENNReal

/-- The literal loss read from the original parent average and the retained
original incidence count, before changing either source or normalization. -/
def retentionFactor (cost population : ℝ) : ℝ :=
  (1024*175616*NativeOriginalPrunedMass.volumeConstant)*cost/population

/-- Source-facing admission for the actual sparse T inside the original
admitted E1 parent. Incidence retention, the local source cells, its common
height, dyadic mesh, and all relative parent populations are derived here.
The scalar retention power and profile payment are explicit obligations;
no native-input assumption is made for the source shaded only by T. -/
theorem exists_actual_sparse_admission (e window : ℝ) (he : 0 < e) (hw : 0 < window) :
    ∃eps0 : ℝ,0 < eps0 ∧ ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta)
      (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
      (a zeta : ℝ),0 ≤ zeta → HasOriginalBackbone D original R a level zeta →
      ∀(Eref H T : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
        (etaRef : ℝ) (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef),
      T ⊆ Eref → Eref ⊆ incidences original →
      (∀z∈T,z.1∈parentLabels D R a (2^m) p) →
      (source h R Eref a m p).thickness ≤ eps0 → etaRef ≤ window*e/256 →
      (64:ℝ)^3*(source h R Eref a m p).thickness^(window*e/16) ≤ D.thickness^zeta →
      ∀population cost : ℝ,0 < population → 0 < cost →
        population*(parentLabels D R a (2^m) p).card ≤ D.thickness*H.card →
        (H.card:ℝ) ≤ cost*T.card →
      ∀b : ℕ,6 ≤ b → m+b ≤ level →
        64/((2^b:ℕ):ℝ) ≤ (source h R Eref a m p).thickness^window →
        retentionFactor cost population ≤ (64/((2^b:ℕ):ℝ))^(-(e/32)) →
      let Sref := source h R Eref a m p
      let IT := incidences (sourceCells D R T a (2^m) p)
      let rep := NativeCoarseDirectionThinning.representative href univ 0 (2^b)
      ∃(Q : Finset Parent)
        (hsep : ∀u∈Q,∀v∈Q,u≠v → 64/((2^b:ℕ):ℝ) ≤
          dist (direction (Sref.line (rep u))) (direction (Sref.line (rep v)))),
        Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
          (parentLabel Sref 0 (2^b)) ∧ Q.Nonempty ∧
        let C := NativeCoarseCellSource.source href 0 (level-m+6) b Q rep IT hsep
        IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
        (ENNReal.ofReal (64/((2^b:ℕ):ℝ))).rpow (7*e/16)*
          NativeFiniteKakeyaCounts.multiplicity
            (NativeFullCoarseShadow.fullSource href univ 0 (level-m+6) b IT) ≤
          NativeFiniteKakeyaCounts.multiplicity C ∧
        (64/((2^b:ℕ):ℝ))^(5*e/16) ≤ (wzTotalShadingVolume C).toReal := by
  obtain ⟨eps0,heps0,_hepsSmall,Hadmit⟩ := exists_same_reference_admission e window he hw
  refine ⟨eps0,heps0,?_⟩
  intro n D eta h original R level a zeta hzeta HB Eref H T m p etaRef href
    hTE hEorig hQ hsmall heta hprofile population cost hpop hcost hparent hretain b hb hmb
    hwindow hpaid Sref IT rep
  have hm : m ≤ level := by omega
  obtain ⟨horiginal,hdy,ha,_hR,_hcard,_hshade,_hden,_hCW,Hpop⟩ := HB
  have hTorig : T ⊆ incidences original := hTE.trans hEorig
  have hret := (retained_incidence_ratio h original horiginal ha R Eref H T m p href
    hTorig hQ population cost hpop hcost hparent hretain).2
  have hF : 0 < retentionFactor cost population := by
    unfold retentionFactor
    have hv := NativeOriginalPrunedMass.volumeConstant_pos
    positivity
  have hRref : (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).Nonempty := by
    apply card_pos.mp
    simpa using href.1.1
  have hE : IT ⊆ NativeOriginalParentDensityCore.retained
      (sourceCells D R Eref a (2^m) p) univ := by
    rw [incidences_retained_univ]
    exact source_incidences_mono D R T Eref hTE a (2^m) p
  have hProfiles := source_population_law h R Eref a zeta (window*e/16) hzeta level hdy
    Hpop m hm p href hprofile
  have hcompact (i : Fin (parentLabels D R a (2^m) p).card) : Sref.line i∈fixedCompactClass := by
    have hi := (mem_parentLabels D R a (2^m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2^m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ hi.2
  have hscale := source_scale_guard h R Eref level m b p hdy hmb
  have hfine : Sref.thickness ≤ 1/((2^b:ℕ):ℝ) := by
    apply (le_div_iff₀ (show (0:ℝ) < ((2^b:ℕ):ℝ) by positivity)).mpr
    simpa only [mul_comm] using hscale
  have heta' : etaRef ≤ (window*e/16)/16 := by linarith only [heta]
  exact Hadmit _ Sref etaRef href hcompact hsmall heta'
    (sourceCells D R Eref a (2^m) p) 0 (level-m+6) univ IT
    (source_common_mesh h R Eref a m p)
    (source_thickness_dyadic h R Eref a level m hdy hm p)
    (source_common_height_zero h R Eref a m p href) hRref hE hProfiles b
    (retentionFactor cost population) hb (by omega) hfine hwindow hF hpaid hret

end NativeActualSparseReferenceAdmission
