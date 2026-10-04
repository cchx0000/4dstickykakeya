import Theorems.Thm_StickyKakeya4_native_source_coarse_readback
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeDenseSourceCoarseFamily
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeDenseSourceRefinement NativeSourceCoarseReadback
open NativeCoarseOriginalIncidences NativeCoarseOriginalGeometry
open scoped ENNReal
/-- The SAME original E0 produced by the native source selector is carried
 through the actual chart, physical coarsening, and common normalization.
 This is a concrete incidence family with proved geometry and density, not
 an assertion that the missing global-grain configuration fields exist. -/
theorem exists_actual_original_coarse_family {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (NativeOriginalParentSelection.mesh D) cells i)
    (hne : (NativeCubicalIncidenceCounts.incidences cells).Nonempty) (hexp : 0 ≤ eta+beta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta) ≤
      MeasureTheory.volume (markedUnitTube (D.line i) D.thickness))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*(D.thickness/8) ≤ 1)
    {L d : ℕ} (hL : 0 < L) (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ a : ℝ, ∃ p ∈ parents D a N, ∃ E0 : Finset (Fin n × Index),
      E0 ⊆ NativeCubicalIncidenceCounts.incidences cells ∧
      let P := data D cells a N p
      let I := originalFamily P (shift D a) E0
      let deltaNew := (N:ℝ)*D.thickness/224
      P.Hypotheses ∧ I.Nonempty ∧
      TwoTubePathCollisionCount.tubes I=E0.image Prod.fst ∧
      E0.card ≤ N*I.card ∧
      (D.thickness^(eta+beta)/(28*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ)))*
        (TwoTubePathCollisionCount.tubes I).card ≤ deltaNew*(I.card:ℝ) ∧
      ∀ e ∈ I, |height P (normalization P) e.1| ≤ 1 ∧
        (∀ j, |(coordinates P (normalization P) e.1).1 j| ≤ 1) ∧
        (∀ j, |(coordinates P (normalization P) e.1).1 j-P.offset e.2 j/normalization P-
          P.slope e.2 j*height P (normalization P) e.1| ≤ 13*deltaNew) := by
  obtain ⟨a,p,hp,E,B,E0,hE0,hread,_hcard,_htubes,hP,_hlam,hEI,hEn,_hB,_hbins,_hwhole,
    _hret,hden,_hballs,_hphase⟩ := dense_source_slice_population h cells hcells hne hexp htube
      N hN hscale hL radii timeDiv offsetMesh slopeMesh
  let P := data D cells a N p
  have hchart : chartFamily (shift D a) E0=E := by
    rw [←hread]
    ext e
    simp only [chartFamily,mem_image]
  have hsub : chartFamily (shift D a) E0 ⊆ P.incidences := by rwa [hchart]
  have hE0n : E0.Nonempty := by
    obtain ⟨e,he⟩ := hEn
    rw [←hread] at he
    obtain ⟨e0,he0,_⟩ := mem_image.mp he
    exact ⟨e0,he0⟩
  have hI : (originalFamily P (shift D a) E0).Nonempty := by
    simpa only [originalFamily,image_nonempty] using hE0n
  have hF : (0:ℝ)<NativeSelectedPhysicalMultiplicity.refinementLoss d L := by
    exact_mod_cast NativeSelectedPhysicalMultiplicity.refinementLoss_pos d L
  have hm := native_scale_readback D cells a N p
  have hTubeImage : @Finset.image (Fin n × Index) (Fin n) (Classical.decEq _) Prod.fst E0=E0.image Prod.fst := by
    ext i
    simp only [mem_image]
  have hmOld : P.δ=D.thickness/8 := hm.1
  have hdensity := original_density P hP (shift D a) E0 hsub hF (normalization_pos P)
    (lambda := D.thickness^(eta+beta)) (by rw [hTubeImage,hmOld]; exact hden)
  rw [hm.2.2,hm.2.1] at hdensity
  have hcap := original_capacity P hP (shift D a) E0 hsub
  have hTubesNative : TwoTubePathCollisionCount.tubes (originalFamily P (shift D a) E0)=E0.image Prod.fst := by
    simp only [TwoTubePathCollisionCount.tubes,originalFamily,image_image]
    rfl
  rw [originalFamily_tubes,hTubeImage] at hdensity
  refine ⟨a,p,hp,E0,hE0,hP,hI,hTubesNative,hcap,?_,?_⟩
  · rw [hTubesNative]
    simpa only [mul_comm (NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ) 28] using hdensity
  · exact native_original_geometry D cells a N p hP E0 hsub
end NativeDenseSourceCoarseFamily
