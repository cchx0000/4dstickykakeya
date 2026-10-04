import Theorems.Thm_StickyKakeya4_native_coarse_backbone_density
import Theorems.Thm_StickyKakeya4_native_original_slice_restriction
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeSameParentSourceSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentPhysicalData NativeDenseOriginalParent
open NativeOriginalShadingDensity NativeNearSourceSlicePopulation NativeDenseSourceRefinement
open NativeOriginalSlicePopulation NativeSelectedPhysicalMultiplicity IncidenceBinTransfer SelfUniform
open scoped ENNReal
/-- The actual dense-parent selector preserves its common height and
parent-relative mass inequality together with the SAME original incidence
pullback, whole fibers, and simultaneous spatial and phase refinements.
This exposes the original facts needed for full-backbone global density. -/
theorem select_same_parent_source {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (mesh D) cells i)
    (hne : (incidences cells).Nonempty) (hexp : 0≤eta+beta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      MeasureTheory.volume (markedUnitTube (D.line i) D.thickness))
    (N : ℕ) (hN : 0<N) (hscale : (N:ℝ)*(D.thickness/8)≤1)
    {L d : ℕ} (hL : 0<L) (radii timeDiv : Fin d→ℕ) (offsetMesh slopeMesh : Fin d→ℝ) :
    ∃ a : ℝ, ∃ p∈parents D a N,
      (∀ i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
      (let P := data D cells a N p
       ∃ E B : Finset (Fin n×Cell), ∃ E0 : Finset (Fin n×Index),
        E0⊆incidences cells ∧
        E0.image (fun z=>(z.1,NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2))=E ∧
        E0.card=E.card ∧ E0.image Prod.fst=E.image Prod.fst ∧
        P.Hypotheses ∧ D.thickness^(eta+beta)≤P.lam ∧
        E⊆P.incidences ∧ P.incidences.card≤refinementLoss d L*E.card ∧ E.Nonempty ∧ B⊆P.newIncidences ∧
        @bins (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin=B ∧
        NativeSourceCoarseReadback.originalFamily P (shift D a) E0=NativeOriginalHeightVertices.pointTube B ∧
        (∀ b∈B,@binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin b=
            @binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance P.incidences P.cellBin b ∧
          P.m≤(@binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin b).card) ∧
        (incidences cells).card≤2*(parents D a N).card*refinementLoss d L*E0.card ∧
        D.thickness^(eta+beta)*(E0.image Prod.fst).card≤
          (refinementLoss d L:ℝ)*(D.thickness/8)*E0.card ∧
        (∀ j : Fin d,0<radii j →
          ∀ x∈E.image (fun z=>P.cellBin z.2),∀ y∈E.image (fun z=>P.cellBin z.2),
            (NativeSliceGridGeometry.gridBall (E.image (fun z=>P.cellBin z.2)) (radii j) x).card≤
              (27*NativeSourceSizeBounds.radix P.incidences.card L^4)*
              (NativeSliceGridGeometry.gridBall (E.image (fun z=>P.cellBin z.2)) (radii j) y).card) ∧
        (∀ j : Fin d,∀ u∈E,∀ v∈E,
          degree (fun _=>1) (fun c e=>phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c)=
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E u≤
          NativeSourceSizeBounds.radix P.incidences.card L^2*
          degree (fun _=>1) (fun c e=>phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c)=
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E v) ∧
        P.lam * P.oldMultiplicity ≤ (2 * P.K * refinementLoss d L) * multiplicity B ∧
        P.lam^2 * (@usedTubes (Fin n) Cell (Classical.decEq _) P.incidences).card /
          (2 * P.K * refinementLoss d L * P.δ * P.oldSupport.card) ≤ multiplicity B ∧
        (∀ J ⊆ B, P.lam * multiplicity J ≤
          (2 * P.K * (NativeSourceSizeBounds.radix P.incidences.card L : ℝ)^2) * multiplicity B) ∧
        (D.thickness^(eta+beta)/(32*(refinementLoss d L:ℝ)))*(backbone D a N p).card ≤
          (P.σ/32)*(NativeSourceCoarseReadback.originalFamily P (shift D a) E0).card) := by
  obtain ⟨a,ha⟩ := exists_common_height h
  obtain ⟨p,hp,hnep,hparent,hden⟩ := exists_dense_parent D cells a N h.1.1 hne
  let P := data D cells a N p
  have hP := data_hypotheses h cells hcells a ha N hN hscale p hp hnep
  have hlam := dense_parent_density h cells hcells htube a N p hp hexp hden
  have hneP : P.incidences.Nonempty := hnep.image _
  obtain ⟨E,B,hEI,hEn,hB,hbins,hwhole,hret,hballs,hphase,hmul,hcount,hrestrict⟩ :=
    NativeOriginalSliceRestriction.original_slice_population_with_multiplicity_and_restriction P hP hneP hL
      radii timeDiv offsetMesh slopeMesh
  obtain ⟨E0,hE0,hread,hcard⟩ := original_subset_readback D cells a N p E hEI
  have htubes := original_readback_tubes D a E0 E hread
  have hchart : NativeSourceCoarseReadback.chartFamily (shift D a) E0=E := by
    rw [←hread]
    ext e
    simp only [NativeSourceCoarseReadback.chartFamily,mem_image]
  have hcoarse : NativeSourceCoarseReadback.originalFamily P (shift D a) E0=
      NativeOriginalHeightVertices.pointTube B := by
    rw [NativeSourceCoarseReadback.originalFamily_eq,hchart,
      NativeCoarseOriginalIncidences.incidences_eq_swapped_bins,hbins]
    ext e
    simp only [NativeOriginalHeightVertices.pointTube,mem_image]
  have hret0 : P.incidences.card ≤ refinementLoss d L*E0.card := by rwa [hcard]
  have hfull := NativeCoarseBackboneDensity.original_full_backbone_density D cells a N p hp hP E0
    (show NativeSourceCoarseReadback.chartFamily (shift D a) E0 ⊆ P.incidences by rw [hchart]; exact hEI)
    (refinementLoss d L) (refinementLoss_pos d L) (by norm_num : (0:ℝ)<32) hlam hret0
  refine ⟨a,p,hp,ha,E,B,E0,hE0,hread,hcard,htubes,hP,hlam,hEI,hret,hEn,hB,hbins,hcoarse,hwhole,?_,?_,hballs,hphase,hmul,hcount,hrestrict,?_⟩
  · rw [hcard]
    exact (hparent.trans (Nat.mul_le_mul_left _ hret)).trans_eq (by unfold refinementLoss; ring)
  · rw [hcard,htubes]
    have hh := refinement_tube_density D cells a N p hp E (refinementLoss d L)
      (Real.rpow_pos_of_pos h.1.2.1 (eta+beta)).le hP.delta_pos.le hlam hEI hret
    simpa only [data,mesh,div_div,show (2:ℝ)*4=8 by norm_num] using hh
  · simpa only [mul_comm (refinementLoss d L:ℝ) 32] using hfull

end NativeSameParentSourceSelection
