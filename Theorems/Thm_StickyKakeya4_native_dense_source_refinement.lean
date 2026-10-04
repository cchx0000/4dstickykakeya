import Theorems.Thm_StickyKakeya4_native_original_shading_density
import Theorems.Thm_StickyKakeya4_native_near_source_slice_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeDenseSourceRefinement
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentPhysicalData NativeDenseOriginalParent
open NativeOriginalShadingDensity NativeNearSourceSlicePopulation
open NativeOriginalSlicePopulation NativeSelectedPhysicalMultiplicity IncidenceBinTransfer SelfUniform
open scoped ENNReal

lemma refinement_tube_density {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent)
    (hp : p∈parents D a N) (E : Finset (Fin n×Cell)) (F : ℕ) {lam : ℝ}
    (hlam : 0≤lam) (hd : 0≤(data D cells a N p).δ)
    (hl : lam≤(data D cells a N p).lam)
    (hE : E⊆(data D cells a N p).incidences)
    (hret : (data D cells a N p).incidences.card≤F*E.card) :
    lam*(E.image Prod.fst).card≤(F:ℝ)*(data D cells a N p).δ*E.card := by
  have hsub : E.image Prod.fst⊆backbone D a N p := by
    intro t ht
    obtain ⟨⟨i,c⟩,hz,he⟩ := mem_image.mp ht
    change i=t at he
    subst t
    obtain ⟨k,_hk,hpar,_hchart⟩ := (mem_data_incidences D cells a N p i c).mp (hE hz)
    exact mem_filter.mpr ⟨mem_univ _,hpar⟩
  have ht : ((E.image Prod.fst).card:ℝ)≤(backbone D a N p).card := by
    exact_mod_cast card_le_card hsub
  have hr : ((data D cells a N p).incidences.card:ℝ)≤F*E.card := by exact_mod_cast hret
  calc
    _ ≤ lam*(backbone D a N p).card := mul_le_mul_of_nonneg_left ht hlam
    _ ≤ (data D cells a N p).lam*(backbone D a N p).card :=
      mul_le_mul_of_nonneg_right hl (by positivity)
    _ ≤ (data D cells a N p).δ*(data D cells a N p).incidences.card :=
      full_backbone_density D cells a N p hp
    _ ≤ (data D cells a N p).δ*((F:ℝ)*E.card) := mul_le_mul_of_nonneg_left hr hd
    _ = _ := by ring

lemma original_readback_tubes {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (E0 : Finset (Fin n×Index)) (E : Finset (Fin n×Cell))
    (hread : E0.image (fun z=>(z.1,NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2))=E) :
    E0.image Prod.fst=E.image Prod.fst := by
  rw [←hread,image_image]
  rfl

/-- Actual original source density is carried by the SAME simultaneous
spatial/phase refinement. Both the original subset and its tube-density lower
bound are constructed; no pointwise incidence regularity is assumed. -/
theorem dense_source_slice_population {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (mesh D) cells i)
    (hne : (incidences cells).Nonempty) (hexp : 0≤eta+beta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      MeasureTheory.volume (markedUnitTube (D.line i) D.thickness))
    (N : ℕ) (hN : 0<N) (hscale : (N:ℝ)*(D.thickness/8)≤1)
    {L d : ℕ} (hL : 0<L) (radii timeDiv : Fin d→ℕ) (offsetMesh slopeMesh : Fin d→ℝ) :
    ∃ a : ℝ, ∃ p∈parents D a N,
      (let P := data D cells a N p
       ∃ E B : Finset (Fin n×Cell), ∃ E0 : Finset (Fin n×Index),
        E0⊆incidences cells ∧
        E0.image (fun z=>(z.1,NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2))=E ∧
        E0.card=E.card ∧ E0.image Prod.fst=E.image Prod.fst ∧
        P.Hypotheses ∧ D.thickness^(eta+beta)≤P.lam ∧
        E⊆P.incidences ∧ E.Nonempty ∧ B⊆P.newIncidences ∧
        @bins (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin=B ∧
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
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E v)) := by
  obtain ⟨a,ha⟩ := exists_common_height h
  obtain ⟨p,hp,hnep,hparent,hden⟩ := exists_dense_parent D cells a N h.1.1 hne
  let P := data D cells a N p
  have hP := data_hypotheses h cells hcells a ha N hN hscale p hp hnep
  have hlam := dense_parent_density h cells hcells htube a N p hp hexp hden
  have hneP : P.incidences.Nonempty := hnep.image _
  obtain ⟨E,B,hEI,hEn,hB,hbins,hwhole,hret,hballs,hphase,_hmul,_hcount⟩ :=
    NativeOriginalSliceMultiplicity.original_slice_population_with_multiplicity P hP hneP hL
      radii timeDiv offsetMesh slopeMesh
  obtain ⟨E0,hE0,hread,hcard⟩ := original_subset_readback D cells a N p E hEI
  have htubes := original_readback_tubes D a E0 E hread
  refine ⟨a,p,hp,E,B,E0,hE0,hread,hcard,htubes,hP,hlam,hEI,hEn,hB,hbins,hwhole,?_,?_,hballs,hphase⟩
  · rw [hcard]
    exact (hparent.trans (Nat.mul_le_mul_left _ hret)).trans_eq (by unfold refinementLoss; ring)
  · rw [hcard,htubes]
    have hh := refinement_tube_density D cells a N p hp E (refinementLoss d L)
      (Real.rpow_pos_of_pos h.1.2.1 (eta+beta)).le hP.delta_pos.le hlam hEI hret
    simpa only [data,mesh,div_div,show (2:ℝ)*4=8 by norm_num] using hh

end NativeDenseSourceRefinement
