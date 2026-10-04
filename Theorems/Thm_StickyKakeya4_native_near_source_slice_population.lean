import Theorems.Thm_StickyKakeya4_native_near_extremal_physical_parent
import Theorems.Thm_StickyKakeya4_native_original_slice_multiplicity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeNearSourceSlicePopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeNearExtremalPhysicalParent NativeFiniteKakeyaExponent
open NativeOriginalSlicePopulation NativeSelectedPhysicalMultiplicity IncidenceBinTransfer SelfUniform
open scoped ENNReal

/-- Every selected physical label has a unique ORIGINAL cell label. The exact
original subset and its cardinality are constructed by preimage, not postulated. -/
lemma original_subset_readback {n : ℕ} (D : FiniteScaleSource n) (cells : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (p : Parent) (E : Finset (Fin n × Cell))
    (hE : E ⊆ (data D cells a N p).incidences) :
    ∃ E0 ⊆ incidences cells,
      E0.image (fun z => (z.1, NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2)) = E ∧
      E0.card = E.card := by
  let f : Fin n × Index → Fin n × Cell := fun z =>
    (z.1, NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2)
  let E0 := (incidences cells).filter (fun z => f z ∈ E)
  have himage : E0.image f = E := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hw).2
    · intro hz
      have hp := hE hz
      obtain ⟨w, hw, he⟩ := mem_image.mp hp
      change f w = z at he
      exact mem_image.mpr ⟨w, mem_filter.mpr ⟨(mem_filter.mp hw).1, by rw [he]; exact hz⟩, he⟩
  have hinj : Function.Injective f := by
    intro z w h
    have hf : z.1 = w.1 := congrArg (fun q : Fin n × Cell => q.1) h
    have hs : NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2 =
        NativeOriginalCellChartGeometry.chartIndex (shift D a) w.2 :=
      congrArg (fun q : Fin n × Cell => q.2) h
    exact Prod.ext hf ((NativeOriginalCellChartGeometry.chartIndex_injective _) hs)
  refine ⟨E0, filter_subset _ _, himage, ?_⟩
  have hh := card_image_of_injective E0 hinj
  rw [himage] at hh
  exact hh.symm

/-- Original admissible near-extremizer -> actual chart/parent -> actual physical
data -> ONE original-incidence refinement carrying all horizontal and phase
populations. All losses below are computed counts/constants, not AD certificates. -/
theorem near_source_slice_population (hk : 0 < extremalExponent)
    {theta0 delta0 : ℝ} (htheta0 : 0 < theta0) (hdelta0 : 0 < delta0)
    (N : ℕ) (hN : 0 < N) {L d : ℕ} (hL : 0 < L)
    (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ theta : ℝ, 0 < theta ∧ theta < theta0 ∧
      ∃ (n : ℕ) (D : FiniteScaleSource n) (cells : Fin n → Finset Index) (a : ℝ) (p : Parent),
        0 < D.thickness ∧ D.thickness < delta0 ∧
        IsWangZakharovNativeFiniteInput D theta ∧
        (∀ i, D.shading i = wzCellShading (mesh D) cells i) ∧
        p ∈ parents D a N ∧
        (let P := data D cells a N p
         ∃ E B : Finset (Fin n × Cell), ∃ E0 : Finset (Fin n × Index),
          E0 ⊆ incidences cells ∧
          E0.image (fun z => (z.1, NativeOriginalCellChartGeometry.chartIndex (shift D a) z.2)) = E ∧
          E0.card = E.card ∧ P.Hypotheses ∧
          E ⊆ P.incidences ∧ E.Nonempty ∧ B ⊆ P.newIncidences ∧
          @bins (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin = B ∧
          (∀ b ∈ B,
            @binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin b =
              @binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance P.incidences P.cellBin b ∧
            P.m ≤ (@binFiber (Fin n) Cell Cell (Classical.decEq _) inferInstance E P.cellBin b).card) ∧
          (incidences cells).card ≤ (parents D a N).card * refinementLoss d L * E0.card ∧
          (∀ j : Fin d, 0 < radii j →
            ∀ x ∈ E.image (fun z => P.cellBin z.2), ∀ y ∈ E.image (fun z => P.cellBin z.2),
              (NativeSliceGridGeometry.gridBall (E.image (fun z => P.cellBin z.2)) (radii j) x).card ≤
                (27 * NativeSourceSizeBounds.radix P.incidences.card L ^ 4) *
                (NativeSliceGridGeometry.gridBall (E.image (fun z => P.cellBin z.2)) (radii j) y).card) ∧
          (∀ j : Fin d, ∀ u ∈ E, ∀ v ∈ E,
            degree (fun _ => 1) (fun c e =>
              phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c) =
              phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E u ≤
            NativeSourceSizeBounds.radix P.incidences.card L ^ 2 *
              degree (fun _ => 1) (fun c e =>
                phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c) =
                phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E v) ∧
          ENNReal.ofReal P.lam *
              (ENNReal.ofReal D.thickness).rpow (-extremalExponent + theta) ≤
            (parents D a N).card * ENNReal.ofReal (2 * P.K * refinementLoss d L) *
              ENNReal.ofReal (NativeSelectedPhysicalMultiplicity.multiplicity B)) := by
  obtain ⟨theta, htheta, htheta0', n, D, cells, a, p, hd, hsmall, hinput, hc,
    _hne, hp, hP, hneP, _hdelta, hparentRet, _hbackbone, _hdensity, _hparams, _hvol, hnear⟩ :=
    exists_near_extremal_physical_parent hk htheta0 hdelta0 N hN
  let P := data D cells a N p
  obtain ⟨E, B, hEI, hEn, hB, hbins, hwhole, hret, hballs, hphase, hmul, _hcount⟩ :=
    NativeOriginalSliceMultiplicity.original_slice_population_with_multiplicity P hP hneP hL
      radii timeDiv offsetMesh slopeMesh
  obtain ⟨E0, hE0, hread, hcard⟩ := original_subset_readback D cells a N p E hEI
  refine ⟨theta, htheta, htheta0', n, D, cells, a, p, hd, hsmall, hinput, hc, hp,
    E, B, E0, hE0, hread, hcard, hP, hEI, hEn, hB, hbins, hwhole, ?_, hballs, hphase, ?_⟩
  · rw [hcard]
    have hr : P.incidences.card ≤ refinementLoss d L * E.card := hret
    calc
      (incidences cells).card ≤ (parents D a N).card * P.incidences.card := hparentRet
      _ ≤ (parents D a N).card * (refinementLoss d L * E.card) := Nat.mul_le_mul_left _ hr
      _ = _ := by ring
  · have hC : 0 ≤ 2 * P.K * (refinementLoss d L : ℝ) := by
      exact mul_nonneg (mul_nonneg (by norm_num) P.K_pos.le) (Nat.cast_nonneg _)
    have hmul' := ENNReal.ofReal_le_ofReal hmul
    rw [ENNReal.ofReal_mul hP.lambda_pos.le, ENNReal.ofReal_mul hC] at hmul'
    calc
      _ ≤ ENNReal.ofReal P.lam *
          ((parents D a N).card * ENNReal.ofReal P.oldMultiplicity) := mul_le_mul' le_rfl hnear
      _ = (parents D a N).card * (ENNReal.ofReal P.lam * ENNReal.ofReal P.oldMultiplicity) := by ring
      _ ≤ (parents D a N).card * (ENNReal.ofReal (2 * P.K * refinementLoss d L) *
          ENNReal.ofReal (NativeSelectedPhysicalMultiplicity.multiplicity B)) := mul_le_mul' le_rfl hmul'
      _ = _ := by ring
end NativeNearSourceSlicePopulation
