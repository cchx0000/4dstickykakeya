import Theorems.Thm_StickyKakeya4_native_fixed_compact_incidence_parent
import Theorems.Thm_StickyKakeya4_native_near_source_slice_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeFixedCompactSlicePopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalSlicePopulation NativeSelectedPhysicalMultiplicity
open IncidenceBinTransfer SelfUniform NativeFixedCompactKakeyaExponent
open scoped ENNReal

/-- Actual normalized fixed-K0 near-extremizer -> original chart/parent -> actual physical
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
        (∀ i,D.line i∈NativeUnitParentNormalization.fixedCompactClass) ∧
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
  obtain ⟨theta, htheta, htheta0', n, D, cells, a, p, hd, hsmall, hinput, hDK, hc,
    _hne, hp, hP, hneP, _hdelta, hparentRet, _hbackbone, _hdensity, _hparams, _hvol, hnear⟩ :=
    NativeFixedCompactIncidenceParent.exists_near_extremal_physical_parent hk htheta0 hdelta0 N hN
  let P := data D cells a N p
  obtain ⟨E, B, hEI, hEn, hB, hbins, hwhole, hret, hballs, hphase, hmul, _hcount⟩ :=
    NativeOriginalSliceMultiplicity.original_slice_population_with_multiplicity P hP hneP hL
      radii timeDiv offsetMesh slopeMesh
  obtain ⟨E0, hE0, hread, hcard⟩ := NativeNearSourceSlicePopulation.original_subset_readback D cells a N p E hEI
  refine ⟨theta, htheta, htheta0', n, D, cells, a, p, hd, hsmall, hinput, hDK, hc, hp,
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
end NativeFixedCompactSlicePopulation
