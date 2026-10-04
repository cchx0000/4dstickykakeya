import Theorems.Thm_StickyKakeya4_native_selected_physical_multiplicity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
noncomputable section
namespace NativeOriginalSliceMultiplicity
open Classical Finset SelfUniform IncidenceBinTransfer NativeOriginalSlicePopulation
open NativeSelectedPhysicalMultiplicity
variable {T : Type*}
/-- Actual same-support homogeneity and multiplicity from original physical
incidences. The multiplicity conclusion is derived from retained mass, original
shading density, and original tube/support cardinalities. -/
theorem original_slice_population_with_multiplicity
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (hne : P.incidences.Nonempty) {L d : ℕ} (hL : 0 < L)
    (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ E B : Finset (T × Cell), E ⊆ P.incidences ∧ E.Nonempty ∧
      B ⊆ P.newIncidences ∧ bins E P.cellBin = B ∧
      (∀ b ∈ B, binFiber E P.cellBin b = binFiber P.incidences P.cellBin b ∧
        P.m ≤ (binFiber E P.cellBin b).card) ∧
      P.incidences.card ≤ 4 * (4 * ((1 + d) + d)) ^ (((1 + d) + d) * L) * E.card ∧
      (∀ j : Fin d, 0 < radii j →
        ∀ x ∈ E.image (fun a => P.cellBin a.2), ∀ y ∈ E.image (fun a => P.cellBin a.2),
          (NativeSliceGridGeometry.gridBall (E.image (fun a => P.cellBin a.2)) (radii j) x).card ≤
            (27 * NativeSourceSizeBounds.radix P.incidences.card L ^ 4) *
            (NativeSliceGridGeometry.gridBall (E.image (fun a => P.cellBin a.2)) (radii j) y).card) ∧
      (∀ j : Fin d, ∀ a ∈ E, ∀ b ∈ E,
        degree (fun _ => 1) (fun c e =>
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c) =
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E a ≤
        NativeSourceSizeBounds.radix P.incidences.card L ^ 2 *
          degree (fun _ => 1) (fun c e =>
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin c) =
            phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) (binLabel P.cellBin e)) E b) ∧
      P.lam * P.oldMultiplicity ≤
        (2 * P.K * refinementLoss d L) * multiplicity B ∧
      P.lam ^ 2 * (usedTubes P.incidences).card /
        (2 * P.K * refinementLoss d L * P.δ * P.oldSupport.card) ≤ multiplicity B := by
  obtain ⟨E, B, hEI, hEn, hB, hbins, hwhole, hret, hball, hphase⟩ :=
    NativeOriginalSliceBallPopulation.original_slice_ball_population P hP hne hL
      radii timeDiv offsetMesh slopeMesh
  have hneB : B.Nonempty := by
    rw [← hbins]
    exact hEn.image _
  have hE : E = originalPullback P B :=
    eq_pullback_of_whole_fibers P E B hEI hbins (fun b hb => (hwhole b hb).1)
  have hret' : P.incidences.card ≤ refinementLoss d L * (originalPullback P B).card := by
    simpa only [refinementLoss, hE] using hret
  exact ⟨E, B, hEI, hEn, hB, hbins, hwhole, hret, hball, hphase,
    selected_density_multiplicity P hP hne B hB hneB _ hret',
    source_count_lower_multiplicity P hP hne B hB hneB _ (refinementLoss_pos d L) hret'⟩
end NativeOriginalSliceMultiplicity
