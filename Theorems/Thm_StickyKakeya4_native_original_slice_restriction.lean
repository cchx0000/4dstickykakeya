import Theorems.Thm_StickyKakeya4_native_uniform_multiplicity_restriction
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeOriginalSliceRestriction
open Classical Finset SelfUniform IncidenceBinTransfer NativeOriginalSlicePopulation
open NativeWeightedPointPopulations NativeSelectedPhysicalMultiplicity
variable {T : Type*}

/-- Prepared-scale horizontal ball homogeneity constructed from original physical
incidences. The same selected ORIGINAL labels witness retention, whole heavy
fibers, every spatial population, and every actual phase/time degree. This proves
the finite population ingredient of (128); it does not assume or assert the
AD exponent estimates (130)--(135). -/
theorem original_slice_ball_population_with_restriction
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
      (∀ J ⊆ B, P.lam * NativeSelectedPhysicalMultiplicity.multiplicity J ≤
        (2 * P.K * (NativeSourceSizeBounds.radix P.incidences.card L : ℝ) ^ 2) *
          NativeSelectedPhysicalMultiplicity.multiplicity B) := by
  classical
  obtain ⟨B, hB, hneB, hret, hpoint, _hspatial, hphase, hcounts⟩ :=
    refine_original_incidence_labels P hP hne hL radii timeDiv offsetMesh slopeMesh
  let E := originalPullback P B
  have hneE : E.Nonempty := by
    apply card_pos.mp
    rw [show E = originalPullback P B from rfl, originalPullback_mass]
    exact SelfUniform.mass_pos (originalWeight P) hneB (fun _ hb => originalWeight_pos P (hB hb))
  refine ⟨E, B, originalPullback_subset P B, hneE, hB, originalPullback_bins P B hB,
    ?_, hret, ?_, ?_, ?_⟩
  · intro b hb
    have he := originalPullback_fiber P B hb
    exact ⟨he, he.symm ▸ (mem_heavyBins.mp (hB hb)).2⟩
  · intro j hj
    rw [show E = originalPullback P B from rfl, originalPullback_support P B hB]
    have hcyl (c : Cell) :
        classPoints (B.image Prod.snd) (spatialLabel (radii j)) c =
          NativeSliceGridGeometry.cylinder (B.image Prod.snd) (radii j) c := by
      ext q
      simp only [classPoints, NativeSliceGridGeometry.cylinder, mem_filter]
      rfl
    apply NativeSliceGridGeometry.gridBall_card_comparable _ _ _ hj
    intro a ha b hb
    rw [← hcyl a, ← hcyl b]
    exact hcounts j a ha b hb
  · intro j a ha b hb
    rw [show E = originalPullback P B from rfl, originalPullback_degree,
      originalPullback_degree]
    exact hphase j _ (mem_filter.mp ha).2 _ (mem_filter.mp hb).2
  · intro J hJB
    exact NativeUniformMultiplicityRestriction.selected_restriction_multiplicity P hP B hB hneB _ hpoint J hJB
/-- Actual same-support homogeneity and multiplicity from original physical
incidences. The multiplicity conclusion is derived from retained mass, original
shading density, and original tube/support cardinalities. -/
theorem original_slice_population_with_multiplicity_and_restriction
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
        (2 * P.K * refinementLoss d L * P.δ * P.oldSupport.card) ≤ multiplicity B ∧
      (∀ J ⊆ B, P.lam * multiplicity J ≤
        (2 * P.K * (NativeSourceSizeBounds.radix P.incidences.card L : ℝ) ^ 2) * multiplicity B) := by
  obtain ⟨E, B, hEI, hEn, hB, hbins, hwhole, hret, hball, hphase, hrestrict⟩ :=
    original_slice_ball_population_with_restriction P hP hne hL
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
    source_count_lower_multiplicity P hP hne B hB hneB _ (refinementLoss_pos d L) hret', hrestrict⟩
end NativeOriginalSliceRestriction
