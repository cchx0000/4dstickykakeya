import Theorems.Thm_StickyKakeya4_native_normalized_parent_output
import Theorems.Thm_StickyKakeya4_native_original_alignment_geometry

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NativeOriginalADAlignment

open NativeOriginalParentAssembly NativeParentRefinement NativeSelectedParentPreparation NativeOriginalParentUnion
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines NativeAngularChartSelection
open ActualTubeFootprintProfiles NativeSeparatedFractionalPatches SmallFiberAlignment FractionalFiberAlignment DisjointProfileEpochs
open NativeFractionalReferenceComposition NativeContactFractionalComposition
open ShearedGridADReference NativeNormalizedParentOutput NativeOriginalAlignmentGeometry
open LiteralAffineFiberCoordinates ActualScalarADProfiles NormalizedQuantizedPatches
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A complete ORIGINAL-source construction with explicit, unabsorbed losses.
The source is only assumed AD. Stopping, epochs, chart choice, angular choice,
contact spines, integer caps, fractional refinement and whole-parent isolation
are all constructed. Every final original ball is near the SAME separated
image on which all real-radius AD and all-direction tube bounds hold. -/
theorem exists_original_AD_near_alignment (A : Finset Plane) (δ ε K t : ℝ) (Nold m Q₁ L₁ Q₂ L₂ Hwork : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (hN : 0 < Nold) (htop : scale δ Nold ≤ 1 / 64)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ CoverProfileStopping.stepBudget ε * (Nold : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hm : 0 < m) (hQ₁ : 4 ≤ Q₁) (hheight₁ : A.card ≤ Q₁ ^ L₁)
    (hQ₂ : 4 ≤ Q₂) (hheight₂ : A.card ≤ Q₂ ^ L₂) (hHwork : 0 < Hwork) :
    ∃ e : Epoch A (Index Nold), ∃ D : StoppedProfile (position A) δ ε K t Nold e.start,
      D.pair = e.index.val ∧ ∃ j : Fin 2, ∃ S : Selection A D j m Q₁ L₁ Q₂ L₂ Hwork,
      let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m S.index
      let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (S.index + 1)
      let μ := scale δ ia / 64
      let b := scale δ ib
      let N : ℕ := 2 ^ (ib - ia + 6)
      let R := workingRadii (ib - ia + 6) Hwork
      let ell := spineConstant Nold (m + 1) Q₁ L₁ K t D.loss
      δ ≤ 64 * μ ∧ 64 * μ ≤ b ∧ b ≤ 1 / 64 ∧
      μ * (N : ℝ) = b ∧ (64 * μ) / (64 * b) = 1 / (N : ℝ) ∧
      ∃ A' ⊆ S.points, A'.Nonempty ∧
        A.card ≤ (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 *
          angularCost D.pair.1 D.pair.2 m *
          (64 ^ 2 * retentionCost ((Hwork + 1) + ((Hwork + 1) + 1)) L₂) * 260 ^ 2) * A'.card ∧
        ∀ q ∈ A', ∃ F : RefinedParent ((parent A S.points b (grid (position A) b q)).image (chartPosition A j))
          μ (S.angle (grid (position A) b q)) R N Q₂ L₂ δ K t D.exponent D.loss ell,
          (A'.filter (fun p => dist (EuclideanAlignmentPatches.euclidean (position A p))
            (EuclideanAlignmentPatches.euclidean (position A q)) < 64 * b)).image (chartPosition A j) = F.points ∧
          NearGraphImage F.points μ (S.angle (grid (position A) b q)) b (chartPosition A j q) ∧
          AllRealBounds (F.points.image (vertex μ (S.angle (grid (position A) b q))))
            (ib - ia + 6) Hwork Q₂ L₂ μ (S.angle (grid (position A) b q)) b t D.exponent
            (density F.residue F.cap N t) (adConstant K t) (contactColumnConstant 2 K D.loss t ell)
            (tubeConstant D.loss) D.loss (chartPosition A j q) ∧
          1 ≤ (8192 * K * (64 : ℝ) ^ t * sourceMassCost A Nold m Q₁ L₁ D.pair.1 D.pair.2 K t) *
            density F.residue F.cap N t := by
  obtain ⟨e, D, hD, j, ⟨S⟩⟩ := exists_original_AD_selection A δ ε K t Nold m Q₁ L₁ Q₂ L₂ Hwork
    hne hδ hN htop hε hεhalf hK ht ht2 hlarge hdiam hAD hm hQ₁ hheight₁ hQ₂ hheight₂ hHwork
  let ia := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m S.index
  let ib := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (S.index + 1)
  let μ := scale δ ia / 64
  let b := scale δ ib
  let N : ℕ := 2 ^ (ib - ia + 6)
  have hboundsA := workingLevel_bounds D.pair.1 D.pair.2 m S.index D.valid.1 hm S.index_lt.le
  have hboundsB := workingLevel_bounds D.pair.1 D.pair.2 m (S.index + 1) D.valid.1 hm (by have := S.index_lt; omega)
  have habIndex : ia ≤ ib := workingLevel_mono _ _ _ (Nat.le_succ S.index)
  have hμ : 0 < μ := (native_grid_extent δ hδ ia ib habIndex).1
  have hmesh : 64 * μ = scale δ ia := by dsimp [μ]; ring
  have hNscale : μ * (N : ℝ) = b := (native_grid_extent δ hδ ia ib habIndex).2
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hab : 64 * μ ≤ b := by rw [hmesh]; exact scale_mono hδ.le habIndex
  have hμb : μ ≤ b := by linarith only [hμ, hab]
  have hell : 0 < spineConstant Nold (m + 1) Q₁ L₁ K t D.loss := by
    have hcost : (0 : ℝ) < refinementCost (m + 1) L₁ := by unfold refinementCost; positivity
    have hQR : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
    have hloss := zero_lt_one.trans_le (D.loss_ge_one hδ hε.le hK ht)
    have hKpos := zero_lt_one.trans_le hK
    unfold spineConstant
    exact div_pos (pruningRate_pos Nold hK) (by positivity)
  obtain ⟨F₀, hF₀, A', hA', hne', hret, hpatch⟩ :=
    NativeOriginalParentUnion.Selection.retain_original_points S hδ
  refine ⟨e, D, hD, j, S, ?_, hab, ?_, hNscale,
    (exact_normalized_mesh hμ hNpos hNscale).1, A', hA'.trans hF₀, hne', hret, ?_⟩
  · rw [hmesh]
    simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le ia)
  · exact (scale_mono hδ.le (hboundsB.2.trans D.valid.2)).trans htop
  · intro q hq
    obtain ⟨F, _hparent, hball⟩ := hpatch q hq
    refine ⟨F, hball,
      refined_parent_near_graph S.points j μ _ b _ _ N Q₂ L₂ δ K t D.exponent D.loss _
        F hμ hμb q rfl, ?_, ?_⟩
    · exact refined_parent_all_real_bounds D S.points S.subset j ia ib Q₂ L₂ Hwork
        hboundsA.1 habIndex hboundsB.2 hQ₂ hHwork _ _ (S.angle_bound _) hell _ F
        hδ hε.le htop hK ht ht2 hdiam hAD (chartPosition A j q)
    · have hmass := S.parent_mass (grid (position A) b q)
        ⟨q, Finset.mem_filter.mpr ⟨hF₀ (hA' hq), rfl⟩⟩
      have hmass' : (b / δ) ^ t ≤ sourceMassCost A Nold m Q₁ L₁ D.pair.1 D.pair.2 K t *
          (((parent A S.points b (grid (position A) b q)).image (chartPosition A j)).card : ℝ) := by
        rw [Finset.card_image_of_injective _ (chartPosition_injective A j)]
        exact hmass
      apply density_lower_from_parent_mass F hδ hμ (zero_le_one.trans hK) ?_ hNpos hNscale hmass'
      have hsp := (spatialConstant_pos (t := t) hK).le
      have hK0 := zero_le_one.trans hK
      unfold sourceMassCost
      positivity

end
end NativeOriginalADAlignment
