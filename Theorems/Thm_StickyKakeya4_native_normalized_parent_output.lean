import Theorems.Thm_StickyKakeya4_native_original_parent_union
import Theorems.Thm_StickyKakeya4_full_normalized_scalar_ad
import Theorems.Thm_StickyKakeya4_full_normalized_ambient_ad

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NativeNormalizedParentOutput

open NativeOriginalParentAssembly NativeParentRefinement NativeSelectedParentPreparation NativeOriginalParentUnion
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines NativeAngularChartSelection
open ActualTubeFootprintProfiles NativeSeparatedFractionalPatches SmallFiberAlignment FractionalFiberAlignment
open NativeFractionalReferenceComposition NativeContactFractionalComposition
open ShearedGridADReference ShearedGridTubeReference ShearedGridSpineColumns
open LiteralAffineFiberCoordinates ActualScalarADProfiles NativeAmbientADGeometry
open NormalizedQuantizedPatches RealScalarADInterpolation
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal geometric conclusions on one actual quantizer image. The scalar
powers use the raw mesh, explicitly 1/(64N); the separated output mesh is 1/N.
All radii are real, including the final interval above physical parent size. -/
structure AllRealBounds (P : Finset Vertex) (M H Q L : ℕ)
    (μ angle b t s dens Bad Bcolumn Btube Htube : ℝ) (c : Plane) : Prop where
  ambient : ∀ p ∈ P, ∀ r, 64 * (μ / (64 * b)) ≤ r → r ≤ 1 →
    (dens / (comparisonCost (H + 1) L Q * Bad)) * (r / (64 * (μ / (64 * b)))) ^ t ≤
      ActualScalarADProfiles.realInterpolationLoss M H t *
        ballCount (P.image (actualPoint μ angle (64 * b) c)) (actualPoint μ angle (64 * b) c p) r ∧
    ballCount (P.image (actualPoint μ angle (64 * b) c)) (actualPoint μ angle (64 * b) c p) r ≤
      ActualScalarADProfiles.realInterpolationLoss M H t * (9 * Bad) * (128 : ℝ) ^ t *
        (r / (64 * (μ / (64 * b)))) ^ t
  fibers : ∀ p ∈ P, ∀ r, 64 * (μ / (64 * b)) ≤ r → r ≤ 1 →
    (dens / (comparisonCost (H + 1) L Q * Bcolumn * Btube)) * (r / (μ / (64 * b))) ^ s ≤
      fullInterpolationLoss M H s * ballCount (fiberCoordinates P μ (64 * b) c p.2)
        (timeCoord μ (c 0) (64 * b) p.1) r ∧
    ballCount (fiberCoordinates P μ (64 * b) c p.2) (timeCoord μ (c 0) (64 * b) p.1) r ≤
      fullInterpolationLoss M H s * Btube * (r / (μ / (64 * b))) ^ s
  quotient : ∀ p ∈ P, ∀ r, 64 * (μ / (64 * b)) ≤ r → r ≤ 1 →
    (dens / (comparisonCost (H + 1) L Q * Bad * Btube)) * (r / (μ / (64 * b))) ^ (t - s) ≤
      fullInterpolationLoss M H (t - s) * ballCount (quotientCoordinates P μ angle (64 * b) c)
        (normalCoord μ angle (64 * b) c p.2) r ∧
    ballCount (quotientCoordinates P μ angle (64 * b) c) (normalCoord μ angle (64 * b) c p.2) r ≤
      fullInterpolationLoss M H (t - s) *
        max ((comparisonCost (H + 1) L Q * Bcolumn * Bad * Btube) / dens)
          ((comparisonCost (H + 1) L Q * Bcolumn * Bad) / dens) * (r / (μ / (64 * b))) ^ (t - s)
  tubes : ∀ ρ τ, 64 * (μ / (64 * b)) ≤ ρ → ρ ≤ τ →
    TraceBound (P.image (fun k => affine c (64 * b) (realized μ angle k))) ρ τ
      (170100 * Htube * (2 : ℝ) ^ s * (τ / ρ) ^ s)

/-- Original AD and the constructed refined parent imply every real-radius
ambient, scalar-fiber, scalar-quotient and all-direction tube estimate on the
SAME normalized image. There is no injectivity premise for original quantization. -/
theorem refined_parent_all_real_bounds {A : Finset Plane} {δ ε K t : ℝ} {Nold : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t Nold E₀)
    (Ω : Finset A) (hΩ : Ω ⊆ E₀) (j : Fin 2) (i k Q L Hwork : ℕ)
    (hlo : D.pair.1 ≤ i) (hik : i ≤ k) (hhi : k ≤ D.pair.2)
    (hQ : 4 ≤ Q) (hHwork : 0 < Hwork)
    (angle ell : ℝ) (hangle : |angle| ≤ 1) (hell : 0 < ell) (c : GridLabel 1)
    (F : RefinedParent ((parent A Ω (scale δ k) c).image (chartPosition A j))
      (scale δ i / 64) angle (workingRadii (k - i + 6) Hwork) (2 ^ (k - i + 6)) Q L
      δ K t D.exponent D.loss ell)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (htop : scale δ Nold ≤ 1 / 64)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t) (center : Plane) :
    AllRealBounds (F.points.image (vertex (scale δ i / 64) angle)) (k - i + 6) Hwork Q L
      (scale δ i / 64) angle (scale δ k) t D.exponent
      (density F.residue F.cap (2 ^ (k - i + 6)) t) (adConstant K t)
      (contactColumnConstant 2 K D.loss t ell) (tubeConstant D.loss) D.loss center := by
  let μ := scale δ i / 64
  let b := scale δ k
  let M := k - i + 6
  have hμ : 0 < μ := (native_grid_extent δ hδ i k hik).1
  have hb : 0 < b := scale_pos hδ k
  have hNscale : μ * ((2 ^ M : ℕ) : ℝ) = b := (native_grid_extent δ hδ i k hik).2
  have hL : 0 < 64 * b := by positivity
  have hmesh : 64 * μ = scale δ i := by dsimp [μ]; ring
  have hδa : δ ≤ 64 * μ := by
    rw [hmesh]
    simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le i)
  have hab : 64 * μ ≤ b := by rw [hmesh]; exact scale_mono hδ.le hik
  have hbone : b ≤ 1 := (scale_mono hδ.le (hhi.trans D.valid.2)).trans (htop.trans (by norm_num))
  have hsource : F.points ⊆ (parent A Ω b c).image (chartPosition A j) := F.subset.trans F.residue_subset
  have hA : F.points ⊆ A.image (chartPoint j) := by
    intro q hq
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp (hsource hq)
    exact chartPosition_mem A j r
  have hchartdiam : ∀ p ∈ A.image (chartPoint j), ∀ q ∈ A.image (chartPoint j), dist p q ≤ 1 := by
    intro p hp q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    rw [chartPoint_dist]
    exact hdiam u hu v hv
  have hglobal := actual_global_vertex_card (A.image (chartPoint j)) F.points hA hδ hμ hδa hab hbone
    hangle hK ht ht2 hchartdiam (chart_AD j A δ K t hAD)
    (fun p hp q hq => parent_chart_diameter A Ω j hb c p (hsource hp) q (hsource hq)) hNscale
  have hspan := parent_time_labels_close F.points (angle := angle) hμ hNscale
    (fun p hp => parent_chart_span A Ω j hb c p (hsource hp))
  have hscale : (μ / (64 * b)) * (2 : ℝ) ^ M = 1 / 64 := by
    have he : μ * (2 : ℝ) ^ M = b := by exact_mod_cast hNscale
    field_simp
    nlinarith only [he]
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hH : 1 ≤ D.loss := D.loss_ge_one hδ hε hK ht
  have hHpos : 0 < D.loss := zero_lt_one.trans_le hH
  have hBad : 0 < adConstant K t := by unfold adConstant referenceFactor; positivity
  have hBcol : 0 < contactColumnConstant 2 K D.loss t ell := by
    unfold contactColumnConstant NativeContactSpineColumns.contactOverlapBudget localCapacity
    positivity
  have hBtu : 0 < tubeConstant D.loss := by unfold tubeConstant; positivity
  have hCmp : 0 < comparisonCost (Hwork + 1) L Q := by
    have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    unfold comparisonCost retentionCost
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp r hrlo hrhi
    exact FullNormalizedAmbientAD.ambient_normalized_AD _ M Hwork Q L hHwork t D.exponent _ _ _ _
      μ angle (64 * b) center hμ hL hangle ht F.density_pos.le hBad.le (mul_pos hCmp hBad)
      F.counts (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hglobal) hscale hp hrlo hrhi
  · intro p hp r hrlo hrhi
    have hrlo' : μ / (64 * b) ≤ r := by have hpos := div_pos hμ hL; linarith only [hrlo, hpos]
    exact FullNormalizedScalarAD.fiber_normalized_AD _ M Hwork Q L hHwork t D.exponent _ _ _ _
      μ (64 * b) center hμ hL D.exponent_nonneg F.density_pos.le hBtu.le
      (mul_pos (mul_pos hCmp hBcol) hBtu) F.counts hspan hscale hp hrlo' hrhi
  · intro p hp r hrlo hrhi
    have hrlo' : μ / (64 * b) ≤ r := by have hpos := div_pos hμ hL; linarith only [hrlo, hpos]
    exact FullNormalizedScalarAD.quotient_normalized_AD _ M Hwork Q L hHwork t D.exponent _ _ _ _
      μ angle (64 * b) center hμ hL (D.exponent_le.trans (min_le_left _ _)) F.density_pos hBad.le hBcol.le
      (mul_pos (mul_pos hCmp hBad) hBtu) (by positivity) F.counts
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hglobal) hscale hp hrlo' hrhi
  · intro ρ τ hρ hρτ
    let E := originalPullback A j F.points
    have hE : E ⊆ parent A Ω b c := originalPullback_subset A j F.points _ hsource
    have hE₀ : E ⊆ E₀ := hE.trans ((parent_subset A Ω b c).trans hΩ)
    have hwidth : scale δ D.pair.1 ≤ (64 * b) * ρ := by
      have hlo' := scale_mono hδ.le hlo
      have hh := (div_le_iff₀ hL).mp (show 64 * μ / (64 * b) ≤ ρ by simpa only [mul_div_assoc] using hρ)
      rw [hmesh] at hh
      linarith only [hlo', hh]
    have hμρ : μ ≤ (64 * b) * ρ := by
      have hh := (div_le_iff₀ hL).mp (show 64 * μ / (64 * b) ≤ ρ by simpa only [mul_div_assoc] using hρ)
      linarith only [hh, hμ]
    have hbound := ParentAllRealTubeControl.quantized_chart_parent_trace_bound (angle := angle) (position A) D E hE₀ k
      (hlo.trans hik) hhi c (fun q hq => (Finset.mem_filter.mp (hE hq)).2) j center
      hμ hL hδ hH hwidth hμρ hρτ
    have himage : E.image (RealScaleTubeProfileTransfer.normalized
        (quantized μ angle ∘ chartPoint j ∘ position A) center (64 * b)) =
        (F.points.image (vertex μ angle)).image (fun k => affine center (64 * b) (realized μ angle k)) := by
      calc
        _ = (E.image (chartPosition A j)).image (affine center (64 * b) ∘ quantized μ angle) := by
          rw [Finset.image_image]
          rfl
        _ = F.points.image (affine center (64 * b) ∘ quantized μ angle) := by rw [originalPullback_image A j F.points hA]
        _ = _ := by rw [Finset.image_image]; rfl
    rwa [himage] at hbound

end
end NativeNormalizedParentOutput
