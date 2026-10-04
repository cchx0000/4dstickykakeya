import Theorems.Thm_StickyKakeya4_native_paper_alignment_scales
import Theorems.Thm_StickyKakeya4_native_literal_aligned_set

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

namespace NativePlanarLemma53
open NativeFinalOriginalAlignment NativePaperAlignmentScales NativeLiteralAlignedSet
open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeOriginalParentAssembly
open NativeOriginalAlignmentGeometry NativeUniformOutputBounds NativeAngularChartSelection
open FiniteVoronoiRealADCoarsening NormalizedQuantizedPatches

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Consume all native output data into the literal planar Lemma 5.3 form:
an actual original subset, actual dyadic scales, a genuine affine map, and
Definition 5.1 graph fibers with native metric AD and all-direction tube bounds. -/
theorem nearAlignment_to_original_points {A : Finset Plane} {delta t zeta chi : ℝ}
    (hdelta : 0 < delta) (hzeta : 0 ≤ zeta) (H : NearAlignment A delta t zeta chi) :
    ∃ rho tau s : ℝ, ∃ j : Fin 2, ∃ A' : Finset Plane,
      A' ⊆ A ∧ A'.Nonempty ∧ delta ≤ rho ∧ rho < tau ∧ tau ≤ 1 ∧
      0 ≤ s ∧ s ≤ min t 1 ∧
      (∃ ir it : ℕ, rho = scale delta ir ∧ tau = scale delta it) ∧
      delta ^ (-chi) ≤ tau / rho ∧
      (rho / tau) ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      delta ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      ∀ a ∈ A', NearlyLiteralAligned
        ((localBall A' a tau).image (normalization j a tau))
        (rho / tau) t s ((rho / tau) ^ (-zeta)) := by
  rcases H with ⟨mu, b, s, j, E, angle, hmu, hb, hsource, hab, hbtop,
    ⟨ia, ib, hia, hib⟩, hs, hst, hE, hsep, hret, hpatch⟩
  obtain ⟨hsource', hscales, htop, _hepos, heone, hdeltamesh⟩ :=
    output_scale_facts hdelta hmu hb hsource hab hbtop
  have hident := output_mesh_identity hmu hb zeta
  have hretout : ((64 * mu) / (64 * b)) ^ zeta * (A.card : ℝ) ≤ (retainedPoints A E).card := by
    rw [retained_card]
    exact retention_in_output_mesh hmu hb hret
  refine ⟨64 * mu, 64 * b, s, j, retainedPoints A E, retained_subset A E,
    retained_nonempty A E hE, hsource', hscales, htop, hs, hst,
    ⟨ia, ib + 6, (output_scales_dyadic hia hib).1, (output_scales_dyadic hia hib).2⟩,
    ?_, hretout, retained_delta_power hdelta.le hdeltamesh hzeta (Nat.cast_nonneg _) hretout, ?_⟩
  · rwa [hident.2.1]
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hangle, hgraph, huniform⟩ := hpatch q hq
    have hnear := nearly_of_nearGraph_uniform hgraph huniform hmu hb hangle
      (originalBall_nonempty A E j hb hq) heone
    rw [← normalized_localBall, ← hident.2.2] at hnear
    exact hnear

/-- Native two-dimensional replacement of Lemma 5.3, with eta chosen after
the fixed positive power gap. The source normalization is diameter at most one;
this includes the native lattice square [-1/4,1/4]^2. The asserted chi is a
proved positive function, not the manuscript's printed explicit formula. -/
theorem native_planar_lemma53 {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta0 chi : ℝ, 0 < eta0 ∧ 0 < chi ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (A : Finset Plane) (delta t : ℝ),
          A.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ t → t ≤ 2 →
          (∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) → ADBounds A delta (delta ^ (-eta)) t →
          ∃ rho tau s : ℝ, ∃ j : Fin 2, ∃ A' : Finset Plane,
            A' ⊆ A ∧ A'.Nonempty ∧ delta ≤ rho ∧ rho < tau ∧ tau ≤ 1 ∧
            0 ≤ s ∧ s ≤ min t 1 ∧
            (∃ ir it : ℕ, rho = scale delta ir ∧ tau = scale delta it) ∧
            delta ^ (-chi) ≤ tau / rho ∧
            (rho / tau) ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            delta ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            ∀ a ∈ A', NearlyLiteralAligned
              ((localBall A' a tau).image (normalization j a tau))
              (rho / tau) t s ((rho / tau) ^ (-zeta)) := by
  obtain ⟨eta0, chi, delta0, heta0, _heta01, hchi, hdelta0, hdelta01, hmain⟩ :=
    exists_original_near_alignment hzeta
  refine ⟨eta0, chi, heta0, hchi, ?_⟩
  intro eta heta hetasmall
  refine ⟨delta0, hdelta0, ?_⟩
  intro A delta t hne hdelta hdeltasmall ht ht2 hdiam hAD
  have hd1 := hdeltasmall.trans hdelta01
  have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).mpr hd1
  have hK : 1 ≤ delta ^ (-eta) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.one_le_rpow hinv heta.le
  have hKsmall : delta ^ (-eta) ≤ delta ^ (-eta0) := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hinv hetasmall
  exact nearAlignment_to_original_points hdelta hzeta.le
    (hmain A delta (delta ^ (-eta)) t hne hdelta hdeltasmall hK hKsmall ht ht2 hdiam hAD)

/-- The native bounded lattice normalization supplies the metric diameter
premise without any additional rescaling or enlargement of the output tau. -/
lemma quarter_square_diameter (A : Finset Plane)
    (hbox : ∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4) :
    ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1 := by
  intro p hp q hq
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [Real.dist_eq]
  exact (abs_sub _ _).trans (by linarith [hbox p hp i, hbox q hq i])

/-- The exact bounded native planar input: the quarter-square normalization
is used directly, so the resulting local-ball radius remains at most one. -/
theorem native_quarter_square_lemma53 {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta0 chi : ℝ, 0 < eta0 ∧ 0 < chi ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (A : Finset Plane) (delta t : ℝ),
          A.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ t → t ≤ 2 →
          (∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4) → ADBounds A delta (delta ^ (-eta)) t →
          ∃ rho tau s : ℝ, ∃ j : Fin 2, ∃ A' : Finset Plane,
            A' ⊆ A ∧ A'.Nonempty ∧ delta ≤ rho ∧ rho < tau ∧ tau ≤ 1 ∧
            0 ≤ s ∧ s ≤ min t 1 ∧
            (∃ ir it : ℕ, rho = scale delta ir ∧ tau = scale delta it) ∧
            delta ^ (-chi) ≤ tau / rho ∧
            (rho / tau) ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            delta ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            ∀ a ∈ A', NearlyLiteralAligned
              ((localBall A' a tau).image (normalization j a tau))
              (rho / tau) t s ((rho / tau) ^ (-zeta)) := by
  obtain ⟨eta0, chi, heta0, hchi, hmain⟩ := native_planar_lemma53 hzeta
  refine ⟨eta0, chi, heta0, hchi, ?_⟩
  intro eta heta hetasmall
  obtain ⟨delta0, hdelta0, hwork⟩ := hmain eta heta hetasmall
  refine ⟨delta0, hdelta0, ?_⟩
  intro A delta t hne hdelta hdeltasmall ht ht2 hbox hAD
  exact hwork A delta t hne hdelta hdeltasmall ht ht2 (quarter_square_diameter A hbox) hAD

end
end NativePlanarLemma53
