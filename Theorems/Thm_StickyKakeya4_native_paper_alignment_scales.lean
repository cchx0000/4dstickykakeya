import Theorems.Thm_StickyKakeya4_native_final_original_alignment
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace NativePaperAlignmentScales
open NativeFinalOriginalAlignment NativeDyadicTubeStopping NativeDyadicTubeEpoch
open NativeOriginalParentAssembly NativeAngularChartSelection NormalizedQuantizedPatches
open EuclideanAlignmentPatches

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Original point labels are returned as their actual subset of the source. -/
def retainedPoints (A : Finset Plane) (E : Finset A) : Finset Plane := E.image (position A)

def localBall (E : Finset Plane) (a : Plane) (tau : ℝ) : Finset Plane :=
  E.filter (fun p => dist (euclidean p) (euclidean a) < tau)

lemma retained_subset (A : Finset Plane) (E : Finset A) : retainedPoints A E ⊆ A := by
  intro p hp
  obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

lemma retained_card (A : Finset Plane) (E : Finset A) : (retainedPoints A E).card = E.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

lemma retained_nonempty (A : Finset Plane) (E : Finset A) (hE : E.Nonempty) :
    (retainedPoints A E).Nonempty := hE.image _

lemma originalBall_eq_localBall (A : Finset Plane) (E : Finset A) (j : Fin 2) (b : ℝ) (q : A) :
    (localBall (retainedPoints A E) (position A q) (64 * b)).image (chartPoint j) =
      originalBall A E j b q := by
  ext p
  simp only [localBall, retainedPoints, originalBall, Finset.mem_image, Finset.mem_filter,
    chartPosition, Function.comp_apply]
  constructor
  · rintro ⟨x, ⟨⟨z, hz, rfl⟩, hd⟩, rfl⟩
    exact ⟨z, ⟨hz, hd⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hd⟩, rfl⟩
    exact ⟨position A z, ⟨⟨z, hz, rfl⟩, hd⟩, rfl⟩

lemma originalBall_nonempty (A : Finset Plane) (E : Finset A) (j : Fin 2) {b : ℝ}
    (hb : 0 < b) {q : A} (hq : q ∈ E) : (originalBall A E j b q).Nonempty := by
  apply Finset.Nonempty.image
  exact ⟨q, Finset.mem_filter.mpr ⟨hq, by simpa only [dist_self] using (show 0 < 64 * b by positivity)⟩⟩

def chartLinear (j : Fin 2) : Plane →ₗ[ℝ] Plane where
  toFun := chartPoint j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The source is only translated, dilated and coordinate-permuted. The
selected shear occurs in the graph slope, never in this affine source map. -/
def normalization (j : Fin 2) (a : Plane) (tau : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (tau⁻¹ • chartLinear j).toAffineMap - AffineMap.const ℝ Plane (tau⁻¹ • chartPoint j a)

lemma normalization_apply (j : Fin 2) (a p : Plane) (tau : ℝ) :
    normalization j a tau p = affine (chartPoint j a) tau (chartPoint j p) := by
  rw [affine_eq_smul]
  change tau⁻¹ • chartPoint j p - tau⁻¹ • chartPoint j a = tau⁻¹ • (chartPoint j p - chartPoint j a)
  rw [smul_sub]

lemma normalized_localBall (A : Finset Plane) (E : Finset A) (j : Fin 2) (b : ℝ) (q : A) :
    (localBall (retainedPoints A E) (position A q) (64 * b)).image (normalization j (position A q) (64 * b)) =
      (originalBall A E j b q).image (affine (chartPosition A j q) (64 * b)) := by
  rw [← originalBall_eq_localBall, Finset.image_image]
  apply Finset.image_congr
  intro p _hp
  exact normalization_apply j (position A q) p (64 * b)

lemma normalized_localBall_bounded (E : Finset Plane) (j : Fin 2) (a : Plane) {tau : ℝ}
    (htau : 0 < tau) :
    ∀ p ∈ (localBall E a tau).image (normalization j a tau), ∀ i : Fin 2, |p i| ≤ 1 := by
  intro p hp i
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have hd := (Finset.mem_filter.mp hq).2
  have hc := coordinate_dist_le q a (chartPerm j i)
  rw [normalization_apply]
  change |(q (chartPerm j i) - a (chartPerm j i)) / tau| ≤ 1
  rw [abs_div, abs_of_pos htau]
  exact (div_le_iff₀ htau).mpr (by nlinarith only [hc, hd])

lemma output_scale_facts {delta mu b : ℝ} (hdelta : 0 < delta) (hmu : 0 < mu)
    (hb : 0 < b) (hsource : delta ≤ 64 * mu) (hab : 64 * mu ≤ b) (hbtop : b ≤ 1 / 64) :
    delta ≤ 64 * mu ∧ 64 * mu < 64 * b ∧ 64 * b ≤ 1 ∧
      0 < (64 * mu) / (64 * b) ∧ (64 * mu) / (64 * b) ≤ 1 ∧
      delta ≤ (64 * mu) / (64 * b) := by
  have htau : 0 < 64 * b := by positivity
  have htop : 64 * b ≤ 1 := by nlinarith only [hbtop]
  refine ⟨hsource, by nlinarith only [hab, hmu], htop, by positivity, ?_, ?_⟩
  · exact (div_le_one htau).mpr (by nlinarith only [hab, hmu])
  · apply (le_div_iff₀ htau).mpr
    exact (mul_le_of_le_one_right hdelta.le htop).trans hsource

lemma output_mesh_identity {mu b : ℝ} (hmu : 0 < mu) (hb : 0 < b) (zeta : ℝ) :
    (64 * mu) / (64 * b) = 64 * (mu / (64 * b)) ∧
      (64 * b) / (64 * mu) = b / mu ∧
      ((64 * mu) / (64 * b)) ^ (-zeta) = (b / mu) ^ zeta := by
  have he : (64 * mu) / (64 * b) = mu / b := by field_simp
  refine ⟨by ring, by field_simp, ?_⟩
  rw [he, Real.rpow_neg_eq_inv_rpow, inv_div]

lemma retention_in_output_mesh {mu b zeta n n' : ℝ} (hmu : 0 < mu) (hb : 0 < b)
    (hret : n ≤ (b / mu) ^ zeta * n') :
    ((64 * mu) / (64 * b)) ^ zeta * n ≤ n' := by
  have he : ((64 * mu) / (64 * b)) * (b / mu) = 1 := by field_simp
  have hp : ((64 * mu) / (64 * b)) ^ zeta * (b / mu) ^ zeta = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), he, Real.one_rpow]
  calc
    _ ≤ ((64 * mu) / (64 * b)) ^ zeta * ((b / mu) ^ zeta * n') :=
      mul_le_mul_of_nonneg_left hret (by positivity)
    _ = n' := by rw [← mul_assoc, hp, one_mul]

lemma retained_delta_power {delta e zeta n n' : ℝ} (hdelta : 0 ≤ delta)
    (hde : delta ≤ e) (hzeta : 0 ≤ zeta) (hn : 0 ≤ n) (hret : e ^ zeta * n ≤ n') :
    delta ^ zeta * n ≤ n' :=
  (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hdelta hde hzeta) hn).trans hret

lemma output_scales_dyadic {delta mu b : ℝ} {ia ib : ℕ}
    (ha : 64 * mu = scale delta ia) (hb : b = scale delta ib) :
    64 * mu = scale delta ia ∧ 64 * b = scale delta (ib + 6) := by
  refine ⟨ha, ?_⟩
  rw [hb, scale_add]
  norm_num
  ring

end
end NativePaperAlignmentScales
