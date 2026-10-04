import Theorems.Thm_StickyKakeya4_parent_all_real_tube_control

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NormalizedQuantizedPatches

open NativeDyadicTubeStopping ShearedGridADReference NativeSeparatedFractionalPatches
open RealScaleTubeProfileTransfer

noncomputable section

def affine (c : Plane) (L : ℝ) (p : Plane) : Plane := normalized id c L p

lemma affine_eq_smul (c : Plane) (L : ℝ) (p : Plane) :
    affine c L p = L⁻¹ • (p - c) := by
  funext i
  simp [affine, normalized, div_eq_mul_inv, mul_comm]

lemma affine_dist (c : Plane) {L : ℝ} (hL : 0 < L) (p q : Plane) :
    dist (affine c L p) (affine c L q) = dist p q / L := by
  rw [affine_eq_smul, affine_eq_smul, dist_smul₀, dist_sub_right]
  simp [Real.norm_eq_abs, abs_of_pos hL, div_eq_mul_inv, mul_comm]

lemma affine_euclidean_dist (c : Plane) {L : ℝ} (hL : 0 < L) (p q : Plane) :
    dist (EuclideanAlignmentPatches.euclidean (affine c L p))
      (EuclideanAlignmentPatches.euclidean (affine c L q)) =
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) / L := by
  rw [affine_eq_smul, affine_eq_smul]
  change dist (L⁻¹ • (EuclideanAlignmentPatches.euclidean p - EuclideanAlignmentPatches.euclidean c))
    (L⁻¹ • (EuclideanAlignmentPatches.euclidean q - EuclideanAlignmentPatches.euclidean c)) = _
  rw [dist_smul₀, dist_sub_right]
  simp [Real.norm_eq_abs, abs_of_pos hL, div_eq_mul_inv, mul_comm]

lemma normalized_quantized_proximity (Ω : Finset Plane) (μ angle : ℝ) (hμ : 0 < μ)
    (c : Plane) {L : ℝ} (hL : 0 < L) :
    (∀ p ∈ Ω.image (affine c L), ∃ q ∈ Ω.image (affine c L ∘ quantized μ angle),
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) <
        (64 * μ / L) / 10) ∧
    (∀ q ∈ Ω.image (affine c L ∘ quantized μ angle), ∃ p ∈ Ω.image (affine c L),
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) <
        (64 * μ / L) / 10) := by
  classical
  have hm : ∀ p : Plane,
      dist (EuclideanAlignmentPatches.euclidean (affine c L p))
        (EuclideanAlignmentPatches.euclidean (affine c L (quantized μ angle p))) < (64 * μ / L) / 10 := by
    intro p
    rw [affine_euclidean_dist c hL]
    have hh := div_lt_div_of_pos_right (quantized_euclidean_movement μ angle hμ p) hL
    have he : ((64 * μ) / 10) / L = (64 * μ / L) / 10 := by ring
    rwa [he] at hh
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨_, Finset.mem_image_of_mem _ hx, hm x⟩
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨_, Finset.mem_image_of_mem _ hx, hm x⟩

lemma normalized_image_separation (Ω : Finset Plane) (μ angle : ℝ) (c : Plane)
    {L : ℝ} (hL : 0 < L)
    (hsep : ∀ p ∈ Ω.image (quantized μ angle), ∀ q ∈ Ω.image (quantized μ angle), p ≠ q →
      64 * μ ≤ dist p q) :
    ∀ p ∈ Ω.image (affine c L ∘ quantized μ angle),
      ∀ q ∈ Ω.image (affine c L ∘ quantized μ angle), p ≠ q →
        64 * μ / L ≤ dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) := by
  classical
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
  have hne : quantized μ angle x ≠ quantized μ angle y := by
    intro he
    exact hpq (congrArg (affine c L) he)
  have hh := hsep _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy) hne
  have hnorm := div_le_div_of_nonneg_right hh hL.le
  have hsup : 64 * μ / L ≤ dist (affine c L (quantized μ angle x)) (affine c L (quantized μ angle y)) := by
    rwa [affine_dist c hL]
  exact hsup.trans (EuclideanAlignmentPatches.sup_dist_le _ _)

/-- The separated output mesh is 1/N, while the underlying vertex mesh is
1/(64N). The original labels may still have repeated quantizer vertices. -/
lemma exact_normalized_mesh {μ b : ℝ} {N : ℕ} (hμ : 0 < μ) (hN : 0 < N)
    (hscale : μ * (N : ℝ) = b) :
    (64 * μ) / (64 * b) = 1 / (N : ℝ) ∧ μ / (64 * b) = 1 / (64 * (N : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← hscale]
  constructor <;> field_simp

lemma normalized_parent_coordinates (μ angle b : ℝ) (hμ : 0 < μ) (hμb : μ ≤ b)
    (p c : Plane) (hcell : ADGridCoverMenus.gridLabel b p = ADGridCoverMenus.gridLabel b c) :
    ∀ i, |affine c (64 * b) (quantized μ angle p) i| ≤ 1 / 32 := by
  have hb : 0 < b := hμ.trans_le hμb
  intro i
  have hsource : |p i - c i| < b := by
    have hd := SeparatedAlignmentPatches.same_cell_dist_lt b hb p c hcell
    have hc : |p i - c i| ≤ dist p c := by simpa only [Real.dist_eq] using dist_le_pi_dist p c i
    exact hc.trans_lt hd
  have hm := quantized_coordinate_movement μ angle hμ p i
  have hnear : |quantized μ angle p i - c i| ≤ 2 * b := by
    have hid : quantized μ angle p i - c i =
        (quantized μ angle p i - p i) + (p i - c i) := by ring
    rw [hid]
    have hh := abs_add_le (quantized μ angle p i - p i) (p i - c i)
    linarith only [hh, hm, hsource, hμb]
  change |(quantized μ angle p i - c i) / (64 * b)| ≤ _
  rw [abs_div, abs_of_pos (by positivity : 0 < 64 * b)]
  apply (div_le_iff₀ (by positivity : 0 < 64 * b)).mpr
  linarith only [hnear]

end
end NormalizedQuantizedPatches
