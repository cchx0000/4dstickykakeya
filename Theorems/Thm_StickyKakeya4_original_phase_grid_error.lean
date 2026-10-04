import Theorems.Thm_StickyKakeya4_native_original_phase_window_edges

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalPhaseGridError
open Classical OriginalPhaseGridPopulation OriginalWNormalizedPhase
open NativeOriginalPhaseWindowGraph

/-- Each native phase-grid corner is within one mesh in the product norm. -/
lemma scalar_floor_error {mesh : ℝ} (hmesh : 0 < mesh) (x : ℝ) :
    |mesh*(⌊x/mesh⌋:ℝ)-x| ≤ mesh := by
  have hl : mesh*(⌊x/mesh⌋:ℝ) ≤ x := by
    have hh := (le_div_iff₀ hmesh).mp (Int.floor_le (x/mesh))
    nlinarith
  have hu : x < ((⌊x/mesh⌋:ℝ)+1)*mesh :=
    (div_lt_iff₀ hmesh).mp (Int.lt_floor_add_one (x/mesh))
  exact abs_le.mpr ⟨by nlinarith,by linarith⟩

def floorLabel (mesh : ℝ) (p : Point) : Label :=
  (⌊p.1/mesh⌋,(⌊p.2.1/mesh⌋,⌊p.2.2/mesh⌋))

lemma grid_floor_error {mesh : ℝ} (hmesh : 0 < mesh) (p : Point) :
    ‖gridPoint mesh (floorLabel mesh p)-p‖ ≤ mesh := by
  exact max_le (scalar_floor_error hmesh p.1)
    (max_le (scalar_floor_error hmesh p.2.1) (scalar_floor_error hmesh p.2.2))

/-- The correct anisotropic physical meshes are r=mesh*rho and
 tau=mesh*Lip*rho. The reflected phase label is exactly the floor of the
 normalized original phase coordinates, not a replacement point set. -/
lemma original_phase_label_identity {P : Type*} (mesh rho Lip x₀ : ℝ)
    (xi₀ : ℝ × ℝ) (x : P → ℝ) (offset : P → ℝ × ℝ) (p : P) :
    phaseLabel (mesh*rho) (mesh*Lip*rho) x₀ xi₀ x offset p=
      floorLabel mesh (phaseCoordinates rho Lip x₀ xi₀ (x p) (offset p)) := by
  apply Prod.ext
  · change ⌊(x p-x₀)/(mesh*rho)⌋=⌊((x p-x₀)/rho)/mesh⌋
    congr 1
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · apply Prod.ext
    · change ⌊(xi₀.1-(offset p).1)/(mesh*Lip*rho)⌋=
        ⌊(-((Lip*rho)⁻¹)*((offset p).1-xi₀.1))/mesh⌋
      congr 1
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · change ⌊(xi₀.2-(offset p).2)/(mesh*Lip*rho)⌋=
        ⌊(-((Lip*rho)⁻¹)*((offset p).2-xi₀.2))/mesh⌋
      congr 1
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

lemma original_phase_grid_error {P : Type*} {mesh : ℝ} (hmesh : 0 < mesh)
    (rho Lip x₀ : ℝ) (xi₀ : ℝ × ℝ) (x : P → ℝ) (offset : P → ℝ × ℝ) (p : P) :
    ‖gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x₀ xi₀ x offset p)-
      phaseCoordinates rho Lip x₀ xi₀ (x p) (offset p)‖ ≤ mesh := by
  rw [original_phase_label_identity]
  exact grid_floor_error hmesh _

/-- Quantizing two actual phase endpoints increases the original relation's
 error by at most two grid meshes. -/
theorem rounded_phase_relation (a b p q d : Point) {mesh error : ℝ}
    (ha : ‖a-p‖ ≤ mesh) (hb : ‖b-q‖ ≤ mesh) (hrel : ‖p-q-d‖ ≤ error) :
    ‖a-b-d‖ ≤ error+2*mesh := by
  have hb' : ‖q-b‖ ≤ mesh := by simpa only [norm_sub_rev] using hb
  calc
    _ = ‖(a-p)+(p-q-d)+(q-b)‖ := by congr 1; abel
    _ ≤ ‖a-p‖+‖p-q-d‖+‖q-b‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ error+2*mesh := by linarith

end OriginalPhaseGridError
