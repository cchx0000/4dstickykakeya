import Theorems.Thm_StickyKakeya4_grid_quotient_ad
import Theorems.Thm_StickyKakeya4_real_scalar_ad_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeQuotientGridCenters
open Classical Finset GridQuotientAD RealScalarADInterpolation

/-- Literal grid centers in the quotient's standard sup metric. -/
def center {d : ℕ} (mu : ℝ) (p : Lattice d) : Fin d → ℝ := fun j => mu*((p j:ℝ)+1/2)

lemma center_injective {d : ℕ} {mu : ℝ} (hmu : 0 < mu) : Function.Injective (center (d:=d) mu) := by
  intro p q he
  funext j
  have hh := congrFun he j
  dsimp only [center] at hh
  have hreal : (p j:ℝ)=(q j:ℝ) := by nlinarith only [hh,hmu]
  exact_mod_cast hreal

lemma center_dist_iff {d : ℕ} {mu : ℝ} (hmu : 0 < mu) (p q : Lattice d) (R : ℕ) :
    dist (center mu p) (center mu q) ≤ mu*(R:ℝ) ↔ p∈box q R := by
  rw [dist_pi_le_iff (by positivity),mem_box_iff]
  constructor
  · intro H j
    have hh := H j
    rw [Real.dist_eq] at hh
    have he : center mu p j-center mu q j=mu*((p j:ℝ)-(q j:ℝ)) := by dsimp [center];ring
    rw [he,abs_mul,abs_of_pos hmu] at hh
    have hb := (mul_le_mul_iff_right₀ hmu).mp hh
    exact_mod_cast hb
  · intro H j
    rw [Real.dist_eq]
    have he : center mu p j-center mu q j=mu*((p j:ℝ)-(q j:ℝ)) := by dsimp [center];ring
    rw [he,abs_mul,abs_of_pos hmu]
    apply mul_le_mul_of_nonneg_left _ hmu.le
    exact_mod_cast H j

lemma ball_card {d : ℕ} (P : Finset (Lattice d)) {mu : ℝ} (hmu : 0 < mu)
    (p : Lattice d) (R : ℕ) :
    ((P.image (center mu)).filter (fun x => dist x (center mu p) ≤ mu*(R:ℝ))).card=
      (P.filter (fun q => q∈box p R)).card := by
  have he : (P.image (center mu)).filter (fun x => dist x (center mu p) ≤ mu*(R:ℝ))=
      (P.filter (fun q => q∈box p R)).image (center mu) := by
    ext x
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hb⟩
      exact ⟨q,⟨hq,(center_dist_iff hmu q p R).mp hb⟩,rfl⟩
    · rintro ⟨q,⟨hq,hb⟩,rfl⟩
      exact ⟨⟨q,hq,rfl⟩,(center_dist_iff hmu q p R).mpr hb⟩
  rw [he]
  exact card_image_of_injective _ (center_injective hmu)

lemma quotient_ball_count {k l : ℕ} (A : Finset (Point k l)) {mu : ℝ} (hmu : 0 < mu)
    (y : Lattice l) (R : ℕ) :
    ballCount ((A.image Prod.snd).image (center mu)) (center mu y) (mu*(R:ℝ))=
      ((quotientBox A y R).card:ℝ) := by
  unfold ballCount
  rw [ball_card _ hmu]
  rfl

lemma quotient_card {k l : ℕ} (A : Finset (Point k l)) {mu : ℝ} (hmu : 0 < mu) :
    ((A.image Prod.snd).image (center mu)).card=(A.image Prod.snd).card :=
  card_image_of_injective _ (center_injective hmu)

end NativeQuotientGridCenters
