import Theorems.Thm_StickyKakeya4_two_walk_box_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GrainJumpAdditiveRelation
noncomputable section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- One original arm, including the two possibly different points of its grain jump. -/
structure Arm (U V : Type*) where
  initialU : U
  initialV : V
  firstX : U
  firstY : V
  jumpX : U
  jumpY : V
  terminalU : U
  terminalV : V
  terminalX : U
  terminalY : V

structure Data (U V : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  F₀ : U →L[ℝ] V
  F₁ : U →L[ℝ] V
  F₂ : U →L[ℝ] V
  startX : U
  startY : V
  ξ : V
  t : ℝ
  s : ℝ
  first : Arm U V
  second : Arm U V

namespace Data
variable (D : Data U V)
def initialResidual (w : Arm U V) : V := w.initialV - D.ξ - D.F₀ w.initialU
def firstErrorX (w : Arm U V) : U := w.firstX - D.startX - D.t • w.initialU
def firstErrorY (w : Arm U V) : V := w.firstY - D.startY - D.t • w.initialV
def grainResidual (w : Arm U V) : V := w.jumpY - w.firstY - D.F₁ (w.jumpX - w.firstX)
def secondErrorX (w : Arm U V) : U := w.terminalX - w.jumpX - D.s • w.terminalU
def secondErrorY (w : Arm U V) : V := w.terminalY - w.jumpY - D.s • w.terminalV
def error (w : Arm U V) : V := D.t • D.initialResidual w +
  (D.firstErrorY w - D.F₁ (D.firstErrorX w)) + D.grainResidual w +
  (D.secondErrorY w - D.F₂ (D.secondErrorX w))

/-- Exact identity from physical incidences and the original grain jump. -/
lemma endpoint_identity (w : Arm U V) :
    w.terminalY - D.F₂ w.terminalX =
      D.startY - D.F₁ D.startX + D.t • D.ξ +
      D.t • ((D.F₀ - D.F₁) w.initialU) +
      (D.F₁ - D.F₂) w.jumpX +
      D.s • (w.terminalV - D.F₂ w.terminalU) + D.error w := by
  simp only [error, initialResidual, firstErrorX, firstErrorY, grainResidual,
    secondErrorX, secondErrorY, sub_apply, map_sub, map_smul]
  module

/-- The actual second arm minus first arm yields the WZ additive term. -/
lemma difference_identity :
    (D.second.terminalY - D.F₂ D.second.terminalX) -
      (D.first.terminalY - D.F₂ D.first.terminalX) -
        D.t • ((D.F₀ - D.F₁) (D.second.initialU - D.first.initialU)) =
      (D.F₁ - D.F₂) (D.second.jumpX - D.first.jumpX) +
      D.s • ((D.second.terminalV - D.first.terminalV) -
        D.F₂ (D.second.terminalU - D.first.terminalU)) +
      (D.error D.second - D.error D.first) := by
  rw [D.endpoint_identity D.second, D.endpoint_identity D.first]
  simp only [map_sub, sub_apply]
  module

structure ArmBounds (w : Arm U V) (e : ℝ) : Prop where
  initial : ‖D.initialResidual w‖ ≤ e
  first_x : ‖D.firstErrorX w‖ ≤ e
  first_y : ‖D.firstErrorY w‖ ≤ e
  grain : ‖D.grainResidual w‖ ≤ e
  second_x : ‖D.secondErrorX w‖ ≤ e
  second_y : ‖D.secondErrorY w‖ ≤ e

lemma error_bound (w : Arm U V) {A e : ℝ} (hA : 0 ≤ A) (_he : 0 ≤ e)
    (hF₁ : ‖D.F₁‖ ≤ A) (hF₂ : ‖D.F₂‖ ≤ A) (ht : |D.t| ≤ 1)
    (hw : D.ArmBounds w e) : ‖D.error w‖ ≤ (4 + 2 * A) * e := by
  have hi : ‖D.t • D.initialResidual w‖ ≤ e := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul ht hw.initial (norm_nonneg _) zero_le_one).trans_eq (one_mul e)
  have h₁ : ‖D.firstErrorY w - D.F₁ (D.firstErrorX w)‖ ≤ (1 + A) * e := by
    calc
      _ ≤ ‖D.firstErrorY w‖ + ‖D.F₁ (D.firstErrorX w)‖ := norm_sub_le _ _
      _ ≤ e + A * e := add_le_add hw.first_y
        ((D.F₁.le_opNorm _).trans (mul_le_mul hF₁ hw.first_x (norm_nonneg _) hA))
      _ = _ := by ring
  have h₂ : ‖D.secondErrorY w - D.F₂ (D.secondErrorX w)‖ ≤ (1 + A) * e := by
    calc
      _ ≤ ‖D.secondErrorY w‖ + ‖D.F₂ (D.secondErrorX w)‖ := norm_sub_le _ _
      _ ≤ e + A * e := add_le_add hw.second_y
        ((D.F₂.le_opNorm _).trans (mul_le_mul hF₂ hw.second_x (norm_nonneg _) hA))
      _ = _ := by ring
  unfold error
  calc
    _ ≤ ‖D.t • D.initialResidual w +
        (D.firstErrorY w - D.F₁ (D.firstErrorX w)) + D.grainResidual w‖ +
        ‖D.secondErrorY w - D.F₂ (D.secondErrorX w)‖ := norm_add_le _ _
    _ ≤ (‖D.t • D.initialResidual w + (D.firstErrorY w - D.F₁ (D.firstErrorX w))‖ +
        ‖D.grainResidual w‖) + (1 + A) * e := add_le_add (norm_add_le _ _) h₂
    _ ≤ ((‖D.t • D.initialResidual w‖ +
        ‖D.firstErrorY w - D.F₁ (D.firstErrorX w)‖) + e) + (1 + A) * e :=
      add_le_add (add_le_add (norm_add_le _ _) hw.grain) le_rfl
    _ ≤ (e + (1 + A) * e + e) + (1 + A) * e := by gcongr
    _ = _ := by ring

/-- Actual close jump cells and close terminal directions imply the additive
relation. No additive-image or endpoint-relation certificate is an input. -/
theorem additive_relation_bound {A S ρ τ e : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hρ : 0 ≤ ρ) (_hτ : 0 ≤ τ) (he : 0 ≤ e)
    (hF₁ : ‖D.F₁‖ ≤ A) (hF₂ : ‖D.F₂‖ ≤ A) (hFdiff : ‖D.F₁ - D.F₂‖ ≤ S * ρ)
    (ht : |D.t| ≤ 1) (hs : |D.s| ≤ ρ)
    (hfirst : D.ArmBounds D.first e) (hsecond : D.ArmBounds D.second e)
    (hjump : ‖D.second.jumpX - D.first.jumpX‖ ≤ τ)
    (hu : ‖D.second.terminalU - D.first.terminalU‖ ≤ τ)
    (hv : ‖D.second.terminalV - D.first.terminalV‖ ≤ τ) :
    ‖(D.second.terminalY - D.F₂ D.second.terminalX) -
      (D.first.terminalY - D.F₂ D.first.terminalX) -
        D.t • ((D.F₀ - D.F₁) (D.second.initialU - D.first.initialU))‖ ≤
      (S + 1 + A) * ρ * τ + (8 + 4 * A) * e := by
  have hJ : ‖(D.F₁ - D.F₂) (D.second.jumpX - D.first.jumpX)‖ ≤ S * ρ * τ :=
    ((D.F₁ - D.F₂).le_opNorm _).trans
      (mul_le_mul hFdiff hjump (norm_nonneg _) (mul_nonneg hS hρ))
  have hV : ‖(D.second.terminalV - D.first.terminalV) -
      D.F₂ (D.second.terminalU - D.first.terminalU)‖ ≤ (1 + A) * τ := by
    calc
      _ ≤ ‖D.second.terminalV - D.first.terminalV‖ +
        ‖D.F₂ (D.second.terminalU - D.first.terminalU)‖ := norm_sub_le _ _
      _ ≤ τ + A * τ := add_le_add hv
        ((D.F₂.le_opNorm _).trans (mul_le_mul hF₂ hu (norm_nonneg _) hA))
      _ = _ := by ring
  have hT : ‖D.s • ((D.second.terminalV - D.first.terminalV) -
      D.F₂ (D.second.terminalU - D.first.terminalU))‖ ≤ ρ * ((1 + A) * τ) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hs hV (norm_nonneg _) hρ
  have hE : ‖D.error D.second - D.error D.first‖ ≤ (8 + 4 * A) * e := by
    exact (norm_sub_le _ _).trans ((add_le_add
      (D.error_bound _ hA he hF₁ hF₂ ht hsecond)
      (D.error_bound _ hA he hF₁ hF₂ ht hfirst)).trans_eq (by ring))
  rw [D.difference_identity]
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add hJ hT)) hE).trans_eq (by ring))
end Data
end
end GrainJumpAdditiveRelation
