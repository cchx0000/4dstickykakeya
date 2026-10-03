import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000

noncomputable section

namespace TwoWalkBoxComparison

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- One genuine two-leg graph walk: original slopes, the intermediate shared
plane offset, and the original intermediate and terminal points. -/
structure Walk (U V : Type*) where
  u : U
  v : V
  terminalU : U
  terminalV : V
  offset : V
  middleX : U
  middleY : V
  terminalX : U
  terminalY : V

/-- Both walks start at the same point and use the same three actual heights. -/
structure Data (U V : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  F₀ : U →L[ℝ] V
  F₁ : U →L[ℝ] V
  F₂ : U →L[ℝ] V
  commonOffset : V
  startX : U
  startY : V
  z₀ : ℝ
  z₁ : ℝ
  z₂ : ℝ
  first : Walk U V
  second : Walk U V

namespace Data
variable (D : Data U V)

def t : ℝ := D.z₁ - D.z₀
def s : ℝ := D.z₂ - D.z₁

def initialResidual (w : Walk U V) : V := w.v - D.commonOffset - D.F₀ w.u
def middleResidual (w : Walk U V) : V := w.v - w.offset - D.F₁ w.u
def terminalResidual (w : Walk U V) : V := w.terminalV - w.offset - D.F₁ w.terminalU

def firstErrorX (w : Walk U V) : U := w.middleX - D.startX - D.t • w.u
def firstErrorY (w : Walk U V) : V := w.middleY - D.startY - D.t • w.v
def secondErrorX (w : Walk U V) : U := w.terminalX - w.middleX - D.s • w.terminalU
def secondErrorY (w : Walk U V) : V := w.terminalY - w.middleY - D.s • w.terminalV

def du : U := D.second.terminalU - D.first.terminalU
def dv : V := D.second.terminalV - D.first.terminalV
def dx : U := D.second.terminalX - D.first.terminalX
def dy : V := D.second.terminalY - D.first.terminalY
def initialDu : U := D.second.u - D.first.u
def initialDv : V := D.second.v - D.first.v

def errorX : U := (D.firstErrorX D.second - D.firstErrorX D.first) +
  (D.secondErrorX D.second - D.secondErrorX D.first)
def errorY : V := (D.firstErrorY D.second - D.firstErrorY D.first) +
  (D.secondErrorY D.second - D.secondErrorY D.first)

/-- Coordinatewise graph-incidence residuals and the actual three direction
residuals at the two shared-point levels. No F₂ terminal certificate is assumed. -/
structure WalkBounds (w : Walk U V) (B e : ℝ) : Prop where
  initial_slope : ‖w.u‖ ≤ B
  initial_direction : ‖D.initialResidual w‖ ≤ e
  middle_direction : ‖D.middleResidual w‖ ≤ e
  terminal_direction : ‖D.terminalResidual w‖ ≤ e
  first_x : ‖D.firstErrorX w‖ ≤ e
  first_y : ‖D.firstErrorY w‖ ≤ e
  second_x : ‖D.secondErrorX w‖ ≤ e
  second_y : ‖D.secondErrorY w‖ ≤ e

structure Bounds (A B S e ρ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  S_nonneg : 0 ≤ S
  error_nonneg : 0 ≤ e
  rho_nonneg : 0 ≤ ρ
  slope₂ : ‖D.F₂‖ ≤ A
  slope₀₁ : ‖D.F₀ - D.F₁‖ ≤ S
  slope₁₂ : ‖D.F₁ - D.F₂‖ ≤ S
  slope₀₂ : ‖D.F₀ - D.F₂‖ ≤ S
  first_time : |D.t| ≤ ρ
  second_time : |D.s| ≤ ρ
  first_walk : D.WalkBounds D.first B e
  second_walk : D.WalkBounds D.second B e
  terminal_gap : ‖D.du‖ ≤ ρ

lemma initialDu_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) : ‖D.initialDu‖ ≤ 2 * B := by
  exact (norm_sub_le _ _).trans (by
    change ‖D.second.u‖ + ‖D.first.u‖ ≤ 2 * B
    linarith [h.first_walk.initial_slope, h.second_walk.initial_slope])

lemma initial_normal_identity :
    D.initialDv - D.F₂ D.initialDu = (D.F₀ - D.F₂) D.initialDu +
      (D.initialResidual D.second - D.initialResidual D.first) := by
  simp only [initialDv, initialDu, initialResidual, sub_apply, map_sub]
  abel

lemma terminal_normal_identity :
    D.dv - D.F₂ D.du =
      (D.F₀ - D.F₁) D.initialDu + (D.F₁ - D.F₂) D.du +
      (D.initialResidual D.second - D.initialResidual D.first) -
      (D.middleResidual D.second - D.middleResidual D.first) +
      (D.terminalResidual D.second - D.terminalResidual D.first) := by
  simp only [dv, du, initialDu, initialResidual, middleResidual, terminalResidual,
    sub_apply, map_sub]
  abel

lemma path_x_identity : D.dx = D.t • D.initialDu + D.s • D.du + D.errorX := by
  simp only [dx, initialDu, du, errorX, firstErrorX, secondErrorX]
  module

lemma path_y_identity : D.dy = D.t • D.initialDv + D.s • D.dv + D.errorY := by
  simp only [dy, initialDv, dv, errorY, firstErrorY, secondErrorY]
  module

lemma path_normal_identity : D.dy - D.F₂ D.dx =
    D.t • (D.initialDv - D.F₂ D.initialDu) + D.s • (D.dv - D.F₂ D.du) +
      (D.errorY - D.F₂ D.errorX) := by
  rw [D.path_x_identity, D.path_y_identity]
  simp only [map_add, map_smul]
  module

lemma residual_difference_bound {X : Type*} [SeminormedAddCommGroup X]
    (a b : X) (e : ℝ) (ha : ‖a‖ ≤ e) (hb : ‖b‖ ≤ e) : ‖a - b‖ ≤ 2 * e := by
  exact (norm_sub_le _ _).trans (by linarith)

lemma initial_normal_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) :
    ‖D.initialDv - D.F₂ D.initialDu‖ ≤ 2 * B * S + 2 * e := by
  rw [D.initial_normal_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      ‖(D.F₀ - D.F₂) D.initialDu‖ ≤ ‖D.F₀ - D.F₂‖ * ‖D.initialDu‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ S * (2 * B) := mul_le_mul h.slope₀₂ (D.initialDu_bound A B S e ρ h) (norm_nonneg _) h.S_nonneg
      _ = _ := by ring
  · exact residual_difference_bound _ _ e h.second_walk.initial_direction h.first_walk.initial_direction

/-- C1: the terminal normal direction estimate is derived from the actual
three direction residuals on each branch. -/
theorem terminal_normal_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) :
    ‖D.dv - D.F₂ D.du‖ ≤ (2 * B + ρ) * S + 6 * e := by
  have h₀ : ‖(D.F₀ - D.F₁) D.initialDu‖ ≤ S * (2 * B) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul h.slope₀₁
      (D.initialDu_bound A B S e ρ h) (norm_nonneg _) h.S_nonneg)
  have h₁ : ‖(D.F₁ - D.F₂) D.du‖ ≤ S * ρ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul h.slope₁₂ h.terminal_gap (norm_nonneg _) h.S_nonneg)
  have h₂ := residual_difference_bound _ _ e h.second_walk.initial_direction h.first_walk.initial_direction
  have h₃ := residual_difference_bound _ _ e h.second_walk.middle_direction h.first_walk.middle_direction
  have h₄ := residual_difference_bound _ _ e h.second_walk.terminal_direction h.first_walk.terminal_direction
  rw [D.terminal_normal_identity]
  calc
    _ ≤ (‖(D.F₀ - D.F₁) D.initialDu + (D.F₁ - D.F₂) D.du +
        (D.initialResidual D.second - D.initialResidual D.first)‖ +
        ‖D.middleResidual D.second - D.middleResidual D.first‖) +
        ‖D.terminalResidual D.second - D.terminalResidual D.first‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ((‖(D.F₀ - D.F₁) D.initialDu‖ + ‖(D.F₁ - D.F₂) D.du‖) +
        ‖D.initialResidual D.second - D.initialResidual D.first‖ +
        ‖D.middleResidual D.second - D.middleResidual D.first‖) +
        ‖D.terminalResidual D.second - D.terminalResidual D.first‖ := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (S * (2 * B) + S * ρ + 2 * e + 2 * e) + 2 * e := by gcongr
    _ = _ := by ring

lemma errorX_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) : ‖D.errorX‖ ≤ 4 * e := by
  have h₁ := residual_difference_bound _ _ e h.second_walk.first_x h.first_walk.first_x
  have h₂ := residual_difference_bound _ _ e h.second_walk.second_x h.first_walk.second_x
  exact (norm_add_le _ _).trans (by linarith)

lemma errorY_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) : ‖D.errorY‖ ≤ 4 * e := by
  have h₁ := residual_difference_bound _ _ e h.second_walk.first_y h.first_walk.first_y
  have h₂ := residual_difference_bound _ _ e h.second_walk.second_y h.first_walk.second_y
  exact (norm_add_le _ _).trans (by linarith)

/-- C2: actual terminal tangential displacement along the two original walks. -/
theorem terminal_tangential_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) :
    ‖D.dx‖ ≤ 2 * B * ρ + ρ ^ 2 + 4 * e := by
  rw [D.path_x_identity]
  calc
    _ ≤ ‖D.t • D.initialDu‖ + ‖D.s • D.du‖ + ‖D.errorX‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ρ * (2 * B) + ρ * ρ + 4 * e := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (add_le_add
        (mul_le_mul h.first_time (D.initialDu_bound A B S e ρ h) (norm_nonneg _) h.rho_nonneg)
        (mul_le_mul h.second_time h.terminal_gap (norm_nonneg _) h.rho_nonneg))
        (D.errorX_bound A B S e ρ h)
    _ = _ := by ring

/-- C3: the normal point error is O(rho*S+e); the small normal scale is not
replaced by a tangential O(rho²) error. Equal/reversed heights are allowed. -/
theorem terminal_point_normal_bound (A B S e ρ : ℝ) (h : D.Bounds A B S e ρ) :
    ‖D.dy - D.F₂ D.dx‖ ≤ (4 * B + ρ) * ρ * S + (8 * ρ + 4 * (1 + A)) * e := by
  have hn := D.terminal_normal_bound A B S e ρ h
  have hi := D.initial_normal_bound A B S e ρ h
  have herr : ‖D.errorY - D.F₂ D.errorX‖ ≤ 4 * (1 + A) * e := by
    calc
      _ ≤ ‖D.errorY‖ + ‖D.F₂ D.errorX‖ := norm_sub_le _ _
      _ ≤ 4 * e + A * (4 * e) := add_le_add (D.errorY_bound A B S e ρ h)
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul h.slope₂
          (D.errorX_bound A B S e ρ h) (norm_nonneg _) h.A_nonneg))
      _ = _ := by ring
  rw [D.path_normal_identity]
  calc
    _ ≤ ‖D.t • (D.initialDv - D.F₂ D.initialDu)‖ +
        ‖D.s • (D.dv - D.F₂ D.du)‖ + ‖D.errorY - D.F₂ D.errorX‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ρ * (2 * B * S + 2 * e) + ρ * ((2 * B + ρ) * S + 6 * e) + 4 * (1 + A) * e := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (add_le_add
        (mul_le_mul h.first_time hi (norm_nonneg _) h.rho_nonneg)
        (mul_le_mul h.second_time hn (norm_nonneg _) h.rho_nonneg)) herr
    _ = _ := by ring

end Data
/-- Explicit constants in the closed scalar-scale comparison. -/
def tangentialConstant (B E : ℝ) : ℝ := 2 * B + 1 + 4 * E
def normalPointConstant (A B E S₀ : ℝ) : ℝ := (4 * B + 1) * S₀ + (12 + 4 * A) * E
def normalDirectionConstant (B E S₀ : ℝ) : ℝ := (2 * B + 1) * S₀ + 6 * E
def comparisonConstant (A B E S₀ : ℝ) : ℝ := max 1
  (max (2 + tangentialConstant B E) (1 + normalPointConstant A B E S₀ + normalDirectionConstant B E S₀))

/-- Three actual heights in a rho-interval give both needed absolute gaps,
including equal heights and either order of traversal. -/
theorem gaps_of_common_interval (z₀ z₁ z₂ a ρ : ℝ)
    (h₀ : z₀ ∈ Set.Icc a (a + ρ)) (h₁ : z₁ ∈ Set.Icc a (a + ρ))
    (h₂ : z₂ ∈ Set.Icc a (a + ρ)) : |z₁ - z₀| ≤ ρ ∧ |z₂ - z₁| ≤ ρ := by
  obtain ⟨h₀l, h₀u⟩ := h₀
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The explicit stronger normal point estimate retains rho*sigma+delta. -/
theorem sharp_normal_point_bound (D : Data U V) (A B E S₀ δ σ ρ : ℝ)
    (h : D.Bounds A B (S₀ * σ) (E * δ) ρ) (hE : 0 ≤ E) (hS : 0 ≤ S₀)
    (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) (hρ : ρ ≤ 1) :
    ‖D.dy - D.F₂ D.dx‖ ≤ (4 * B + 1) * S₀ * ρ * σ + (12 + 4 * A) * E * δ := by
  have hA := h.A_nonneg
  have hB := h.B_nonneg
  have hρ₀ := h.rho_nonneg
  calc
    _ ≤ (4 * B + ρ) * ρ * (S₀ * σ) + (8 * ρ + 4 * (1 + A)) * (E * δ) :=
      D.terminal_point_normal_bound A B (S₀ * σ) (E * δ) ρ h
    _ ≤ (4 * B + 1) * ρ * (S₀ * σ) + (12 + 4 * A) * (E * δ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : 4 * B + ρ ≤ 4 * B + 1) hρ₀)
          (mul_nonneg hS hσ)
      · exact mul_le_mul_of_nonneg_right (by linarith : 8 * ρ + 4 * (1 + A) ≤ 12 + 4 * A)
          (mul_nonneg hE hδ)
    _ = _ := by ring

/-- Derived direction, tangential, and normal bounds in the FINAL box scales.
The stronger source restriction rho²≤sigma is not needed for this endpoint. -/
theorem normalized_gap_bounds (D : Data U V) (A B E S₀ δ σ ρ : ℝ)
    (h : D.Bounds A B (S₀ * σ) (E * δ) ρ) (hE : 0 ≤ E) (hS : 0 ≤ S₀)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ) (hσρ : σ ≤ ρ) (hρ : ρ ≤ 1) :
    ‖D.dv - D.F₂ D.du‖ ≤ normalDirectionConstant B E S₀ * σ ∧
      ‖D.dx‖ ≤ tangentialConstant B E * ρ ∧
      ‖D.dy - D.F₂ D.dx‖ ≤ normalPointConstant A B E S₀ * σ := by
  have hA := h.A_nonneg
  have hB := h.B_nonneg
  have hρ₀ := h.rho_nonneg
  have hσ : 0 ≤ σ := hδ.trans hδσ
  have hδρ := hδσ.trans hσρ
  constructor
  · calc
      _ ≤ (2 * B + ρ) * (S₀ * σ) + 6 * (E * δ) := D.terminal_normal_bound A B (S₀ * σ) (E * δ) ρ h
      _ ≤ (2 * B + 1) * (S₀ * σ) + 6 * (E * σ) := by gcongr
      _ = _ := by dsimp [normalDirectionConstant]; ring
  constructor
  · have hsq : ρ ^ 2 ≤ ρ := by nlinarith
    calc
      _ ≤ 2 * B * ρ + ρ ^ 2 + 4 * (E * δ) := D.terminal_tangential_bound A B (S₀ * σ) (E * δ) ρ h
      _ ≤ 2 * B * ρ + ρ + 4 * (E * ρ) := by gcongr
      _ = _ := by dsimp [tangentialConstant]; ring
  · calc
      _ ≤ (4 * B + 1) * S₀ * ρ * σ + (12 + 4 * A) * E * δ :=
        sharp_normal_point_bound D A B E S₀ δ σ ρ h hE hS hδ hσ hρ
      _ ≤ (4 * B + 1) * S₀ * 1 * σ + (12 + 4 * A) * E * σ := by gcongr
      _ = _ := by dsimp [normalPointConstant]; ring

abbrev SpaceTime (U V : Type*) := U × V × ℝ

def tangentResidual (w : Walk U V) (z : ℝ) (p : SpaceTime U V) : U :=
  p.1 - w.terminalX - (p.2.2 - z) • w.terminalU

def normalResidual (F : U →L[ℝ] V) (w : Walk U V) (z : ℝ) (p : SpaceTime U V) : V :=
  p.2.1 - w.terminalY - (p.2.2 - z) • w.terminalV - F (tangentResidual w z p)

/-- An actual anisotropic affine box, written by its tangential and normal
residual inequalities in the chosen norms. Finite real products use sup norms. -/
def box (F : U →L[ℝ] V) (w : Walk U V) (z ρ σ L : ℝ) : Set (SpaceTime U V) :=
  {p | |p.2.2 - z| ≤ L ∧ ‖tangentResidual w z p‖ ≤ L * ρ ∧
    ‖normalResidual F w z p‖ ≤ L * σ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma tangentResidual_change (w₁ w₂ : Walk U V) (z : ℝ) (p : SpaceTime U V) :
    tangentResidual w₂ z p = tangentResidual w₁ z p - (w₂.terminalX - w₁.terminalX) -
      (p.2.2 - z) • (w₂.terminalU - w₁.terminalU) := by
  dsimp [tangentResidual]
  module

lemma normalResidual_change (F : U →L[ℝ] V) (w₁ w₂ : Walk U V) (z : ℝ) (p : SpaceTime U V) :
    normalResidual F w₂ z p = normalResidual F w₁ z p -
      ((w₂.terminalY - w₁.terminalY) - F (w₂.terminalX - w₁.terminalX)) -
      (p.2.2 - z) • ((w₂.terminalV - w₁.terminalV) - F (w₂.terminalU - w₁.terminalU)) := by
  simp only [normalResidual, tangentResidual, map_sub, map_smul]
  module

/-- Direct subtraction of residuals gives an inclusion of the explicitly
constructed boxes. The final theorem supplies every gap bound from incidences. -/
lemma box_subset_of_gaps (F : U →L[ℝ] V) (w₁ w₂ : Walk U V)
    (z ρ σ Pₓ Pₙ Dₙ C L : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hPₓ : 0 ≤ Pₓ) (hPₙ : 0 ≤ Pₙ) (hL : 1 ≤ L)
    (hC₀ : 1 ≤ C) (hCₓ : 2 + Pₓ ≤ C) (hCₙ : 1 + Pₙ + Dₙ ≤ C)
    (hdu : ‖w₂.terminalU - w₁.terminalU‖ ≤ ρ)
    (hdx : ‖w₂.terminalX - w₁.terminalX‖ ≤ Pₓ * ρ)
    (hdn : ‖(w₂.terminalV - w₁.terminalV) - F (w₂.terminalU - w₁.terminalU)‖ ≤ Dₙ * σ)
    (hpn : ‖(w₂.terminalY - w₁.terminalY) - F (w₂.terminalX - w₁.terminalX)‖ ≤ Pₙ * σ) :
    box F w₁ z ρ σ L ⊆ box F w₂ z ρ σ (C * L) := by
  have hL₀ : 0 ≤ L := by linarith
  have hxcoef : L + Pₓ + L ≤ C * L := by
    have hh : (2 + Pₓ) * L ≤ C * L := mul_le_mul_of_nonneg_right hCₓ hL₀
    nlinarith
  have hncoef : L + Pₙ + L * Dₙ ≤ C * L := by
    have hh : (1 + Pₙ + Dₙ) * L ≤ C * L := mul_le_mul_of_nonneg_right hCₙ hL₀
    nlinarith
  intro p hp
  obtain ⟨ht, hx, hn⟩ := hp
  refine ⟨ht.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₀ hL₀), ?_, ?_⟩
  · rw [tangentResidual_change w₁ w₂ z p]
    calc
      _ ≤ ‖tangentResidual w₁ z p‖ + ‖w₂.terminalX - w₁.terminalX‖ +
          ‖(p.2.2 - z) • (w₂.terminalU - w₁.terminalU)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ L * ρ + Pₓ * ρ + L * ρ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (add_le_add hx hdx) (mul_le_mul ht hdu (norm_nonneg _) hL₀)
      _ = (L + Pₓ + L) * ρ := by ring
      _ ≤ (C * L) * ρ := mul_le_mul_of_nonneg_right hxcoef hρ
  · rw [normalResidual_change F w₁ w₂ z p]
    calc
      _ ≤ ‖normalResidual F w₁ z p‖ +
          ‖(w₂.terminalY - w₁.terminalY) - F (w₂.terminalX - w₁.terminalX)‖ +
          ‖(p.2.2 - z) • ((w₂.terminalV - w₁.terminalV) - F (w₂.terminalU - w₁.terminalU))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ L * σ + Pₙ * σ + L * (Dₙ * σ) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (add_le_add hn hpn) (mul_le_mul ht hdn (norm_nonneg _) hL₀)
      _ = (L + Pₙ + L * Dₙ) * σ := by ring
      _ ≤ (C * L) * σ := mul_le_mul_of_nonneg_right hncoef hσ

lemma normal_gap_reverse (F : U →L[ℝ] V) (x₁ x₂ : U) (y₁ y₂ : V) :
    ‖(y₁ - y₂) - F (x₁ - x₂)‖ = ‖(y₂ - y₁) - F (x₂ - x₁)‖ := by
  rw [show (y₁ - y₂) - F (x₁ - x₂) = -((y₂ - y₁) - F (x₂ - x₁)) by
    simp only [map_sub]
    abel, norm_neg]

/-- Claim 19.3: mutual containment of the two ACTUAL adapted boxes, derived
from the genuine two-walk incidence/direction errors. No higher-grain, KT,
Frostman, normal-direction certificate, or nonzero time-gap input is used.
The original point and tube-slope labels in D are unchanged. -/
theorem two_walk_box_comparison (D : Data U V) (A B E S₀ δ σ ρ : ℝ)
    (h : D.Bounds A B (S₀ * σ) (E * δ) ρ) (hE : 0 ≤ E) (hS : 0 ≤ S₀)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ) (hσρ : σ ≤ ρ) (hρ : ρ ≤ 1) (L : ℝ) (hL : 1 ≤ L) :
    box D.F₂ D.first D.z₂ ρ σ L ⊆
        box D.F₂ D.second D.z₂ ρ σ (comparisonConstant A B E S₀ * L) ∧
      box D.F₂ D.second D.z₂ ρ σ L ⊆
        box D.F₂ D.first D.z₂ ρ σ (comparisonConstant A B E S₀ * L) := by
  obtain ⟨hdn, hdx, hpn⟩ := normalized_gap_bounds D A B E S₀ δ σ ρ h hE hS hδ hδσ hσρ hρ
  have hA := h.A_nonneg
  have hB := h.B_nonneg
  have hσ := hδ.trans hδσ
  have hPₓ : 0 ≤ tangentialConstant B E := by unfold tangentialConstant; positivity
  have hPₙ : 0 ≤ normalPointConstant A B E S₀ := by unfold normalPointConstant; positivity
  have hC₀ : 1 ≤ comparisonConstant A B E S₀ := le_max_left _ _
  have hCₓ : 2 + tangentialConstant B E ≤ comparisonConstant A B E S₀ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCₙ : 1 + normalPointConstant A B E S₀ + normalDirectionConstant B E S₀ ≤ comparisonConstant A B E S₀ :=
    (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · exact box_subset_of_gaps D.F₂ D.first D.second D.z₂ ρ σ _ _ _ _ L
      h.rho_nonneg hσ hPₓ hPₙ hL hC₀ hCₓ hCₙ h.terminal_gap hdx hdn hpn
  · apply box_subset_of_gaps D.F₂ D.second D.first D.z₂ ρ σ _ _ _ _ L
      h.rho_nonneg hσ hPₓ hPₙ hL hC₀ hCₓ hCₙ
    · simpa only [Data.du, norm_sub_rev] using h.terminal_gap
    · simpa only [Data.dx, norm_sub_rev] using hdx
    · rw [normal_gap_reverse]
      exact hdn
    · rw [normal_gap_reverse]
      exact hpn

end TwoWalkBoxComparison
