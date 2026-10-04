import Theorems.Thm_StickyKakeya4_original_core_endpoint_lifting
import Theorems.Thm_StickyKakeya4_original_w_adapted_boxes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalCoreBoxPaths
open Classical OriginalWCoreDynamics OriginalCoreEndpointLifting

/-- Literal adapted boxes increase with their real dilation parameter. -/
theorem box_mono {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : U →L[ℝ] V) (w : TwoWalkBoxComparison.Walk U V)
    (z rho sigma L₁ L₂ : ℝ) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (hL : L₁ ≤ L₂) :
    TwoWalkBoxComparison.box F w z rho sigma L₁ ⊆
      TwoWalkBoxComparison.box F w z rho sigma L₂ := by
  intro p hp
  exact ⟨hp.1.trans hL,
    hp.2.1.trans (mul_le_mul_of_nonneg_right hL hrho),
    hp.2.2.trans (mul_le_mul_of_nonneg_right hL hsigma)⟩

/-- The boxes attached to actual original state representatives are monotone. -/
theorem coreBox_mono {P T U V : Type*} [DecidableEq P] [DecidableEq T]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : Finset (P × T)) (height : P → ℝ) (x : P → U) (y : P → V)
    (u : T → U) (v : T → V) (F : ℝ → U →L[ℝ] V)
    (S : Finset (ℝ × T)) (hSV : S ⊆ OriginalWCoarseEscapeMenus.vertices I height)
    (state : Core S) (rho sigma L₁ L₂ : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hL : L₁ ≤ L₂) :
    OriginalWAdaptedBoxes.coreBox I height x y u v F S hSV state rho sigma L₁ ⊆
      OriginalWAdaptedBoxes.coreBox I height x y u v F S hSV state rho sigma L₂ := by
  exact box_mono _ _ _ rho sigma L₁ L₂ hrho hsigma hL

variable {P T K A Ω : Type*}
  [DecidableEq P] [DecidableEq T] [DecidableEq K] [DecidableEq A]

/-- Generic composition over the actual occupied one-step menu endpoints.
For the physical boxes, the step hypothesis is supplied by
`OriginalWAdaptedBoxes.constructed_successor_box_comparison`. -/
theorem oneStates_box_comparison
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (B : Core S → ℝ → Set Ω) (C : ℝ) (hC : 1 ≤ C)
    (hmono : ∀ state L₁ L₂, L₁ ≤ L₂ → B state L₁ ⊆ B state L₂)
    (hstep : ∀ state g, g ∈ M I height cell angle S state → ∀ L, 1 ≤ L →
      B state L ⊆ B (next I height cell angle S state g) (C*L) ∧
      B (next I height cell angle S state g) L ⊆ B state (C*L))
    (root state : Core S) (hs : state ∈ oneStates I height cell angle S root)
    (L : ℝ) (hL : 1 ≤ L) :
    B root L ⊆ B state (C*L) ∧ B state L ⊆ B root (C*L) := by
  rcases Finset.mem_insert.mp hs with rfl | hs
  · have hLC : L ≤ C*L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (zero_le_one.trans hL)
    exact ⟨hmono state L (C*L) hLC,hmono state L (C*L) hLC⟩
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hs
    exact hstep root g hg L hL

/-- Generic two-step composition over the exact menu paths in `twoStates`.
Root and one-step endpoints are included at the common dilation C² L.
This is a path-composition helper, not a population or density hypothesis. -/
theorem twoStates_box_comparison
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (B : Core S → ℝ → Set Ω) (C : ℝ) (hC : 1 ≤ C)
    (hmono : ∀ state L₁ L₂, L₁ ≤ L₂ → B state L₁ ⊆ B state L₂)
    (hstep : ∀ state g, g ∈ M I height cell angle S state → ∀ L, 1 ≤ L →
      B state L ⊆ B (next I height cell angle S state g) (C*L) ∧
      B (next I height cell angle S state g) L ⊆ B state (C*L))
    (root state : Core S) (hs : state ∈ twoStates I height cell angle S root)
    (L : ℝ) (hL : 1 ≤ L) :
    B root L ⊆ B state (C^2*L) ∧ B state L ⊆ B root (C^2*L) := by
  have hLC : L ≤ C*L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (zero_le_one.trans hL)
  have hCL : 1 ≤ C*L := hL.trans hLC
  have hCC : C*L ≤ C^2*L := by
    calc
      C*L ≤ C*(C*L) := mul_le_mul_of_nonneg_left hLC (zero_le_one.trans hC)
      _ = C^2*L := by ring
  rcases Finset.mem_insert.mp hs with rfl | hs
  · exact ⟨hmono state L (C^2*L) (hLC.trans hCC),
      hmono state L (C^2*L) (hLC.trans hCC)⟩
  · rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hs
      have h := hstep root g hg L hL
      exact ⟨h.1.trans (hmono _ (C*L) (C^2*L) hCC),
        h.2.trans (hmono _ (C*L) (C^2*L) hCC)⟩
    · obtain ⟨gs,hgs,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨hg₁,hg₂⟩ := (TwoStepMenuPaths.mem_paths _ _ gs).mp hgs
      have h₁ := hstep root gs.1 hg₁ L hL
      have h₂ := hstep (next I height cell angle S root gs.1) gs.2 hg₂ (C*L) hCL
      have h₃ := hstep (next I height cell angle S root gs.1) gs.2 hg₂ L hL
      have h₄ := hstep root gs.1 hg₁ (C*L) hCL
      have heq : C*(C*L)=C^2*L := by ring
      rw [heq] at h₂ h₄
      exact ⟨h₁.1.trans h₂.1,h₃.2.trans h₄.2⟩

end OriginalCoreBoxPaths
