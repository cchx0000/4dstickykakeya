import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry
import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowConfiguredCounts
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeAnisotropicShortRowGeometry
open NativeReferenceXYGridMaps NativeMatchedShadowConfiguredGeometry
open NativeUniformRetentionTransfer

/-- Fixed Euclidean packing at the actual separated output scale. -/
lemma separated_ball_card (A : Finset E4) (delta : ℝ) (hd : 0 < delta) (c : E4)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → delta ≤ dist x y)
    (hball : ∀ x ∈ A, dist x c ≤ 2 * delta) : A.card ≤ 33 ^ 4 := by
  let f := wzDyadicCellIndex (delta / 8)
  have hinj : Set.InjOn f (A : Set E4) := by
    intro x hx y hy he
    by_contra hne
    have hcoord (v : Fin 4) : |x v - y v| ≤ delta / 8 :=
      same_floor_abs (by positivity) (congrFun he v)
    have hdist := distance_of_coordinates x y (delta / 8) (by positivity) hcoord
    have hs := hsep x hx y hy hne
    linarith
  have hsub : A.image f ⊆ columnHalo 16 16 (f c) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
    apply Fintype.mem_piFinset.mpr
    intro v
    simp only [ite_self]
    apply floor_neighbor (by positivity) 16
    have hc : |x v - c v| ≤ dist x c := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x c v
    have hb := hball x hx
    norm_num
    linarith
  calc
    A.card = (A.image f).card := (card_image_of_injOn hinj).symm
    _ ≤ (columnHalo 16 16 (f c)).card := card_le_card hsub
    _ = 33 ^ 4 := by rw [columnHalo_card]; norm_num

/-- Literal shadow-cell labels at half the output thickness. -/
def shadowLabel {X : Type*} (delta : ℝ) (front : X → E4) (z : X) : Index :=
  wzDyadicCellIndex (delta / 2) (front z)

/-- One configured point sees at most five neighboring labels per coordinate.
This inverse bound needs no separation assumption. -/
lemma inverse_point_fiber {X : Type*} (A : Finset X) (delta : ℝ) (hd : 0 < delta)
    (O : E4 ≃ₗᵢ[ℝ] E4) (front cfg : X → E4)
    (hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ delta) (c : E4) :
    ((A.filter (fun z => cfg z = c)).image (shadowLabel delta front)).card ≤ 5 ^ 4 := by
  have hsub : (A.filter (fun z => cfg z = c)).image (shadowLabel delta front) ⊆
      columnHalo 2 2 (wzDyadicCellIndex (delta / 2) (O.symm c)) := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    have hc : dist (front z) (O.symm c) ≤ delta := by
      rw [← O.dist_map, LinearIsometryEquiv.apply_symm_apply, dist_comm]
      simpa only [he] using hclose z hz
    apply Fintype.mem_piFinset.mpr
    intro v
    simp only [ite_self]
    apply floor_neighbor (by positivity) 2
    have hv : |front z v - O.symm c v| ≤ dist (front z) (O.symm c) := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (front z) (O.symm c) v
    norm_num
    linarith
  exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)

/-- All configured points above one actual shadow cell lie in a fixed ball.
Only their genuine output-scale separation is used in the packing step. -/
lemma forward_point_fiber {X : Type*} (A : Finset X) (delta : ℝ) (hd : 0 < delta)
    (O : E4 ≃ₗᵢ[ℝ] E4) (front cfg : X → E4)
    (hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ delta)
    (hsep : ∀ x ∈ A.image cfg, ∀ y ∈ A.image cfg, x ≠ y → delta ≤ dist x y)
    (q : Index) :
    ((A.filter (fun z => shadowLabel delta front z = q)).image cfg).card ≤ 33 ^ 4 := by
  apply separated_ball_card _ delta hd (O (cellCenter (delta / 2) q))
  · intro x hx y hy hxy
    exact hsep x (image_subset_image (filter_subset _ _) hx)
      y (image_subset_image (filter_subset _ _) hy) hxy
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    have hc : dist (front z) (cellCenter (delta / 2) q) ≤ delta / 2 := by
      apply (distance_of_coordinates _ _ (delta / 4) (by positivity) ?_).trans_eq (by ring)
      intro v
      have hv := NativeRelativeCoarseGeometry.cell_center_coordinate_error
        (by positivity : 0 < delta / 2) (front z) v
      change wzDyadicCellIndex (delta / 2) (front z) = q at he
      rw [he, abs_sub_comm] at hv
      exact hv.trans_eq (by ring)
    have hh := dist_triangle (cfg z) (O (front z)) (O (cellCenter (delta / 2) q))
    rw [O.dist_map] at hh
    have hzclose := hclose z hz
    linarith

/-- Retaining the phase component adds no menu cost: it is fixed in each
pair fiber. This keeps literal tube parents rather than forgetting them. -/
lemma pair_fiber_bound {X Q Y Z : Type*} [DecidableEq Q] [DecidableEq Y] [DecidableEq Z]
    (A : Finset X) (phase : X → Q) (f : X → Y) (g : X → Z) (K : ℕ)
    (h : ∀ y, ((A.filter (fun z => f z = y)).image g).card ≤ K) (v : Q × Y) :
    ((A.filter (fun z => (phase z, f z) = v)).image (fun z => (phase z, g z))).card ≤ K := by
  let B := A.filter (fun z => (phase z, f z) = v)
  have hB : B ⊆ A.filter (fun z => f z = v.2) := by
    intro z hz
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hz, congrArg Prod.snd he⟩
  have he : B.image (fun z => (phase z, g z)) = (B.image g).image (fun y => (v.1, y)) := by
    rw [image_image]
    apply image_congr
    intro z hz
    have hp := congrArg Prod.fst (mem_filter.mp hz).2
    exact Prod.ext hp rfl
  change (B.image (fun z => (phase z, g z))).card ≤ K
  rw [he]
  exact (card_image_le).trans ((card_le_card (image_subset_image hB)).trans (h v.2))

/-- The inverse shadow count requires no separation of configured points.
It therefore also applies when the configured mesh is finer than delta. -/
theorem inverse_image_bounds {X Q : Type*} [DecidableEq Q]
    (A : Finset X) (delta : ℝ) (hd : 0 < delta)
    (O : E4 ≃ₗᵢ[ℝ] E4) (phase : X → Q) (front cfg : X → E4)
    (hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ delta) :
    (A.image (shadowLabel delta front)).card ≤ 5 ^ 4 * (A.image cfg).card ∧
    (A.image (fun z => (phase z, shadowLabel delta front z))).card ≤
      5 ^ 4 * (A.image (fun z => (phase z, cfg z))).card := by
  have hi := inverse_point_fiber A delta hd O front cfg hclose
  refine ⟨image_card_le_mul_of_fiber_images _ _ _ _ (fun c _ => hi c),
    image_card_le_mul_of_fiber_images _ _ _ _ ?_⟩
  intro v _hv
  exact pair_fiber_bound A phase cfg (shadowLabel delta front) (5 ^ 4) hi v

/-- Two-way cardinality transfer for both point supports and actual
phase-point incidence images, with only fixed constants. -/
theorem image_bounds {X Q : Type*} [DecidableEq Q]
    (A : Finset X) (delta : ℝ) (hd : 0 < delta)
    (O : E4 ≃ₗᵢ[ℝ] E4) (phase : X → Q) (front cfg : X → E4)
    (hclose : ∀ z ∈ A, dist (cfg z) (O (front z)) ≤ delta)
    (hsep : ∀ x ∈ A.image cfg, ∀ y ∈ A.image cfg, x ≠ y → delta ≤ dist x y) :
    (A.image (shadowLabel delta front)).card ≤ 5 ^ 4 * (A.image cfg).card ∧
    (A.image cfg).card ≤ 33 ^ 4 * (A.image (shadowLabel delta front)).card ∧
    (A.image (fun z => (phase z, shadowLabel delta front z))).card ≤
      5 ^ 4 * (A.image (fun z => (phase z, cfg z))).card ∧
    (A.image (fun z => (phase z, cfg z))).card ≤
      33 ^ 4 * (A.image (fun z => (phase z, shadowLabel delta front z))).card := by
  have hi := inverse_point_fiber A delta hd O front cfg hclose
  have hf := forward_point_fiber A delta hd O front cfg hclose hsep
  refine ⟨image_card_le_mul_of_fiber_images _ _ _ _ (fun c _ => hi c),
    image_card_le_mul_of_fiber_images _ _ _ _ (fun q _ => hf q),
    image_card_le_mul_of_fiber_images _ _ _ _ ?_,
    image_card_le_mul_of_fiber_images _ _ _ _ ?_⟩
  · intro v _hv
    exact pair_fiber_bound A phase cfg (shadowLabel delta front) (5 ^ 4) hi v
  · intro v _hv
    exact pair_fiber_bound A phase (shadowLabel delta front) cfg (33 ^ 4) hf v

end NativeMatchedShadowConfiguredCounts
