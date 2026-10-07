import Theorems.Thm_StickyKakeya4_native_rounded_rotated_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeConfiguredOriginalCellSelection
open Classical Finset StickyKakeya4 NativeMatrixHeightWholePoint NativeRotatedCellSelection
open scoped BigOperators

/-- The old points are in first-parent coordinates, whereas configured
points are in the second, 1/512-contracted chart. The two genuine raw/old
errors and the configured-cell diameter give 26 times the old mesh. -/
theorem same_cell_old_dist (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {mu delta : ℝ} (hdelta : 0 < delta) (hscale : 64 * mu ≤ delta)
    (oldx oldy rawx rawy cfgx cfgy : E4)
    (hrawx : dist rawx oldx ≤ 128 * mu) (hrawy : dist rawy oldy ≤ 128 * mu)
    (hx : dist cfgx (O ((1 / 512 : ℝ) • rawx - c)) ≤ 3 * (delta / 512))
    (hy : dist cfgy (O ((1 / 512 : ℝ) • rawy - c)) ≤ 3 * (delta / 512))
    (hcell : wzDyadicCellIndex (delta / 64) cfgx = wzDyadicCellIndex (delta / 64) cfgy) :
    dist oldx oldy ≤ 26 * delta := by
  have hcellDist := same_grid_dist_le (by positivity : 0 < delta / 64) hcell
  have hcontract : dist ((1 / 512 : ℝ) • rawx) ((1 / 512 : ℝ) • rawy) = dist rawx rawy / 512 := by
    rw [dist_smul₀]
    norm_num
    ring
  have htri := dist_triangle4 (O ((1 / 512 : ℝ) • rawx - c)) cfgx cfgy
    (O ((1 / 512 : ℝ) • rawy - c))
  rw [LinearIsometryEquiv.dist_map, dist_sub_right, hcontract,
    dist_comm (O ((1 / 512 : ℝ) • rawx - c)) cfgx] at htri
  have hraw : dist rawx rawy ≤ 22 * delta := by
    nlinarith only [htri, hx, hy, hcellDist]
  have hold := dist_triangle4 oldx rawx rawy oldy
  have hxold : dist oldx rawx ≤ 128 * mu := by simpa only [dist_comm] using hrawx
  nlinarith only [hold, hxold, hrawy, hraw, hscale]

/-- The fixed residue53 comes from the proved unequal-grid displacement,
not from an assumed occupied-cell capacity. -/
theorem same_residue_original_cell (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {mu delta : ℝ} (hdelta : 0 < delta) (hscale : 64 * mu ≤ delta)
    (oldx oldy rawx rawy cfgx cfgy : E4)
    (hrawx : dist rawx oldx ≤ 128 * mu) (hrawy : dist rawy oldy ≤ 128 * mu)
    (hx : dist cfgx (O ((1 / 512 : ℝ) • rawx - c)) ≤ 3 * (delta / 512))
    (hy : dist cfgy (O ((1 / 512 : ℝ) • rawy - c)) ≤ 3 * (delta / 512))
    (hcell : wzDyadicCellIndex (delta / 64) cfgx = wzDyadicCellIndex (delta / 64) cfgy)
    (hcolor : SeparatedAlignmentPatches.color 53 (by norm_num) (wzDyadicCellIndex delta oldx) =
      SeparatedAlignmentPatches.color 53 (by norm_num) (wzDyadicCellIndex delta oldy)) :
    wzDyadicCellIndex delta oldx = wzDyadicCellIndex delta oldy := by
  have hd := same_cell_old_dist O c hdelta hscale oldx oldy rawx rawy cfgx cfgy hrawx hrawy hx hy hcell
  have hsup : dist (fun j : Fin 4 => oldx j) (fun j : Fin 4 => oldy j) ≤ 26 * delta := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro j
    exact (PiLp.dist_apply_le oldx oldy j).trans hd
  have hclose : dist (fun j : Fin 4 => oldx j) (fun j : Fin 4 => oldy j) < 27 * delta := by
    linarith only [hsup, hdelta]
  have hgap : 27 * delta ≤ ((53 : ℝ) - 1) * delta := by linarith only [hdelta]
  exact SeparatedAlignmentPatches.close_same_color_cell_eq delta (27 * delta) hdelta 53
    (by norm_num) hgap (fun j : Fin 4 => oldx j) (fun j : Fin 4 => oldy j) hcolor hclose

/-- Maximum original-weight residue selection in each actual configured
cell. All maps and source labels remain unchanged. -/
theorem select_one {A : Type*} (S : Finset A) (w : A → ℕ)
    (old raw configured : A → E4) (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4)
    {mu delta : ℝ} (hdelta : 0 < delta) (hscale : 64 * mu ≤ delta)
    (hraw : ∀ x ∈ S, dist (raw x) (old x) ≤ 128 * mu)
    (hround : ∀ x ∈ S, dist (configured x) (O ((1 / 512 : ℝ) • raw x - c)) ≤ 3 * (delta / 512)) :
    ∃ T ⊆ S, mass S w ≤ 53 ^ 4 * mass T w ∧
      ∀ x ∈ T, ∀ y ∈ T,
        wzDyadicCellIndex (delta / 64) (configured x) = wzDyadicCellIndex (delta / 64) (configured y) →
          wzDyadicCellIndex delta (old x) = wzDyadicCellIndex delta (old y) := by
  let : Nonempty (Fin 4 → Fin 53) := ⟨fun _ => 0⟩
  let paint := fun x => SeparatedAlignmentPatches.color 53 (by norm_num) (wzDyadicCellIndex delta (old x))
  let label := fun x => wzDyadicCellIndex (delta / 64) (configured x)
  obtain ⟨chi, hsub, _hlocal, hret, hcolor⟩ := select_color_per_cell S w label paint
  refine ⟨S.filter (fun x => paint x = chi (label x)), hsub, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hret
  · intro x hx y hy heq
    exact same_residue_original_cell O c hdelta hscale (old x) (old y) (raw x) (raw y)
      (configured x) (configured y) (hraw x (hsub hx)) (hraw y (hsub hy))
      (hround x (hsub hx)) (hround y (hsub hy)) heq (hcolor x hx y hy heq)

/-- Every later restriction inherits earlier configured-to-original cell
equalities, so a fixed finite menu costs exactly53^(4*#menu). -/
theorem select_finite_menu {A I : Type*} [DecidableEq I]
    (menu : Finset I) (S : Finset A) (w : A → ℕ) (old raw : A → E4)
    (configured : I → A → E4) (O : I → E4 ≃ₗᵢ[ℝ] E4) (c : I → E4)
    (mu : ℝ) (delta : I → ℝ) (hdelta : ∀ i, 0 < delta i) (hscale : ∀ i, 64 * mu ≤ delta i)
    (hraw : ∀ x ∈ S, dist (raw x) (old x) ≤ 128 * mu)
    (hround : ∀ i, ∀ x ∈ S, dist (configured i x) (O i ((1 / 512 : ℝ) • raw x - c i)) ≤
      3 * (delta i / 512)) :
    ∃ T ⊆ S, mass S w ≤ 53 ^ (4 * menu.card) * mass T w ∧
      ∀ i ∈ menu, ∀ x ∈ T, ∀ y ∈ T,
        wzDyadicCellIndex (delta i / 64) (configured i x) = wzDyadicCellIndex (delta i / 64) (configured i y) →
          wzDyadicCellIndex (delta i) (old x) = wzDyadicCellIndex (delta i) (old y) := by
  induction menu using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S, Subset.refl _, ?_, ?_⟩
      · simp
      · intro i hi
        simp at hi
  | @insert i menu hi ih =>
      obtain ⟨S1, hS1, hret1, hcell1⟩ := select_one S w old raw (configured i) (O i) (c i)
        (hdelta i) (hscale i) hraw (hround i)
      obtain ⟨T, hT, hret, hcell⟩ := ih S1 (fun x hx => hraw x (hS1 hx))
        (fun j x hx => hround j x (hS1 hx))
      refine ⟨T, hT.trans hS1, ?_, ?_⟩
      · calc
          mass S w ≤ 53 ^ 4 * mass S1 w := hret1
          _ ≤ 53 ^ 4 * (53 ^ (4 * menu.card) * mass T w) := Nat.mul_le_mul_left _ hret
          _ = 53 ^ (4 * (insert i menu).card) * mass T w := by
            rw [card_insert_of_notMem hi, ← mul_assoc, ← pow_add]
            congr 2
            omega
      · intro j hj x hx y hy heq
        rcases mem_insert.mp hj with rfl | hj
        · exact hcell1 x (hT hx) y (hT hy) heq
        · exact hcell j hj x hx y hy heq

/-- Whole-edge lift with actual original point-fiber weights. Each selected
point keeps every one of its original edges, and all finite-menu implications
hold on that same final edge subset. -/
theorem select_original_edges {E P : Type*} [DecidableEq P]
    (K : ℕ) (A : Finset E) (point : E → P) (old raw : P → E4)
    (configured : Fin K → P → E4) (O : Fin K → E4 ≃ₗᵢ[ℝ] E4) (c : Fin K → E4)
    (mu : ℝ) (delta : Fin K → ℝ) (hdelta : ∀ i, 0 < delta i) (hscale : ∀ i, 64 * mu ≤ delta i)
    (hraw : ∀ p ∈ A.image point, dist (raw p) (old p) ≤ 128 * mu)
    (hround : ∀ i, ∀ p ∈ A.image point,
      dist (configured i p) (O i ((1 / 512 : ℝ) • raw p - c i)) ≤ 3 * (delta i / 512)) :
    ∃ B ⊆ A.image point, let T := edgeLift A point B
      T ⊆ A ∧ A.card ≤ 53 ^ (4 * K) * T.card ∧
      (∀ p ∈ B, T.filter (fun x => point x = p) = A.filter (fun x => point x = p)) ∧
      ∀ i, ∀ x ∈ T, ∀ y ∈ T,
        wzDyadicCellIndex (delta i / 64) (configured i (point x)) =
          wzDyadicCellIndex (delta i / 64) (configured i (point y)) →
        wzDyadicCellIndex (delta i) (old (point x)) = wzDyadicCellIndex (delta i) (old (point y)) := by
  let w := fun p => (A.filter (fun x => point x = p)).card
  have hmass : mass (A.image point) w = A.card := (card_eq_sum_card_image point A).symm
  obtain ⟨B, hB, hret, hcell⟩ := select_finite_menu univ (A.image point) w old raw configured O c
    mu delta hdelta hscale hraw hround
  rw [hmass, ← edgeLift_card A point B] at hret
  refine ⟨B, hB, filter_subset _ _, by simpa using hret,
    fun p hp => edgeLift_fiber A point B p hp, ?_⟩
  intro i x hx y hy heq
  exact hcell i (mem_univ i) (point x) (mem_filter.mp hx).2 (point y) (mem_filter.mp hy).2 heq

end NativeConfiguredOriginalCellSelection
