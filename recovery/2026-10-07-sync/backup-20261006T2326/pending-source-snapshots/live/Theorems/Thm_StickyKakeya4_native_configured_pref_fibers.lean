import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_caps
import Theorems.Thm_StickyKakeya4_native_configured_phase_fibers
import Theorems.Thm_StickyKakeya4_native_actual_configured_point
import Theorems.Thm_StickyKakeya4_native_configured_original_cell_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeConfiguredPrefFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeAnisotropicShortRowGeometry
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open scoped Matrix.Norms.Elementwise

/-- The actual reference grid has horizontal width8mu and height widthmu/8.
This cost concerns distinct reference labels, not original microcell indices. -/
def pointCost (R : ℕ) : ℕ := (8*R+1)^3 * (416*R+1)

theorem pref_halo_of_distance {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (R : ℕ) (k l : Index)
    (hd : dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 26*(mu m*(R:ℝ))) :
    pref D a m p k ∈ columnHalo (4*R) (208*R) (pref D a m p l) := by
  have hmu := mu_pos m
  have hc (j : Fin 4) :
      |oldPoint D a m p k j-oldPoint D a m p l j| ≤ 26*(mu m*(R:ℝ)) := by
    exact (show |oldPoint D a m p k j-oldPoint D a m p l j| ≤
      dist (oldPoint D a m p k) (oldPoint D a m p l) by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le
          (oldPoint D a m p k) (oldPoint D a m p l) j).trans hd
  apply Fintype.mem_piFinset.mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [show (Fin.last 3 : Fin 4)=3 by rfl, if_true]
    rw [pref_height_floor, pref_height_floor, heightMesh_eq]
    apply floor_neighbor (by positivity) (208*R)
    push_cast
    nlinarith only [hc 3]
  · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
    simp only [if_neg hj]
    rw [pref_spatial, pref_spatial, prefMesh_eq m hm]
    apply floor_neighbor (by positivity) (4*R)
    push_cast
    have hR : (0:ℝ) ≤ R := Nat.cast_nonneg R
    nlinarith only [hc j.castSucc, mul_nonneg hmu.le hR]

/-- A concrete mixed-grid capacity from a physical diameter bound. The
configured-point producer supplies this bound before the image comparison. -/
theorem pref_image_card_of_diameter {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (hm : 6 ≤ m) (p : Parent) (R : ℕ) (S : Finset Index)
    (hd : ∀ k ∈ S, ∀ l ∈ S,
      dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 26*(mu m*(R:ℝ))) :
    (S.image (pref D a m p)).card ≤ pointCost R := by
  by_cases hn : S.Nonempty
  · obtain ⟨l, hl⟩ := hn
    have hs : S.image (pref D a m p) ⊆ columnHalo (4*R) (208*R) (pref D a m p l) := by
      intro v hv
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
      exact pref_halo_of_distance D a m hm p R k l (hd k hk l hl)
    exact (card_le_card hs).trans_eq (by rw [columnHalo_card]; unfold pointCost; ring)
  · rw [not_nonempty_iff_eq_empty.mp hn, image_empty, card_empty]
    exact Nat.zero_le _

/-- The displayed polynomial is paid only at the base-to-reference ratio. -/
theorem pointCost_le (R : ℕ) (hR : 0 < R) : pointCost R ≤ (9^3*417)*R^4 := by
  have h1 : 8*R+1 ≤ 9*R := by omega
  have h2 : 416*R+1 ≤ 417*R := by omega
  calc
    _ ≤ (9*R)^3*(417*R) := Nat.mul_le_mul (Nat.pow_le_pow_left h1 3) h2
    _ = _ := by ring

/-- The actual squared old phase and second-source output phase have at
most six powers of the configured/reference ratio. -/
theorem squared_phase_cost_le (m u : ℕ) :
    512^3 * (2^((2*m-6)-(m+(u+12))))^6 ≤ 512^3 * (2^(m-u))^6 := by
  have hg : (2*m-6)-(m+(u+12)) ≤ m-u := by omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hg) 6)

/-- The actual configured realization factors through the original pxy
label. Thus its forward capacity has NO base/reference power loss. -/
theorem configured_forward_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1/4:ℝ)) (R : ℕ) (S : Finset Index) (q : Index) :
    ((S.filter (fun k => pref D a m p k=q)).image
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R)).card ≤ 1201^3 := by
  rw [NativeActualConfiguredPoint.point_factorization, ← image_image]
  apply card_image_le.trans
  cases s with
  | oneTwo =>
      exact NativeReferenceXYGridCaps.fine_forward_capacity h m 2 hm p i hi P hP
        (by norm_num) (by norm_num) hd F hF S q
  | twoOne =>
      exact NativeReferenceXYGridCaps.fine_forward_capacity h m 3 hm p i hi P hP
        (by norm_num) (by norm_num) hd F hF S q

/-- Equal ACTUAL configured points occupy at most the displayed number of
old reference labels. The physical diameter is derived internally from
the original rounding and the unified configured-point reader. -/
theorem configured_pref_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀ t, ‖Fcfg t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (hbase : rho m ≤ mu m*(R:ℝ)) (S : Finset Index) (q : E4) :
    ((S.filter (fun k => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R k=q)).image
      (pref D a m p)).card ≤ pointCost R := by
  have hFe (t : ℤ) (v : Fin (normalDim s)) (w : Fin (tangentDim s)) : |F t v w| ≤ 1/4 := by
    simpa only [Real.norm_eq_abs] using
      (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) v w
  have hCe (t : ℤ) (v : Fin (normalDim s)) (w : Fin (tangentDim s)) : |Fcfg t v w| ≤ 1/4 := by
    simpa only [Real.norm_eq_abs] using
      (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hCfg t) v w
  have hscale : 64*mu m ≤ mu m*(R:ℝ) := by
    have he : 64*mu m=rho m := by unfold mu; ring
    rwa [he]
  apply pref_image_card_of_diameter D a m hm p R
  intro k hk l hl
  apply NativeConfiguredOriginalCellSelection.same_cell_old_dist
    (NativePackedFrameIsometry.frame s P hP hd) 0
    (by have hmu := mu_pos m; positivity) hscale
    (oldPoint D a m p k) (oldPoint D a m p l)
    (rawPoint D a m p k) (rawPoint D a m p l)
    (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R k)
    (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R l)
    (physical_rounding h m hm p i hi k) (physical_rounding h m hm p i hi l)
  · simpa only [sub_zero] using
      NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hFe hCe R hR k hbase
  · simpa only [sub_zero] using
      NativeActualConfiguredPoint.point_distance D a m hm p s P hP hd F Fcfg hFe hCe R hR l hbase
  · rw [(mem_filter.mp hk).2, (mem_filter.mp hl).2]

/-- New geometric point support is counted after deduplication, with the
actual forward capacity. It is not identified with original point labels. -/
theorem configured_point_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1/4:ℝ)) (R : ℕ) (S : Finset Index) :
    (S.image (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R)).card ≤
      1201^3*(S.image (pref D a m p)).card := by
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images S
    (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R) (pref D a m p) (1201^3:ℕ)
    (fun q _ => Nat.cast_le.mpr (configured_forward_capacity h m hm p i hi s P hP hd F Fcfg hF R S q))
  exact_mod_cast hh

end NativeConfiguredPrefFibers
