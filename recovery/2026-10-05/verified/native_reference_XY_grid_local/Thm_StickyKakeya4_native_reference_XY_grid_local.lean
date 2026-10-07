import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridLocal
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeReferenceXYGridMetric NativeReferenceXYGridMenus NativeReferenceXYGridCaps
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeTranslatedGrainHeightOverlap
open NativeAnisotropicShortRowGeometry
open scoped Matrix.Norms.Elementwise

lemma floor_center_error {r : ℝ} (hr : 0 < r) (x : ℝ) :
    |x-r*((⌊x/r⌋:ℝ)+1/2)| ≤ r/2 := by
  have hlo := (le_div_iff₀ hr).mp (Int.floor_le (x/r))
  have hhi := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x/r))
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma grid_ball_pair {mu r x y c : ℝ} (hmu : 0 < mu)
    (hx : |mu*((⌊x/mu⌋:ℝ)+1/2)-c| ≤ r)
    (hy : |mu*((⌊y/mu⌋:ℝ)+1/2)-c| ≤ r) : |x-y| ≤ 2*r+mu := by
  have hxe := floor_center_error hmu x
  have hye := floor_center_error hmu y
  have hxc := abs_sub_le x (mu*((⌊x/mu⌋:ℝ)+1/2)) c
  have hyc := abs_sub_le y (mu*((⌊y/mu⌋:ℝ)+1/2)) c
  have hxy := abs_sub_le x c y
  rw [abs_sub_comm c y] at hxy
  linarith

/-- A true coordinate box around an arbitrary real XY center at one actual
translated height. Euclidean balls are contained in these boxes. -/
def inBox (m ell : ℕ) (t : ℤ) (cx : Fin (ell-1) → ℝ) (cy : Fin (4-ell) → ℝ)
    (r : ℝ) (z : XY ell) : Prop :=
  z.1=t ∧ (∀j,|mu m*((z.2.1 j:ℝ)+1/2)-cx j| ≤ r) ∧
    (∀j,|mu m*((z.2.2 j:ℝ)+1/2)-cy j| ≤ r)

/-- Inverse cover for an actual local XY box, including phase rounding.
At every dyadic scale R with r≤R*mu, only201^3 reference-coarse cells occur. -/
theorem local_inverse_cover {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (S : Finset Index) (t : ℤ)
    (cx : Fin (ell-1) → ℝ) (cy : Fin (4-ell) → ℝ) (r : ℝ) (hr : r ≤ (R:ℝ)*mu m) :
    (((S.filter (fun k => inBox m ell t cx cy r (pxy D a m ell p P hP hell hell4 hd F k))).image
      (fun k => coarseIndex R (pref D a m p k))).card) ≤ 201^3 := by
  let T := S.filter (fun k => inBox m ell t cx cy r (pxy D a m ell p P hP hell hell4 hd F k))
  by_cases hT : T.Nonempty
  · obtain ⟨l,hl⟩ := hT
    have hlb := (mem_filter.mp hl).2
    have hsub : T.image (fun k => coarseIndex R (pref D a m p k))⊆columnHalo 100 0 (coarseIndex R (pref D a m p l)) := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      have hkb := (mem_filter.mp hk).2
      have ht : translatedHeight D a m k=translatedHeight D a m l := hkb.1.trans hlb.1.symm
      have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
      have hRmu := mul_le_mul_of_nonneg_right hRr (mu_pos m).le
      have hX (j : Fin (ell-1)) : |tangentCoordinates P ell hd (rawPoint D a m p k) j-
          tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ 4*((R:ℝ)*mu m) := by
        have hh := grid_ball_pair (mu_pos m) (hkb.2.1 j) (hlb.2.1 j)
        change |tangentCoordinates P ell hd (rawPoint D a m p k) j-
          tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ 2*r+mu m at hh
        have hp := mu_pos m
        nlinarith only [hh,hr,hRmu,hp]
      have hY (j : Fin (4-ell)) :
          |quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j-
            quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j| ≤
              4*((R:ℝ)*mu m) := by
        have hh := grid_ball_pair (mu_pos m) (hkb.2.2 j) (hlb.2.2 j)
        change |quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j-
          quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j| ≤ 2*r+mu m at hh
        have hp := mu_pos m
        nlinarith only [hh,hr,hRmu,hp]
      have hB : 0 ≤ 4*((R:ℝ)*mu m) := mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (mu_pos m).le)
      have hd := old_dist_of_coordinate_bounds h m ell hm p i hi P hP hell hell4 hd F hF k l ht _ hB hX hY
      apply pref_neighbor_of_old_dist D a m hm p R hR k l ht
      have hp := mu_pos m
      nlinarith only [hd,hRmu,hp]
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · rw [not_nonempty_iff_eq_empty] at hT
    change (T.image _).card ≤ _
    simp only [hT,image_empty,card_empty,Nat.zero_le]

end NativeReferenceXYGridLocal
