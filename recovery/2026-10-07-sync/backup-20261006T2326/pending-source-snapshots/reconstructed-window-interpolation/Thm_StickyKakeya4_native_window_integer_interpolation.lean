import Theorems.Thm_StickyKakeya4_native_window_nesting
import Theorems.Thm_StickyKakeya4_native_half_scale_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

noncomputable section
namespace NativeWindowIntegerInterpolation
open Classical Finset NativeWindowNesting NativeWindowXYLabels
open NativeQuotientLatticeTransport GridQuotientAD

def count {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) (n : ℕ) : ℝ :=
  ((atPoint S R z).filter (fun y => y∈box (gridDiv R z.2.2) n)).card

lemma count_nonneg {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) (n : ℕ) :
    0 ≤ count S R z n := Nat.cast_nonneg _

lemma count_ambient {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) (n : ℕ) :
    count S R z n ≤ ((2*n+1:ℕ):ℝ)^l := by
  have hh : ((atPoint S R z).filter (fun y => y∈box (gridDiv R z.2.2) n)).card ≤
      (box (gridDiv R z.2.2) n).card :=
    card_le_card (fun _ h => (mem_filter.mp h).2)
  rw [box_card] at hh
  exact_mod_cast hh

/-- A single finer window containing the same actual source point supplies
the lower bound. Its population need not be a fixed fraction of its parent. -/
theorem lower_from_descendant {k l : ℕ} (S : Finset (XY k l))
    (R D N : ℕ) (hD : 0 < D) (z : XY k l) {c s : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (H : ∀n:ℕ,1 ≤ n → n ≤ D*N → c*(n:ℝ)^s ≤ count S R z n)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    (c/(D:ℝ)^l)*(n:ℝ)^s ≤ count S (R*D) z n := by
  have hDp : (0:ℝ)<D := by exact_mod_cast hD
  have hnD : n ≤ D*n := Nat.le_mul_of_pos_left n hD
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg n)
    (show (n:ℝ) ≤ ((D*n:ℕ):ℝ) by exact_mod_cast hnD) hs
  have hlo := (mul_le_mul_of_nonneg_left hp hc).trans
    (H (D*n) (hn.trans hnD) (Nat.mul_le_mul_left D hnN))
  have htransfer : count S R z (D*n) ≤ (D:ℝ)^l*count S (R*D) z n := by
    exact_mod_cast local_card_transfer S R D (D*n) n hD le_rfl z
  have hh := hlo.trans htransfer
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (pow_pos hDp l)).mpr (by simpa only [mul_comm] using hh)

def upperConstant (l D : ℕ) (U s : ℝ) : ℝ :=
  max ((3*(D:ℝ))^l) ((D:ℝ)^l*U*(2:ℝ)^s)

lemma upperConstant_nonneg (l D : ℕ) (U s : ℝ) : 0 ≤ upperConstant l D U s :=
  (by positivity : (0:ℝ) ≤ (3*(D:ℝ))^l).trans (le_max_left _ _)

/-- A coarser actual ancestor controls every integer radius. Below the
ancestor mesh the lattice bound is used explicitly. -/
theorem upper_from_ancestor {k l : ℕ} (S : Finset (XY k l))
    (R D N : ℕ) (hD : 0 < D) (z : XY k l) {U s : ℝ}
    (hU : 0 ≤ U) (hs : 0 ≤ s)
    (H : ∀n:ℕ,1 ≤ n → n ≤ N → count S (R*D) z n ≤ U*(n:ℝ)^s)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ D*N) :
    count S R z n ≤ upperConstant l D U s*(n:ℝ)^s := by
  have hDp : (0:ℝ)<D := by exact_mod_cast hD
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpowone : (1:ℝ) ≤ (n:ℝ)^s := Real.one_le_rpow hnp hs
  by_cases hnD : n < D
  · have hcell : (2*(n:ℝ)+1) ≤ 3*(D:ℝ) := by
      have hh : (n:ℝ)<D := by exact_mod_cast hnD
      linarith
    have hamb := count_ambient S R z n
    push_cast at hamb
    have hsmall := hamb.trans (pow_le_pow_left₀ (by positivity) hcell l)
    have hC := upperConstant_nonneg l D U s
    exact (hsmall.trans (le_max_left _ _)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowone hC)
  · have hDn : D ≤ n := Nat.le_of_not_gt hnD
    let V : ℕ := ⌈(n:ℝ)/(D:ℝ)⌉₊
    have hratio : (1:ℝ) ≤ (n:ℝ)/(D:ℝ) :=
      (le_div_iff₀ hDp).mpr (by exact_mod_cast hDn)
    have hV : 1 ≤ V := Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hratio)
    have hVN : V ≤ N := Nat.ceil_le.mpr ((div_le_iff₀ hDp).mpr (by exact_mod_cast hnN))
    have hnV : n ≤ D*V := by
      have hh : (n:ℝ)/(D:ℝ) ≤ (V:ℝ) := Nat.le_ceil _
      have hh' := (div_le_iff₀ hDp).mp hh
      exact_mod_cast (by simpa only [mul_comm] using hh')
    have hVtwo : (V:ℝ) ≤ 2*(n:ℝ) := by
      have hh : (V:ℝ)<(n:ℝ)/(D:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
      have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
      have hdiv : (n:ℝ)/(D:ℝ) ≤ (n:ℝ) := div_le_self (by positivity) hD1
      linarith
    have htransfer : count S R z n ≤ (D:ℝ)^l*count S (R*D) z V := by
      exact_mod_cast local_card_transfer S R D n V hD hnV z
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg V) hVtwo hs
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp
    calc
      count S R z n ≤ (D:ℝ)^l*(U*(V:ℝ)^s) :=
        htransfer.trans (mul_le_mul_of_nonneg_left (H V hV hVN) (by positivity))
      _ ≤ (D:ℝ)^l*(U*((2:ℝ)^s*(n:ℝ)^s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hU) (by positivity)
      _ = ((D:ℝ)^l*U*(2:ℝ)^s)*(n:ℝ)^s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The global upper uses the proved global ancestor count rather than
assuming that a unit ball contains the whole quotient. -/
theorem global_from_ancestor {k l : ℕ} (S : Finset (XY k l))
    (R D N : ℕ) (hD : 0 < D) (z : XY k l) {G s : ℝ}
    (hG : 0 ≤ G) (hs : 0 ≤ s)
    (H : ((atPoint S (R*D) z).card:ℝ) ≤ G*(N:ℝ)^s) :
    ((atPoint S R z).card:ℝ) ≤ ((D:ℝ)^l*G)*((D*N:ℕ):ℝ)^s := by
  have hh : ((atPoint S R z).card:ℝ) ≤ (D:ℝ)^l*((atPoint S (R*D) z).card:ℝ) := by
    exact_mod_cast card_transfer S R D hD z
  have hND : N ≤ D*N := Nat.le_mul_of_pos_left N hD
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg N)
    (show (N:ℝ) ≤ ((D*N:ℕ):ℝ) by exact_mod_cast hND) hs
  calc
    _ ≤ (D:ℝ)^l*(G*(N:ℝ)^s) := hh.trans (mul_le_mul_of_nonneg_left H (by positivity))
    _ ≤ (D:ℝ)^l*(G*((D*N:ℕ):ℝ)^s) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hG) (by positivity)
    _ = _ := by ring

end NativeWindowIntegerInterpolation
