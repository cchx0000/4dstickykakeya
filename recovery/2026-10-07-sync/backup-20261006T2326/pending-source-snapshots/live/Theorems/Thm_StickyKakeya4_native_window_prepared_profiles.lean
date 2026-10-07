import Theorems.Thm_StickyKakeya4_native_window_real_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowPreparedProfiles
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeQuotientGridCenters
open NativeWindowIntegerInterpolation NativeWindowRealInterpolation RealScalarADInterpolation
open FiniteVoronoiRealADCoarsening

/-- Read the integer population from a prepared window's actual metric
AD statement. The center is the literal image of the same original point. -/
theorem integer_profile_of_AD {k l : ℕ} (S : Finset (XY k l)) (R : ℕ)
    {mesh K s : ℝ} (hmesh : 0 < mesh) (z : XY k l) (hz : z∈S)
    (H : ADBounds (points S R mesh z) mesh K s)
    (n : ℕ) (hn : 1 ≤ n) (hradius : mesh*(n:ℝ) ≤ 1) :
    (n:ℝ)^s/K ≤ count S R z n ∧ count S R z n ≤ K*(n:ℝ)^s := by
  have ha : center mesh (gridDiv R z.2.2)∈points S R mesh z :=
    mem_image.mpr ⟨gridDiv R z.2.2,anchor_mem S R z hz,rfl⟩
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmin : mesh ≤ mesh*(n:ℝ) := le_mul_of_one_le_right hmesh.le hnr
  have hh := H _ ha (mesh*(n:ℝ)) hmin hradius
  change (mesh*(n:ℝ)/mesh)^s/K ≤
      ballCount (points S R mesh z) (center mesh (gridDiv R z.2.2)) (mesh*(n:ℝ)) ∧
    ballCount (points S R mesh z) (center mesh (gridDiv R z.2.2)) (mesh*(n:ℝ)) ≤
      K*(mesh*(n:ℝ)/mesh)^s at hh
  rw [ball_count_eq S R hmesh z n] at hh
  have hcancel : mesh*(n:ℝ)/mesh = (n:ℝ) := by field_simp
  simpa only [hcancel] using hh

/-- Genuine fine-descendant and coarse-ancestor AD statements generate
all interpolation tests internally. The ancestor's separately proved
global quotient count supplies the large-radius bound. No child-window
retention fraction or intermediate-window population is assumed. -/
theorem AD_from_prepared_profiles {k l : ℕ} (S : Finset (XY k l))
    (R Ds Db N : ℕ) (hDs : 0 < Ds) (hDb : 0 < Db) (hN : 1 ≤ N)
    {muFine muTarget muBig Kfine Kbig G s : ℝ}
    (hFine : 0 < muFine) (hKfine : 0 < Kfine) (hKbig : 0 < Kbig)
    (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hFineMesh : muFine*(Ds:ℝ)=muTarget)
    (hBigMesh : muTarget*(Db:ℝ)=muBig)
    (hscale : muBig*(N:ℝ)=1/2)
    (Hfine : ∀z∈S,ADBounds (points S R muFine z) muFine Kfine s)
    (Hbig : ∀z∈S,ADBounds (points S ((R*Ds)*Db) muBig z) muBig Kbig s)
    (Hglobal : ∀z∈S,((atPoint S ((R*Ds)*Db) z).card:ℝ) ≤ G*(N:ℝ)^s)
    (anchor : XY k l) :
    ADBounds (points S (R*Ds) muTarget anchor) muTarget
      (NativeHalfScaleInterpolation.constant ((1/Kfine)/(Ds:ℝ)^l)
        (upperConstant l Db Kbig s) ((Db:ℝ)^l*G) s) s := by
  have hDsr : (0:ℝ) < Ds := by exact_mod_cast hDs
  have hDbr : (0:ℝ) < Db := by exact_mod_cast hDb
  have hTarget : 0 < muTarget := by rw [←hFineMesh]; positivity
  have hBig : 0 < muBig := by rw [←hBigMesh]; positivity
  have hTargetScale : muTarget*((Db*N:ℕ):ℝ)=1/2 := by
    rw [Nat.cast_mul,←mul_assoc,hBigMesh]
    exact hscale
  have hFineScale : muFine*((Ds*(Db*N):ℕ):ℝ)=1/2 := by
    rw [Nat.cast_mul,←mul_assoc,hFineMesh]
    exact hTargetScale
  apply AD_from_brackets S R Ds Db N hDs hDb hN hTarget (by positivity) hKbig.le hG hs hTargetScale
  · intro z hz n hn hnmax
    have htest : muFine*(n:ℝ) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnmax) hFine.le
      rw [hFineScale] at hh
      linarith only [hh]
    have hh := (integer_profile_of_AD S R hFine z hz (Hfine z hz) n hn htest).1
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh
  · intro z hz n hn hnN
    have htest : muBig*(n:ℝ) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) hBig.le
      rw [hscale] at hh
      linarith only [hh]
    exact (integer_profile_of_AD S ((R*Ds)*Db) hBig z hz (Hbig z hz) n hn htest).2
  · exact Hglobal

end NativeWindowPreparedProfiles
