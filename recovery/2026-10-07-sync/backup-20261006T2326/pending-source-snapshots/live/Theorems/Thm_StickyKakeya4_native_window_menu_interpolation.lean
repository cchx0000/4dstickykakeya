import Theorems.Thm_StickyKakeya4_native_window_prepared_profiles
import Theorems.Thm_StickyKakeya4_native_window_depth_brackets
import Theorems.Thm_StickyKakeya4_native_fixed_horizontal_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeWindowMenuInterpolation
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowIntegerInterpolation NativeWindowPreparedProfiles NativeWindowDepthBrackets
open NativeWindowQuotientTransport NativeReferenceXYGridPoints NativeSquaredGrainQueries
open FiniteVoronoiRealADCoarsening

/-- Read the finite prepared profiles at the actual two bracketing depths.
The intermediate window is the original source's own window, with its own
original point anchors. The two ratios are bounded by the fixed menu gap. -/
theorem middle_window_AD {k l J : ℕ} (S : Finset (XY k l))
    (m : ℕ) (hm : 6 ≤ m) (hJ : 0 < J) {K G s : ℝ}
    (hK : 0 < K) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (H : ∀i : Fin (J+1),∀z∈S,
      ADBounds (points S (factor m (NativeFixedHorizontalMenu.depths J m i))
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) z)
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) K s)
    (Hglobal : ∀i : Fin (J+1),∀z∈S,
      ((atPoint S (factor m (NativeFixedHorizontalMenu.depths J m i)) z).card:ℝ) ≤
        G*(windowHalfWidth m (NativeFixedHorizontalMenu.depths J m i):ℝ)^s)
    (f : ℕ) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) (anchor : XY k l) (hanchor : anchor∈S) :
    ∃lo hi : Fin (J+1),
      let fl := NativeFixedHorizontalMenu.depths J m lo
      let fh := NativeFixedHorizontalMenu.depths J m hi
      let Ds := (2:ℕ)^(fh-f)
      let Db := (2:ℕ)^(f-fl)
      fl ≤ f ∧ f ≤ fh ∧
      Ds ≤ 2^((phaseDepth m-m)/J+1) ∧ Db ≤ 2^((phaseDepth m-m)/J+1) ∧
      ADBounds (points S (factor m f) (mu m*(factor m f:ℝ)) anchor)
        (mu m*(factor m f:ℝ))
        (NativeHalfScaleInterpolation.constant ((1/K)/(Ds:ℝ)^l)
          (upperConstant l Db K s) ((Db:ℝ)^l*G) s) s ∧
      ((atPoint S (factor m f) anchor).card:ℝ) ≤
        (Db:ℝ)^l*G*(windowHalfWidth m fl:ℝ)^s := by
  obtain ⟨lo,hi,hlo,hhi,hgaplo,hgaphi⟩ := bracket_depth J m (phaseDepth m)
    ((phaseDepth m-m)/J+1) (NativeFixedHorizontalMenu.depths J m)
    (NativeFixedHorizontalMenu.depths_zero J m)
    (NativeFixedHorizontalMenu.depths_last J m hJ hm)
    (NativeFixedHorizontalMenu.depths_gap J m hJ) f hmf hfb
  let fl := NativeFixedHorizontalMenu.depths J m lo
  let fh := NativeFixedHorizontalMenu.depths J m hi
  let Ds := (2:ℕ)^(fh-f)
  let Db := (2:ℕ)^(f-fl)
  have hfl := NativeFixedHorizontalMenu.depths_bounds J m hm lo
  have hfh := NativeFixedHorizontalMenu.depths_bounds J m hm hi
  have hfactors := dyadic_factors (phaseDepth m) fl f fh ((phaseDepth m-m)/J+1)
    hlo hhi hfh.2 hgaplo hgaphi
  have hsmall : factor m fh*Ds=factor m f := hfactors.1
  have hbig : factor m f*Db=factor m fl := hfactors.2.1
  have hboth : (factor m fh*Ds)*Db=factor m fl := by rw [hsmall,hbig]
  refine ⟨lo,hi,hlo,hhi,hfactors.2.2.1,hfactors.2.2.2,?_⟩
  have hfineMesh : (mu m*(factor m fh:ℝ))*(Ds:ℝ)=mu m*(factor m f:ℝ) := by
    rw [mul_assoc,←Nat.cast_mul,hsmall]
  have hbigMesh : (mu m*(factor m f:ℝ))*(Db:ℝ)=mu m*(factor m fl:ℝ) := by
    rw [mul_assoc,←Nat.cast_mul,hbig]
  have hh := AD_from_prepared_profiles S (factor m fh) Ds Db (windowHalfWidth m fl)
    (by dsimp [Ds]; positivity) (by dsimp [Db]; positivity)
    (by unfold windowHalfWidth; positivity)
    (mul_pos (mu_pos m) (by unfold factor; positivity)) hK hK hG hs hfineMesh hbigMesh
    (window_mesh_halfWidth m fl hm hfl.1 hfl.2) (H hi)
    (by simpa only [hboth] using H lo)
    (by simpa only [hboth] using Hglobal lo) anchor
  constructor
  · simpa only [hsmall] using hh
  · have htransfer : ((atPoint S (factor m f) anchor).card:ℝ) ≤
        (Db:ℝ)^l*(atPoint S (factor m fl) anchor).card := by
      have hh := card_transfer S (factor m f) Db (by dsimp [Db]; positivity) anchor
      rw [hbig] at hh
      exact_mod_cast hh
    calc
      _ ≤ _ := htransfer
      _ ≤ (Db:ℝ)^l*(G*(windowHalfWidth m fl:ℝ)^s) :=
        mul_le_mul_of_nonneg_left (Hglobal lo anchor hanchor) (by positivity)
      _ = _ := by ring

end NativeWindowMenuInterpolation
