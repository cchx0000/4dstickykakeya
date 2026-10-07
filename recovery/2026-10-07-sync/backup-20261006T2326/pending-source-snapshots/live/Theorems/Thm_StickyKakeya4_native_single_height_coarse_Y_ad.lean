/- UNVERIFIED finest-only coarse-Y transfer. It does not assert any
larger time-window regularity. All points remain images of the same set. -/
import Theorems.Thm_StickyKakeya4_native_configured_Y_quarter_square
import Theorems.Thm_StickyKakeya4_native_grid_center_coarsening
import Theorems.Thm_StickyKakeya4_native_grid_center_contraction
import Theorems.Thm_StickyKakeya4_native_grid_support_population
import Theorems.Thm_StickyKakeya4_native_quotient_lattice_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeSingleHeightCoarseYAD
open Classical Finset FiniteVoronoiRealADCoarsening NativeGridSupportPopulation
open NativeGridCenterCoarsening NativeGridCenterContraction NativeConfiguredYQuarterSquare
open NativeLiteralGridOverlap NativeQuotientLatticeTransport

/-- Quadratic fine-Y cost, with each fixed geometric factor explicit. -/
def coarseConstant (K s : ℝ) : ℝ := 81*(169*K)^2*12^s

def finalConstant (K s : ℝ) : ℝ := 512^s*169*coarseConstant K s

/-- Fine AD, actual bounded fine labels, and literal integer division
produce AD on the contracted coarse centers. Both global counts are proved
from bounded AD, so no test is made beyond the source's radius-one range. -/
theorem coarse_contracted_AD (P : Finset (Fin 2 → ℤ))
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (R : ℕ) (hR : 0 < R) (hbase : mu*(R:ℝ) ≤ 1)
    (hsupport : ∀p∈P,∀j : Fin 2,|mu*(p j:ℝ)| ≤ 1)
    (H : ADBounds (P.image (center mu)) mu K s) :
    ADBounds ((P.image (divide R)).image (center (mu*(R:ℝ)/512)))
      (mu*(R:ℝ)/512) (finalConstant K s) s := by
  have hR1 : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hmu1 : mu ≤ 1 := (le_mul_of_one_le_right hmu.le hR1).trans hbase
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hbox : ∀x∈P.image (center mu),dist x 0 ≤ 2 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    apply (dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 2)).mpr
    intro j
    rw [Real.dist_eq,Pi.zero_apply,sub_zero]
    have he : center mu p j=mu*(p j:ℝ)+mu/2 := by dsimp only [center]; ring
    rw [he]
    have ha := abs_add_le (mu*(p j:ℝ)) (mu/2)
    rw [abs_of_pos (half_pos hmu)] at ha
    linarith only [ha,hsupport p hp j,hmu1]
  have hg := global_card_of_bounded_AD (P.image (center mu)) hmu hmu1 hKp H hbox
  rw [card_image_of_injective _ (NativeLiteralGridOverlap.center_injective hmu)] at hg
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hg
  have hK0 : 1 ≤ 169*K := by nlinarith only [hK]
  have HK : ADBounds (P.image (center mu)) mu (169*K) s := by
    intro x hx r hr hr1
    have hh := H x hx r hr hr1
    have hKK : K ≤ 169*K := by nlinarith only [hK]
    have hrpos : 0 < r := hmu.trans_le hr
    have hp : 0 ≤ (r/mu)^s := Real.rpow_nonneg (by positivity) _
    exact ⟨(div_le_div_of_nonneg_left hp hKp hKK).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right hKK hp)⟩
  have HC := coarsened_ADBounds P R hR hmu hK0 hs HK hg
  change ADBounds ((P.image (divide R)).image (center (mu*(R:ℝ))))
    (mu*(R:ℝ)) (coarseConstant K s) s at HC
  have hbpos : 0 < mu*(R:ℝ) := mul_pos hmu (by exact_mod_cast hR)
  have hcoarsepos : 0 < coarseConstant K s := by unfold coarseConstant; positivity
  have hboxCoarse : ∀x∈(P.image (divide R)).image (center (mu*(R:ℝ))),dist x 0 ≤ 2 := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    apply (dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 2)).mpr
    intro j
    rw [Real.dist_eq,Pi.zero_apply,sub_zero]
    have hh := contracted_midpoint_bound hmu R hR hbase (p j) (hsupport p hp j)
    have he : (mu*(R:ℝ)/512)*(((p j/(R:ℤ):ℤ):ℝ)+1/2)=
        center (mu*(R:ℝ)) (divide R p) j/512 := by dsimp only [center,divide]; ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)] at hh
    linarith only [hh]
  have hgc := global_card_of_bounded_AD _ hbpos hbase hcoarsepos HC hboxCoarse
  rw [card_image_of_injective _ (NativeLiteralGridOverlap.center_injective hbpos)] at hgc
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hgc
  have Hfinal := contracted_grid_AD (P.image (divide R)) hbpos hbase
    (by norm_num : (1:ℝ) ≤ 512) hcoarsepos hs HC hgc
  have hmax : max (coarseConstant K s) (169*coarseConstant K s)=169*coarseConstant K s :=
    max_eq_right (by linarith only [hcoarsepos])
  rw [hmax] at Hfinal
  simpa only [finalConstant,mul_assoc] using Hfinal

/-- Exact single-old-height readback for the whole current incidence set.
The new normal key is literal integer division, and the old height witness
is retained explicitly instead of identifying its real time with a bin. -/
theorem key_image_eq_one_height {Ω : Type*} {k : ℕ} (T : Finset Ω)
    (labels : Ω → ℤ × ((Fin k → ℤ) × (Fin 2 → ℤ)))
    (key : Ω → ℤ × (Fin 2 → ℤ)) (R : ℕ)
    (Hkey : ∀z∈T,key z=((labels z).1/((8*R:ℕ):ℤ),divide R (labels z).2.2))
    (Hsingle : ∀z∈T,∀w∈T,(labels z).1/((8*R:ℕ):ℤ)=(labels w).1/((8*R:ℕ):ℤ) →
      (labels z).1=(labels w).1)
    (z : Ω) (hz : z∈T) :
    (T.filter (fun w => (key w).1=(key z).1)).image (fun w => (key w).2)=
      ((productSlice (T.image labels) (labels z).1).image Prod.snd).image (divide R) := by
  ext y
  simp only [mem_image,mem_filter,productSlice]
  constructor
  · rintro ⟨w,⟨hw,hheight⟩,hy⟩
    rw [Hkey w hw,Hkey z hz] at hheight
    have hold := Hsingle w hw z hz hheight
    refine ⟨(labels w).2.2,⟨(labels w).2,⟨labels w,⟨⟨w,hw,rfl⟩,hold⟩,rfl⟩,rfl⟩,?_⟩
    simpa only [Hkey w hw] using hy
  · rintro ⟨q,⟨xy,⟨w,⟨⟨x,hx,rfl⟩,hheight⟩,rfl⟩,rfl⟩,rfl⟩
    refine ⟨x,⟨hx,?_⟩,?_⟩
    · rw [Hkey x hx,Hkey z hz,hheight]
    · rw [Hkey x hx]

end NativeSingleHeightCoarseYAD
