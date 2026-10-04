import Theorems.Thm_StickyKakeya4_original_common_scalar_fibers
import Theorems.Thm_StickyKakeya4_vector_graph_weighted_rounding
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open Finset
open scoped Pointwise
noncomputable section
open Classical
namespace OriginalScalarLineCover
open OriginalCommonScalarFibers VectorGraphCollisionEnergy PlanarShiftedNearEnergy
open TwoTubePathCollisionCount

/-- Literal outputs from original A points and original common scalar labels. -/
def lineOutput (A : Finset (ℝ × ℝ)) (D : Finset ℝ) (v : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  (A ×ˢ D).image (fun e => e.1+e.2 • v)

/-- Sharing the same original c gives exact vector cancellation. There is no
representative or rounded-value substitution in this containment. -/
theorem common_lineOutput_subset (A : Finset (ℝ × ℝ)) (C : Finset ℝ)
    (F : Finset ((ℝ × ℝ) × ℝ)) (b b' : ℝ × ℝ) :
    lineOutput A (commonFiber F C b b') (b-b') ⊆ A+F.image productValue-F.image productValue := by
  intro x hx
  obtain ⟨⟨a,c⟩,hac,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha,hc⟩ := Finset.mem_product.mp hac
  obtain ⟨_,hbc,hb'c⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_sub.mpr ⟨a+productValue (b,c),
    Finset.mem_add.mpr ⟨a,ha,productValue (b,c),Finset.mem_image_of_mem _ hbc,rfl⟩,
    productValue (b',c),Finset.mem_image_of_mem _ hb'c,?_⟩
  change a+c • b-c • b'=a+c • (b-b')
  rw [smul_sub]
  abel

/-- The actual Eq169 cover controls every common-C line output. -/
theorem common_line_grid_cover (A : Finset (ℝ × ℝ)) (C : Finset ℝ)
    (F : Finset ((ℝ × ℝ) × ℝ)) (b b' : ℝ × ℝ) (eta : ℝ) :
    ((A ×ˢ commonFiber F C b b').image (fun e => roundPoint eta (e.1+e.2 • (b-b')))).card ≤
      ((A+F.image productValue-F.image productValue).image (roundPoint eta)).card := by
  have hh := Finset.card_le_card (Finset.image_subset_image (f := roundPoint eta) (common_lineOutput_subset A C F b b'))
  simpa only [lineOutput,Finset.image_image,Function.comp_def] using hh

/-- The retained A density turns an original-population output cover into
actual collision energy on A×D. This is derived by finite Cauchy on that set. -/
theorem line_cover_collision_energy (A : Finset (ℝ × ℝ)) (D : Finset ℝ)
    (v : ℝ × ℝ) {eta r Q N : ℝ} (hA : A.Nonempty) (hr : 0 < r) (hQ : 0 < Q)
    (hret : r*N ≤ A.card)
    (hcover : (((A ×ˢ D).image (fun e => roundPoint eta (e.1+e.2 • v))).card : ℝ) ≤ Q*N) :
    (r/Q)*A.card*(D.card : ℝ)^2 ≤
      ((collisions (A ×ˢ D) (fun e => roundPoint eta (e.1+e.2 • v))).card : ℝ) := by
  have hcover' : (((A ×ˢ D).image (fun e => roundPoint eta (e.1+e.2 • v))).card : ℝ) ≤
      (Q/r)*A.card := by
    have hN : N ≤ (A.card : ℝ)/r := (le_div_iff₀ hr).mpr (by nlinarith only [hret])
    calc
      _ ≤ Q*N := hcover
      _ ≤ Q*((A.card : ℝ)/r) := mul_le_mul_of_nonneg_left hN hQ.le
      _ = _ := by ring
  have hh := VectorGraphWeightedRounding.original_graph_cover_grid_energy A D (fun c => c • v)
    (A ×ˢ D) hA (show (0:ℝ) ≤ 1 by norm_num) (show 0 < Q/r by positivity)
    (by simp only [one_mul,Finset.card_product,Nat.cast_mul]; exact le_rfl) hcover'
  have hid : (1:ℝ)^2/(Q/r)=r/Q := by field_simp
  simpa only [hid] using hh

/-- Quantitative common-C mass is preserved in the actual line collision
energy; the source reference remains the unchanged original scalar carrier C. -/
theorem common_line_collision_energy (A : Finset (ℝ × ℝ)) (C : Finset ℝ)
    (F : Finset ((ℝ × ℝ) × ℝ)) (b b' : ℝ × ℝ)
    {eta r Q N q : ℝ} (hA : A.Nonempty) (hr : 0 < r) (hQ : 0 < Q) (hq : 0 ≤ q)
    (hret : r*N ≤ A.card)
    (hcommon : q*C.card ≤ (commonFiber F C b b').card)
    (hcover : (((A+F.image productValue-F.image productValue).image (roundPoint eta)).card : ℝ) ≤ Q*N) :
    (r*q^2/Q)*A.card*(C.card : ℝ)^2 ≤
      ((collisions (A ×ˢ commonFiber F C b b')
        (fun e => roundPoint eta (e.1+e.2 • (b-b')))).card : ℝ) := by
  have hc : (((A ×ˢ commonFiber F C b b').image
      (fun e => roundPoint eta (e.1+e.2 • (b-b')))).card : ℝ) ≤ Q*N :=
    (Nat.cast_le.mpr (common_line_grid_cover A C F b b' eta)).trans hcover
  have he := line_cover_collision_energy A (commonFiber F C b b') (b-b') hA hr hQ hret hc
  have hsq := pow_le_pow_left₀ (show 0 ≤ q*(C.card : ℝ) by positivity) hcommon 2
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (r/Q)*(A.card : ℝ) by positivity)
  calc
    _ = (r/Q)*A.card*(q*(C.card : ℝ))^2 := by ring
    _ ≤ _ := hm.trans he
end OriginalScalarLineCover
