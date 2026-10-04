import Theorems.Thm_StickyKakeya4_original_rounded_ruzsa_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalRoundedRingProduct
open OriginalRoundedRuzsaCover GKZGridCodePerturbation ActualRoundedAdditiveEnergy

def dilate (x : ℝ) (A : Finset ℝ) : Finset ℝ := A.image (fun a => x*a)

lemma dilate_sum (x : ℝ) (A B : Finset ℝ) :
    dilate x (A+B)=dilate x A+dilate x B := by
  ext z
  constructor
  · intro hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hw
    exact Finset.mem_add.mpr ⟨x*a,Finset.mem_image_of_mem _ ha,
      x*b,Finset.mem_image_of_mem _ hb,(mul_add x a b).symm⟩
  · intro hz
    obtain ⟨p,hp,q,hq,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨a+b,Finset.mem_add.mpr ⟨a,ha,b,hb,rfl⟩,mul_add x a b⟩

lemma dilate_product (x y : ℝ) (A : Finset ℝ) :
    dilate x (dilate y A)=dilate (x*y) A := by
  simp only [dilate,Finset.image_image,mul_assoc,Function.comp_def]

lemma dilate_inverse {x : ℝ} (hx : x≠0) (A : Finset ℝ) :
    dilate (1/x) (dilate x A)=A := by
  rw [dilate_product,one_div_mul_cancel hx]
  simp only [dilate,one_mul,Finset.image_id']

/-- Actual occupied covers under dilation retain their full scale factor. -/
theorem original_dilation_cover (A : Finset ℝ) {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    ((cells delta (dilate x A)).card:ℝ) ≤ (2*|x|+2)*(cells delta A).card := by
  have hh := bounded_dilation_floor_image A id hd (abs_nonneg x) (le_refl |x|)
  simpa only [cells,dilate,Finset.image_image,Function.comp_def,id_eq] using hh

/-- The denominator factor comes from the ACTUAL inverse dilation, not a
claim that unequal dilations preserve the original sum cover. -/
theorem original_inverse_dilation_cover (A : Finset ℝ) {delta x : ℝ}
    (hd : 0 < delta) (hx : x≠0) :
    ((cells delta A).card:ℝ) ≤ (2/|x|+2)*(cells delta (dilate x A)).card := by
  have hh := original_dilation_cover (dilate x A) hd (1/x)
  rw [dilate_inverse hx] at hh
  simpa only [abs_div,abs_one,mul_one_div] using hh

/-- Multiplying two original coefficients is controlled by original covers
through genuine Ruzsa and exact dilation identities. The reciprocal scale
loss is explicit, and the statement assumes no polynomial-image bound. -/
theorem original_product_coefficient_cover (A : Finset ℝ) {delta x y : ℝ}
    (hd : 0 < delta) (hx : x≠0) :
    ((cells delta (A+dilate (x*y) A)).card:ℝ)*(cells delta A).card ≤
      (1536*(1+|x|)^2/|x|)*
        (cells delta (A+dilate x A)).card*(cells delta (A+dilate y A)).card := by
  have htri := original_rounded_sum_triangle A (dilate x A) (dilate (x*y) A) hd
  have hscale := original_dilation_cover (A+dilate y A) hd x
  rw [dilate_sum,dilate_product] at hscale
  have hinv := original_inverse_dilation_cover A hd hx
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have hI : 0 ≤ 2/|x|+2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hinv
    (show (0:ℝ)≤(cells delta (A+dilate (x*y) A)).card from Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left htri hI
  have h3 := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ (2/|x|+2)*384*((cells delta (A+dilate x A)).card:ℝ) by positivity)
  have he : (2/|x|+2)*384*(2*|x|+2)=1536*(1+|x|)^2/|x| := by
    field_simp
    ring
  calc
    _ ≤ ((2/|x|+2)*384*(2*|x|+2))*
        ((cells delta (A+dilate x A)).card:ℝ)*(cells delta (A+dilate y A)).card := by
      nlinarith only [h1,h2,h3]
    _ = _ := by rw [he]

/-- A quantitative original small-cover consequence for a single product,
with no variable-length iteration hidden in the exponent. -/
theorem original_product_small_cover (A : Finset ℝ) {delta x y Dx Dy : ℝ}
    (hd : 0 < delta) (hx : x≠0) (hA : A.Nonempty) (hDx : 0 ≤ Dx)
    (hX : ((cells delta (A+dilate x A)).card:ℝ) ≤ Dx*(cells delta A).card)
    (hY : ((cells delta (A+dilate y A)).card:ℝ) ≤ Dy*(cells delta A).card) :
    ((cells delta (A+dilate (x*y) A)).card:ℝ) ≤
      (1536*(1+|x|)^2/|x|)*Dx*Dy*(cells delta A).card := by
  have hN : (0:ℝ) < (cells delta A).card := Nat.cast_pos.mpr (hA.image _).card_pos
  have hcoef : 0 ≤ 1536*(1+|x|)^2/|x| := by positivity
  have hh := original_product_coefficient_cover A hd hx (y:=y)
  have hp := mul_le_mul hX hY (Nat.cast_nonneg _)
    (show 0 ≤ Dx*((cells delta A).card:ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_left hp hcoef
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith only [hh,hm]

end OriginalRoundedRingProduct
