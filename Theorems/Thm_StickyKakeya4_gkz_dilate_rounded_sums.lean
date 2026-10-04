import Theorems.Thm_StickyKakeya4_gkz_grid_code_perturbation
import Theorems.Thm_StickyKakeya4_gkz_original_product_overlap
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace GKZDilateRoundedSums
open ActualRoundedAdditiveEnergy GKZGridCodePerturbation GKZOriginalProductOverlap

lemma image_add_image {X Y G : Type*} [DecidableEq G] [Add G]
    (P : Finset X) (Q : Finset Y) (f : X → G) (g : Y → G) :
    P.image f + Q.image g = (P.product Q).image (fun p => f p.1+g p.2) := by
  ext z
  constructor
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_add.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx,
      g p.2, Finset.mem_image_of_mem _ hy, rfl⟩

lemma image_sub_image {X Y G : Type*} [DecidableEq G] [Sub G]
    (P : Finset X) (Q : Finset Y) (f : X → G) (g : Y → G) :
    P.image f - Q.image g = (P.product Q).image (fun p => f p.1-g p.2) := by
  ext z
  constructor
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact Finset.mem_sub.mpr ⟨f p.1, Finset.mem_image_of_mem _ hx,
      g p.2, Finset.mem_image_of_mem _ hy, rfl⟩

/-- Literal rounded self-sums of every bounded original dilation are
controlled by the original occupied sum cover, with the carry loss explicit. -/
theorem original_dilate_selfsum_cover (A : Finset ℝ) {delta a : ℝ}
    (hd : 0 < delta) (ha : |a| ≤ 2) :
    ((dilateCells delta A a+dilateCells delta A a).card : ℝ) ≤
      48*((A.product A).image (fun p => rounded delta (p.1+p.2))).card := by
  have herr : ∀ p∈A.product A,
      |a*(p.1+p.2)-delta*((rounded delta (a*p.1)+rounded delta (a*p.2):ℤ):ℝ)| ≤ 2*delta := by
    intro p _
    have h1 := round_error hd (a*p.1)
    have h2 := round_error hd (a*p.2)
    have hid : a*(p.1+p.2)-delta*((rounded delta (a*p.1)+rounded delta (a*p.2):ℤ):ℝ)=
        (a*p.1-delta*(rounded delta (a*p.1):ℝ))+
        (a*p.2-delta*(rounded delta (a*p.2):ℝ)) := by push_cast; ring
    rw [hid, abs_of_nonneg (by linarith)]
    linarith
  have hcode := code_image_le_floor_image (A.product A) (fun p => a*(p.1+p.2))
    (fun p => rounded delta (a*p.1)+rounded delta (a*p.2)) hd (by norm_num : (0:ℝ) ≤ 2) herr
  have hdilate := bounded_dilation_floor_image (A.product A) (fun p => p.1+p.2)
    hd (by norm_num : (0:ℝ) ≤ 2) ha
  rw [dilateCells, image_add_image]
  norm_num only at hcode hdilate
  nlinarith only [hcode, hdilate]

/-- Negating an actual real dilation is transferred to the integer difference
set with the complete rounding loss; no floor-negation identity is assumed. -/
theorem negative_dilate_anchor_cover (X : Finset ℤ) (A : Finset ℝ)
    {delta a : ℝ} (hd : 0 < delta) :
    ((X+dilateCells delta A (-a)).card : ℝ) ≤
      4*(X-dilateCells delta A a).card := by
  let value : ℤ × ℝ → ℝ := fun p => delta*(p.1:ℝ)-a*p.2
  let code : ℤ × ℝ → ℤ := fun p => p.1-rounded delta (a*p.2)
  have herr : ∀ p∈X.product A, |value p-delta*(code p:ℝ)| ≤ 1*delta := by
    intro p _
    have he := round_error hd (a*p.2)
    have hid : value p-delta*(code p:ℝ)=-(a*p.2-delta*(rounded delta (a*p.2):ℝ)) := by
      dsimp [value,code]
      push_cast
      ring
    rw [hid, abs_neg, abs_of_nonneg he.1, one_mul]
    exact he.2.le
  have hcode := floor_image_le_code_image (X.product A) value code hd (by norm_num) herr
  have hround (p : ℤ × ℝ) : rounded delta (value p)=p.1+rounded delta ((-a)*p.2) := by
    unfold rounded
    have hid : value p/delta=(p.1:ℝ)+((-a)*p.2)/delta := by
      dsimp [value]
      field_simp
      ring
    rw [hid, Int.floor_intCast_add]
  have hleft : (X.product A).image (fun p => rounded delta (value p))=
      X+dilateCells delta A (-a) := by
    simp_rw [hround]
    have hh := image_add_image X A (fun z : ℤ => z) (fun y => rounded delta ((-a)*y))
    simpa only [Finset.image_id', dilateCells] using hh.symm
  have hright : (X.product A).image code=X-dilateCells delta A a := by
    have hh := image_sub_image X A (fun z : ℤ => z) (fun y => rounded delta (a*y))
    simpa only [Finset.image_id', dilateCells, code] using hh.symm
  rw [hleft, hright] at hcode
  norm_num only at hcode
  exact hcode

end GKZDilateRoundedSums
