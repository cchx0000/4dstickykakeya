import Theorems.Thm_StickyKakeya4_gkz_finite_anchored_plunnecke
import Theorems.Thm_StickyKakeya4_gkz_original_product_overlap
import Theorems.Thm_StickyKakeya4_rounded_iterated_cover_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace GKZRealDilationUnion
open ActualRoundedAdditiveEnergy GKZOriginalProductOverlap GKZFiniteAnchoredPlunnecke

def dilateUnion (A J : Finset ℝ) : Finset ℝ :=
  J.biUnion (fun a => A.image (fun x => a*x))

lemma rounded_dilateUnion (A J : Finset ℝ) (delta : ℝ) :
    (dilateUnion A J).image (rounded delta)=J.biUnion (dilateCells delta A) := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem _ hx⟩
  · intro hz
    obtain ⟨a, ha, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨a*x,
      Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem _ hx⟩, rfl⟩

/-- The fixed original real union is controlled by its actual integer union,
homogeneous Plünnecke, and the existing explicit iterated rounding bridge. -/
theorem original_dilate_union_iterated_cover (A J : Finset ℝ) (X : Finset ℤ)
    {delta M : ℝ} (hd : 0 < delta) (hX : X.Nonempty)
    (hsmall : ∀ a∈J, ((X+dilateCells delta A a).card : ℝ) ≤ M*X.card) (n : ℕ) :
    (((n • dilateUnion A J).image (rounded delta)).card : ℝ) ≤
      (2*(n+1)+1 : ℕ)*((J.card : ℝ)*M)^n*X.card := by
  have hp := finite_union_anchored_sum X J (dilateCells delta A) hX hsmall n
  have hr := RoundedIteratedCoverTransfer.iterated_grid_cover_bound
    (dilateUnion A J) (0 : Finset ℝ) hd n 0
  have hzero : (0 : Finset ℝ).image (rounded delta)=(0 : Finset ℤ) := by
    change ({0} : Finset ℝ).image (rounded delta)=({0} : Finset ℤ)
    simp [rounded]
  simp only [zero_nsmul, zero_add, sub_zero, hzero, Nat.add_zero] at hr
  rw [rounded_dilateUnion] at hr
  have hrR : (((n • dilateUnion A J).image (rounded delta)).card : ℝ) ≤
      ((2*(n+1)+1 : ℕ) : ℝ)*(n • J.biUnion (dilateCells delta A)).card := by
    exact_mod_cast hr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (2*(n+1)+1))
  exact hrR.trans (by nlinarith only [hm])

private lemma nine_sum_mem (U : Finset ℝ) {w0 w1 w2 w3 w4 w5 w6 w7 w8 : ℝ}
    (h0 : w0∈U) (h1 : w1∈U) (h2 : w2∈U) (h3 : w3∈U) (h4 : w4∈U)
    (h5 : w5∈U) (h6 : w6∈U) (h7 : w7∈U) (h8 : w8∈U) :
    w0+w1+w2+w3+w4+w5+w6+w7+w8 ∈ 9 • U := by
  have append {n : ℕ} {x y : ℝ} (hx : x∈n • U) (hy : y∈U) :
      x+y∈(n+1) • U := by
    rw [succ_nsmul]
    exact Finset.mem_add.mpr ⟨x,hx,y,hy,rfl⟩
  have hstart : w0∈1 • U := by simpa using h0
  exact append (append (append (append (append (append (append (append hstart h1) h2) h3) h4) h5) h6) h7) h8

/-- Both actual gap expressions, together with a full original anchor,
belong to nine sums of the signed original dilation union. -/
theorem original_gap_target_subset_nine (A A1 U : Finset ℝ)
    {b x x' y y' e1 e2 : ℝ} (hA1 : A1 ⊆ A)
    (hzero : 0∈U)
    (hanchor : ∀ a∈A, b*a∈U)
    (hx : ∀ a∈A, x*a∈U) (hx' : ∀ a∈A, (-x')*a∈U)
    (hy : ∀ a∈A, y*a∈U) (hy' : ∀ a∈A, (-y')*a∈U)
    (he2 : e2=2*(y-y')) (he1 : e1=x-x' ∨ e1=(x-x')+(y-y')) :
    (A.product ((A1.product A1).image (fun p => e2*p.1+e1*p.2))).image
      (fun p => b*p.1+p.2) ⊆ 9 • U := by
  intro z hz
  obtain ⟨⟨a,s⟩, hq, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hqa, hqs⟩ := Finset.mem_product.mp hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hqs
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  have hp1A := hA1 hp1
  have hp2A := hA1 hp2
  rcases he1 with he1 | he1
  · have hm := nine_sum_mem U (hanchor a hqa) (hx p.2 hp2A) (hx' p.2 hp2A)
      (hy p.1 hp1A) (hy' p.1 hp1A) (hy p.1 hp1A) (hy' p.1 hp1A) hzero hzero
    convert hm using 1
    rw [he1, he2]
    ring
  · have hm := nine_sum_mem U (hanchor a hqa) (hx p.2 hp2A) (hx' p.2 hp2A)
      (hy p.1 hp1A) (hy' p.1 hp1A) (hy p.1 hp1A) (hy' p.1 hp1A)
      (hy p.2 hp2A) (hy' p.2 hp2A)
    convert hm using 1
    rw [he1, he2]
    ring

/-- The actual dense-case expression uses four signed original dilates and
the full original anchor; four zero terms pad it to the same ninth sum. -/
theorem original_dense_target_subset_nine (A A1 U : Finset ℝ)
    {b x x' y y' : ℝ} (hA1 : A1 ⊆ A) (hzero : 0∈U)
    (hanchor : ∀ a∈A, b*a∈U)
    (hx : ∀ a∈A, x*a∈U) (hx' : ∀ a∈A, (-x')*a∈U)
    (hy : ∀ a∈A, y*a∈U) (hy' : ∀ a∈A, (-y')*a∈U) :
    (A.product ((A1.product A1).image (fun p => (y-y')*p.1+(x-x')*p.2))).image
      (fun p => b*p.1+p.2) ⊆ 9 • U := by
  intro z hz
  obtain ⟨⟨a,s⟩, hq, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hqa,hqs⟩ := Finset.mem_product.mp hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hqs
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  have hm := nine_sum_mem U (hanchor a hqa) (hx p.2 (hA1 hp2)) (hx' p.2 (hA1 hp2))
    (hy p.1 (hA1 hp1)) (hy' p.1 (hA1 hp1)) hzero hzero hzero hzero
  convert hm using 1
  ring

end GKZRealDilationUnion
