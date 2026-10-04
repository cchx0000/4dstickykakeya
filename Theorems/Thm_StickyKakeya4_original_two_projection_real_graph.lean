import Theorems.Thm_StickyKakeya4_original_two_projection_cover
import Theorems.Thm_StickyKakeya4_integer_bin_real_near_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalTwoProjectionRealGraph
open OriginalTwoProjectionCartesian OriginalTwoProjectionCover ProjectionAnnulusEnergy
open ActualRoundedAdditiveEnergy IntegerBinRealNearEnergy

def realPoint (delta : ℝ) (z : ℤ × ℤ) : Point :=
  ((delta/4)*(z.1 : ℝ),(delta/4)*(z.2 : ℝ))
def realAlphabet (P : Finset Point) (delta lam : ℝ) : Finset ℝ :=
  realGrid (delta/4) (alphabet P delta lam)
def realGraph (P : Finset Point) (delta lam0 lam1 : ℝ) : Finset Point :=
  (graph P delta lam0 lam1).image (realPoint delta)
def linearValue (lam0 lam1 lam : ℝ) (z : Point) : ℝ :=
  leftWeight lam0 lam1 lam*z.1+rightWeight lam0 lam1 lam*z.2

lemma realPoint_injective {delta : ℝ} (hd : 0 < delta) :
    Function.Injective (realPoint delta) := by
  intro z w he
  have hpos : 0 < delta/4 := by positivity
  exact Prod.ext (real_grid_injective hpos (congrArg Prod.fst he))
    (real_grid_injective hpos (congrArg Prod.snd he))

theorem real_graph_card (P : Finset Point) {delta lam0 lam1 : ℝ} (hd : 0 < delta) :
    (realGraph P delta lam0 lam1).card=(graph P delta lam0 lam1).card :=
  Finset.card_image_of_injective _ (realPoint_injective hd)

theorem real_alphabet_card (P : Finset Point) {delta lam : ℝ} (hd : 0 < delta) :
    (realAlphabet P delta lam).card=(alphabet P delta lam).card :=
  real_grid_card (by positivity) _

theorem real_graph_subset_product (P : Finset Point) (delta lam0 lam1 : ℝ) :
    realGraph P delta lam0 lam1 ⊆
      (realAlphabet P delta lam0).product (realAlphabet P delta lam1) := by
  rintro z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  have hp := Finset.mem_product.mp (graph_subset_product P delta lam0 lam1 hw)
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp.1,Finset.mem_image_of_mem _ hp.2⟩

theorem real_alphabet_separated (P : Finset Point) {delta lam : ℝ} (hd : 0 < delta) :
    ∀ x ∈ realAlphabet P delta lam, ∀ y ∈ realAlphabet P delta lam,
      x≠y → delta/4 ≤ |x-y| := real_grid_separated (by positivity) _

theorem real_alphabet_unit_box (P : Finset Point) {delta lam : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hlam : |lam| ≤ 1)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1) :
    ∀ x ∈ realAlphabet P delta lam, |x| ≤ 1 := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp0,hp1⟩ := hP p hp
  have hprod := mul_le_mul hlam hp1 (abs_nonneg p.2) (by norm_num : (0:ℝ) ≤ 1)
  have htri := abs_add_le p.1 (-(lam*p.2))
  simp only [← sub_eq_add_neg,abs_neg,abs_mul] at htri
  have hproj : |projection lam p| ≤ 2 := by
    dsimp [projection]
    nlinarith only [htri,hprod,hp0]
  have he := round_error hd (projection lam p)
  have hprojb := abs_le.mp hproj
  change |delta/4*(rounded delta (projection lam p) : ℝ)| ≤ 1
  apply abs_le.mpr
  constructor <;> nlinarith only [he.1,he.2,hprojb.1,hprojb.2,hd1]

/-- Actual Cartesian edges remember a single original planar point. -/
theorem real_graph_original_witness (P : Finset Point) (delta lam0 lam1 : ℝ)
    {z : Point} (hz : z ∈ realGraph P delta lam0 lam1) :
    ∃ p ∈ P, z=realPoint delta (code delta lam0 lam1 p) := by
  obtain ⟨w,hw,hwz⟩ := Finset.mem_image.mp hz
  obtain ⟨p,hp,hpw⟩ := Finset.mem_image.mp hw
  exact ⟨p,hp,hwz.symm.trans (congrArg (realPoint delta) hpw.symm)⟩

lemma rounded_linearValue_realPoint {delta lam0 lam1 lam : ℝ} (hd : 0 < delta)
    (z : ℤ × ℤ) :
    rounded (delta/4) (linearValue lam0 lam1 lam (realPoint delta z))=
      rounded delta (syntheticProjection delta lam0 lam1 lam z) := by
  unfold rounded
  congr 1
  dsimp [linearValue,realPoint,syntheticProjection]
  field_simp

/-- Literal restricted scalar images on separated real alphabets have the
same controlled cover as their original planar queries. -/
theorem real_query_cover (Q : Finset Point) {delta h lam0 lam1 lam : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (htrans : h ≤ |lam1-lam0|)
    (h0 : |lam0| ≤ 1) (h1 : |lam1| ≤ 1) (hl : |lam| ≤ 1) :
    (((realGraph Q delta lam0 lam1).image
      (fun z => rounded (delta/4) (linearValue lam0 lam1 lam z))).card : ℝ) ≤
      (8/h+4)*(alphabet Q delta lam).card := by
  have him : (realGraph Q delta lam0 lam1).image
      (fun z => rounded (delta/4) (linearValue lam0 lam1 lam z))=
      (graph Q delta lam0 lam1).image
        (fun z => rounded delta (syntheticProjection delta lam0 lam1 lam z)) := by
    unfold realGraph
    rw [Finset.image_image]
    apply Finset.image_congr
    intro z _hz
    exact rounded_linearValue_realPoint hd z
  rw [him]
  exact original_transverse_query_cover Q hd hh htrans h0 h1 hl

/-- A true original query supplies actual graph collision energy; no energy
or density certificate is assumed after quotienting. -/
theorem original_query_collision_energy (P Q : Finset Point)
    {delta h lam0 lam1 lam : ℝ} (hd : 0 < delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (h0 : |lam0| ≤ 1) (h1 : |lam1| ≤ 1) (hl : |lam| ≤ 1)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p≠q → delta ≤ ‖p-q‖) (hQP : Q ⊆ P) :
    (Q.card : ℝ)^2 ≤ fiberBound h^2 * (8/h+4) * (alphabet Q delta lam).card *
      (TwoTubePathCollisionCount.collisions (realGraph Q delta lam0 lam1)
        (fun z => rounded (delta/4) (linearValue lam0 lam1 lam z))).card := by
  let G := realGraph Q delta lam0 lam1
  let f := fun z => rounded (delta/4) (linearValue lam0 lam1 lam z)
  have hm := original_query_graph_mass P hd hh hh1 htrans h0 hsep Q hQP
  rw [← real_graph_card Q hd] at hm
  have hc : (G.card : ℝ)^2 ≤ ((G.image f).card : ℝ)*
      (TwoTubePathCollisionCount.collisions G f).card := by
    exact_mod_cast TwoTubePathCollisionCount.square_card_le_image_mul_collisions G f
  have hcover := real_query_cover Q hd hh htrans h0 h1 hl
  have hmass2 := sq_le_sq₀ (Nat.cast_nonneg Q.card)
    (show 0 ≤ fiberBound h*(realGraph Q delta lam0 lam1).card by
      exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) |>.mpr hm
  have hc1 := mul_le_mul_of_nonneg_left hc (sq_nonneg (fiberBound h))
  have hc2 := mul_le_mul_of_nonneg_right hcover
    (Nat.cast_nonneg (TwoTubePathCollisionCount.collisions G f).card)
  have hc3 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg (fiberBound h))
  dsimp [G,f] at hc1 hc3
  nlinarith only [hmass2,hc1,hc3]

end OriginalTwoProjectionRealGraph
