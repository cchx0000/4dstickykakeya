import Theorems.Thm_StickyKakeya4_original_recoded_graph_source
import Theorems.Thm_StickyKakeya4_original_two_projection_real_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open Classical

namespace OriginalNativeProjectionRecode
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph
open OriginalAffineAlphabetRecode OriginalRecodedGraphSource

def sourceCode (delta sigma a b wa wb : ℝ) (p : Point) : ℤ × ℤ :=
  pairLabel sigma wa wb (realPoint delta (code delta a b p))

def sourceGraph (Q : Finset Point) (delta sigma a b wa wb : ℝ) : Finset (ℤ × ℤ) :=
  Q.image (sourceCode delta sigma a b wa wb)

lemma original_source_graph_eq (Q : Finset Point) (delta sigma a b wa wb : ℝ) :
    sourceGraph Q delta sigma a b wa wb=
      recodedGraph (realGraph Q delta a b) sigma wa wb := by
  unfold sourceGraph sourceCode recodedGraph realGraph graph
  rw [Finset.image_image,Finset.image_image]
  rfl

lemma original_real_point_membership (R : Finset Point) (delta a b : ℝ)
    {p : Point} (hp : p∈R) :
    realPoint delta (code delta a b p)∈
      (realAlphabet R delta a).product (realAlphabet R delta b) := by
  apply real_graph_subset_product R delta a b
  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hp)

theorem original_source_graph_subset (R Q : Finset Point) (delta sigma a b wa wb : ℝ)
    (hQR : Q⊆R) :
    sourceGraph Q delta sigma a b wa wb⊆
      (labels (realAlphabet R delta a) sigma wa).product
        (labels (realAlphabet R delta b) sigma wb) := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  have hpAB := Finset.mem_product.mp (original_real_point_membership R delta a b (hQR hp))
  exact Finset.mem_product.mpr
    ⟨Finset.mem_image_of_mem _ hpAB.1,Finset.mem_image_of_mem _ hpAB.2⟩

/-- The finer weighted labels preserve the ORIGINAL two-projection
equivalence relation exactly on the original source. -/
theorem original_source_code_eq_iff (R : Finset Point) {delta sigma a b wa wb : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma)
    (hwa : sigma≤|wa| *(delta/4)) (hwb : sigma≤|wb| *(delta/4))
    {p q : Point} (hp : p∈R) (hq : q∈R) :
    sourceCode delta sigma a b wa wb p=sourceCode delta sigma a b wa wb q ↔
      code delta a b p=code delta a b q := by
  constructor
  · intro he
    have hpAB := Finset.mem_product.mp (original_real_point_membership R delta a b hp)
    have hqAB := Finset.mem_product.mp (original_real_point_membership R delta a b hq)
    apply realPoint_injective hd
    exact Prod.ext
      (original_label_injective (realAlphabet R delta a) (by positivity) hs hwa
        (real_alphabet_separated R hd) hpAB.1 hqAB.1 (congrArg Prod.fst he))
      (original_label_injective (realAlphabet R delta b) (by positivity) hs hwb
        (real_alphabet_separated R hd) hpAB.2 hqAB.2 (congrArg Prod.snd he))
  · intro he
    exact congrArg (fun z => pairLabel sigma wa wb (realPoint delta z)) he

/-- Every fiber of the actual final code is an old original geometric
fiber. Its cardinal cap comes from native point separation. -/
theorem original_source_code_fiber (R : Finset Point) {delta sigma h a b wa wb : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hh : 0 < h) (hh1 : h≤1)
    (htrans : h≤|b-a|) (ha : |a|≤1)
    (hwa : sigma≤|wa| *(delta/4)) (hwb : sigma≤|wb| *(delta/4))
    (hsep : ∀ p∈R, ∀ q∈R, p≠q → delta≤‖p-q‖)
    {z : ℤ × ℤ} (hz : z∈sourceGraph R delta sigma a b wa wb) :
    ((R.filter (fun p => sourceCode delta sigma a b wa wb p=z)).card:ℝ)≤fiberBound h := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  have he : R.filter (fun p => sourceCode delta sigma a b wa wb p=
      sourceCode delta sigma a b wa wb q)=R.filter (fun p => code delta a b p=code delta a b q) := by
    ext p
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hp => original_source_code_eq_iff R hd hs hwa hwb hp hq)
  rw [he]
  exact original_code_fiber_card R hd hh hh1 htrans ha hsep (Finset.mem_image_of_mem _ hq)

theorem original_source_graph_card (Q : Finset Point) {delta sigma a b wa wb : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma)
    (hwa : sigma≤|wa| *(delta/4)) (hwb : sigma≤|wb| *(delta/4)) :
    (sourceGraph Q delta sigma a b wa wb).card=(graph Q delta a b).card := by
  rw [original_source_graph_eq]
  rw [original_recoded_graph_card (realAlphabet Q delta a) (realAlphabet Q delta b)
    (realGraph Q delta a b) (by positivity : 0<delta/4) hs hwa hwb
    (real_alphabet_separated Q hd) (real_alphabet_separated Q hd)
    (real_graph_subset_product Q delta a b)]
  exact real_graph_card Q hd

/-- Every later original query retains the same geometrically proved
mass bound after both normalizations and both floor operations. -/
theorem original_source_query_mass (P Q : Finset Point) {delta sigma h a b wa wb : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hh : 0 < h) (hh1 : h≤1)
    (htrans : h≤|b-a|) (ha : |a|≤1)
    (hwa : sigma≤|wa| *(delta/4)) (hwb : sigma≤|wb| *(delta/4))
    (hsep : ∀ p∈P, ∀ q∈P, p≠q → delta≤‖p-q‖) (hQP : Q⊆P) :
    (Q.card:ℝ)≤fiberBound h*(sourceGraph Q delta sigma a b wa wb).card := by
  rw [original_source_graph_card Q hd hs hwa hwb]
  exact original_query_graph_mass P hd hh hh1 htrans ha hsep Q hQP

lemma original_transverse_recode_scale {delta h w : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hw : h/2≤|w|) :
    h*delta/64≤|w| *(delta/4) := by
  have hm := mul_le_mul_of_nonneg_right hw hd.le
  nlinarith only [hm,mul_pos hh hd]

end OriginalNativeProjectionRecode
