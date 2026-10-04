import Theorems.Thm_StickyKakeya4_original_affine_alphabet_recode
import Theorems.Thm_StickyKakeya4_original_grid_bourgain_transfer
import Theorems.Thm_StickyKakeya4_gkz_grid_code_perturbation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open Classical

namespace OriginalRecodedGraphSource
open ActualRoundedAdditiveEnergy OriginalAffineAlphabetRecode OriginalGridBourgainTransfer
open GKZGridCodePerturbation

def pairLabel (sigma wa wb : ℝ) (p : ℝ × ℝ) : ℤ × ℤ :=
  (label sigma wa p.1,label sigma wb p.2)
def recodedGraph (G : Finset (ℝ × ℝ)) (sigma wa wb : ℝ) : Finset (ℤ × ℤ) :=
  G.image (pairLabel sigma wa wb)
def weightedValue (wa wb x : ℝ) (p : ℝ × ℝ) : ℝ := wa*p.1+x*(wb*p.2)

lemma original_recoded_graph_subset (A B : Finset ℝ) (G : Finset (ℝ × ℝ))
    (sigma wa wb : ℝ) (hG : G⊆A.product B) :
    recodedGraph G sigma wa wb⊆(labels A sigma wa).product (labels B sigma wb) := by
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp (hG hp)
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,Finset.mem_image_of_mem _ hb⟩

/-- BOTH original coordinate labels are injective at the chosen mesh,
so every actual old graph edge survives with exact cardinality. -/
theorem original_recoded_graph_card (A B : Finset ℝ) (G : Finset (ℝ × ℝ))
    {delta sigma wa wb : ℝ} (hd : 0 < delta) (hs : 0 < sigma)
    (hsa : sigma ≤ |wa| *delta) (hsb : sigma ≤ |wb| *delta)
    (hAsep : ∀ x∈A, ∀ y∈A, x≠y → delta ≤ |x-y|)
    (hBsep : ∀ x∈B, ∀ y∈B, x≠y → delta ≤ |x-y|)
    (hG : G⊆A.product B) : (recodedGraph G sigma wa wb).card=G.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  have hpAB := Finset.mem_product.mp (hG hp)
  have hqAB := Finset.mem_product.mp (hG hq)
  exact Prod.ext
    (original_label_injective A hd hs hsa hAsep hpAB.1 hqAB.1 (congrArg Prod.fst he))
    (original_label_injective B hd hs hsb hBsep hpAB.2 hqAB.2 (congrArg Prod.snd he))

lemma original_recode_value_error {sigma : ℝ} (hs : 0 < sigma)
    (wa wb x : ℝ) (p : ℝ × ℝ) :
    |weightedValue wa wb x p-
      ((scaledPoint sigma (pairLabel sigma wa wb p)).1+x*(scaledPoint sigma (pairLabel sigma wa wb p)).2)| ≤
      (1+|x|)*sigma := by
  have ha := original_label_error hs wa p.1
  have hb := original_label_error hs wb p.2
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg x)
  have ht := abs_add_le (wa*p.1-sigma*(label sigma wa p.1:ℝ))
    (x*(wb*p.2-sigma*(label sigma wb p.2:ℝ)))
  rw [abs_mul] at ht
  have he : weightedValue wa wb x p-
      ((scaledPoint sigma (pairLabel sigma wa wb p)).1+x*(scaledPoint sigma (pairLabel sigma wa wb p)).2)=
      (wa*p.1-sigma*(label sigma wa p.1:ℝ))+x*(wb*p.2-sigma*(label sigma wb p.2:ℝ)) := by
    dsimp [weightedValue,scaledPoint,pairLabel]
    ring
  rw [he]
  nlinarith only [ha,hm,ht]

/-- Re-rounding error is paid on the same original graph, retaining each
old witness and every queried coefficient. -/
theorem original_recoded_query_cover (G : Finset (ℝ × ℝ)) {sigma : ℝ} (hs : 0 < sigma)
    (wa wb x : ℝ) :
    (((recodedGraph G sigma wa wb).image (OriginalBourgainGraphTransfer.code x)).card:ℝ) ≤
      (8+2*|x|)*((G.image (fun p => rounded sigma (weightedValue wa wb x p))).card:ℝ) := by
  have herr : ∀ p∈G, |weightedValue wa wb x p-
      sigma*(OriginalBourgainGraphTransfer.code x (pairLabel sigma wa wb p):ℝ)| ≤ (2+|x|)*sigma := by
    intro p _hp
    let z := scaledPoint sigma (pairLabel sigma wa wb p)
    have h1 := original_recode_value_error hs wa wb x p
    have h2 := round_error hs (z.1+x*z.2)
    have he : rounded sigma (z.1+x*z.2)=OriginalBourgainGraphTransfer.code x (pairLabel sigma wa wb p) :=
      original_scaled_round hs x _
    rw [he] at h2
    have h2abs : |z.1+x*z.2-sigma*(OriginalBourgainGraphTransfer.code x (pairLabel sigma wa wb p):ℝ)| ≤ sigma :=
      (abs_of_nonneg h2.1).le.trans h2.2.le
    have ht := abs_sub_le (weightedValue wa wb x p) (z.1+x*z.2)
      (sigma*(OriginalBourgainGraphTransfer.code x (pairLabel sigma wa wb p):ℝ))
    nlinarith only [ht,h1,h2abs]
  have hh := code_image_le_floor_image G (weightedValue wa wb x)
    (fun p => OriginalBourgainGraphTransfer.code x (pairLabel sigma wa wb p)) hs
    (show 0≤2+|x| by positivity) herr
  unfold recodedGraph
  rw [Finset.image_image]
  simpa only [Function.comp_def,show (2:ℝ)*(2+|x|)+4=8+2*|x| by ring] using hh


lemma original_code_one (z : ℤ × ℤ) : OriginalBourgainGraphTransfer.code 1 z=z.1+z.2 := by
  unfold OriginalBourgainGraphTransfer.code OriginalBourgainGraphTransfer.value
  simp only [one_mul,← Int.cast_add,Int.floor_intCast]

/-- The selected third query is an actual restricted INTEGER sumset after
re-rounding. Its original value cover pays the explicit factor ten. -/
theorem original_recoded_restricted_sum_cover (G : Finset (ℝ × ℝ)) {sigma : ℝ}
    (hs : 0 < sigma) (wa wb : ℝ) :
    (((recodedGraph G sigma wa wb).image (fun z => z.1+z.2)).card:ℝ) ≤
      10*((G.image (fun p => rounded sigma (weightedValue wa wb 1 p))).card:ℝ) := by
  have hh := original_recoded_query_cover G hs wa wb 1
  have he : OriginalBourgainGraphTransfer.code 1=(fun z : ℤ × ℤ => z.1+z.2) := by
    funext z
    exact original_code_one z
  rw [he] at hh
  norm_num only [abs_one,show (8:ℝ)+2*1=10 by norm_num] at hh
  exact hh

end OriginalRecodedGraphSource
