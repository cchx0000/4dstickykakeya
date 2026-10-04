import Theorems.Thm_StickyKakeya4_original_rounded_ring_product
import Theorems.Thm_StickyKakeya4_gkz_real_dilation_union

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped Pointwise BigOperators

namespace OriginalSelectedWordCover
open OriginalRoundedRuzsaCover OriginalRoundedRingProduct
open ActualRoundedAdditiveEnergy GKZOriginalProductOverlap GKZRealDilationUnion

/-- A selected sum uses only its own finitely many actual coefficient
terms. The carrier is bounded by the word LENGTH, not by the number of all
possible monomials in the original coefficient set. -/
theorem original_selected_word_cover (A : Finset ℝ) (T : ℕ) (f : Fin T → ℝ)
    {delta M : ℝ} (hd : 0 < delta) (hA : A.Nonempty) (hM : 0 ≤ M)
    (hself : ((cells delta (A+A)).card:ℝ) ≤ M*(cells delta A).card)
    (hsmall : ∀ i, ((cells delta (A+dilate (f i) A)).card:ℝ) ≤ M*(cells delta A).card) :
    ((cells delta (A+dilate (∑ i,f i) A)).card:ℝ) ≤
      ((2*T+5:ℕ):ℝ)*(((T+1:ℕ):ℝ)*(8*M))^(T+1)*(cells delta A).card := by
  let J := insert 1 (Finset.univ.image f)
  let U := dilateUnion A J
  let X := cells delta A
  have hX : X.Nonempty := hA.image _
  have hJ : (J.card:ℝ) ≤ (T+1:ℕ) := by
    have hh : J.card ≤ T+1 := (Finset.card_insert_le _ _).trans (by
      have hi := Finset.card_image_le (s:=Finset.univ) (f:=f)
      simpa only [Finset.card_univ,Fintype.card_fin] using Nat.add_le_add_right hi 1)
    exact_mod_cast hh
  have hJsmall : ∀ x∈J, ((cells delta (A+dilate x A)).card:ℝ) ≤ M*X.card := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have he : dilate 1 A=A := by simp only [dilate,one_mul,Finset.image_id']
      simpa only [he] using hself
    · obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hx
      exact hsmall i
  have hanchor : ∀ x∈J, ((X+dilateCells delta A x).card:ℝ) ≤ (8*M)*X.card := by
    intro x hx
    have hround := (sum_rounding_comparison A (dilate x A) hd).1
    have he : cells delta (dilate x A)=dilateCells delta A x := by
      simp only [cells,dilate,dilateCells,Finset.image_image,Function.comp_def]
    rw [he] at hround
    have hm := mul_le_mul_of_nonneg_left (hJsmall x hx) (by norm_num : (0:ℝ)≤8)
    nlinarith only [hround,hm]
  have hcover := original_dilate_union_iterated_cover A J X hd hX hanchor (T+1)
  have hmember : ∀ a∈A, ∀ b∈A, a+(∑ i,f i)*b∈(T+1) • U := by
    intro a ha b hb
    have hfirst : a∈U := by
      apply Finset.mem_biUnion.mpr
      exact ⟨1,Finset.mem_insert_self _ _,Finset.mem_image.mpr ⟨a,ha,one_mul a⟩⟩
    have hterms : ∀ i : Fin T, f i*b∈U := by
      intro i
      apply Finset.mem_biUnion.mpr
      exact ⟨f i,Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)),
        Finset.mem_image_of_mem _ hb⟩
    have hsum : (∑ i,f i*b)∈T • U := by
      apply Finset.mem_nsmul.mpr
      refine ⟨fun i => ⟨f i*b,hterms i⟩,?_⟩
      simp only [List.sum_ofFn]
    rw [succ_nsmul]
    apply Finset.mem_add.mpr
    exact ⟨∑ i,f i*b,hsum,a,hfirst,by rw [← Finset.sum_mul]; ring⟩
  have hsub : A+dilate (∑ i,f i) A⊆(T+1) • U := by
    intro z hz
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact hmember a ha b hb
  have hcount : ((cells delta (A+dilate (∑ i,f i) A)).card:ℝ) ≤
      (((T+1) • U).image (rounded delta)).card :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hsub))
  have hfactor := mul_le_mul_of_nonneg_right hJ (show 0≤8*M by positivity)
  have hp := pow_le_pow_left₀ (show 0≤(J.card:ℝ)*(8*M) by positivity) hfactor (T+1)
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0≤((2*(T+1+1)+1:ℕ):ℝ)*(X.card:ℝ) by positivity)
  have hid : 2*(T+1+1)+1=2*T+5 := by omega
  rw [hid] at hcover hm
  exact hcount.trans (hcover.trans (by nlinarith only [hm]))

end OriginalSelectedWordCover
