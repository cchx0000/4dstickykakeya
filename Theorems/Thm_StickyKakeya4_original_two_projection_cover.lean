import Theorems.Thm_StickyKakeya4_original_two_projection_cartesian
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTwoProjectionCover
open OriginalTwoProjectionCartesian ProjectionAnnulusEnergy
open ActualRoundedAdditiveEnergy NativeTangentGridCoarsening

/-- Bounded perturbation of actual values gives a bounded loss of occupied
floor cells, preserving the original input labels. -/
theorem perturbed_floor_image_card {X : Type*} [DecidableEq X]
    (P : Finset X) (f g : X → ℝ) {delta W : ℝ} (hd : 0 < delta) (hW : 0 ≤ W)
    (herr : ∀ p ∈ P, |g p-f p| ≤ W*delta) :
    ((P.image (fun p => rounded delta (g p))).card : ℝ) ≤
      (2*W+4)*(P.image (fun p => rounded delta (f p))).card := by
  let I := P.image (fun p => rounded delta (f p))
  let Q := fun z : ℤ => P.filter (fun p => rounded delta (f p)=z)
  let J := fun z : ℤ => (Q z).image (fun p => rounded delta (g p))
  have hfib : ∀ z ∈ I, ((J z).card : ℝ) ≤ 2*W+4 := by
    intro z _hz
    have hnear : ∀ p ∈ Q z, |g p-delta*(z : ℝ)| ≤ (W+1)*delta := by
      intro p hp
      obtain ⟨hpP,hpf⟩ := Finset.mem_filter.mp hp
      have he := round_error hd (f p)
      rw [hpf] at he
      have hfe : |f p-delta*(z : ℝ)| ≤ delta := abs_le.mpr ⟨by linarith,he.2.le⟩
      have ht := abs_add_le (g p-f p) (f p-delta*(z : ℝ))
      have hid : g p-f p+(f p-delta*(z : ℝ))=g p-delta*(z : ℝ) := by ring
      rw [hid] at ht
      have hg := herr p hpP
      nlinarith only [hfe,ht,hg]
    have hc := scalar_centered_grid_card (Q z) g hd
      (show 0 ≤ W+1 by linarith) hnear
    convert hc using 1 <;> try rfl
    ring
  have him : P.image (fun p => rounded delta (g p))=I.biUnion J := by
    ext z
    constructor
    · intro hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_biUnion.mpr ⟨rounded delta (f p),Finset.mem_image_of_mem _ hp,
        Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,rfl⟩,rfl⟩⟩
    · intro hz
      obtain ⟨i,_hi,hzi⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hzi
      exact Finset.mem_image.mpr ⟨p,(Finset.mem_filter.mp hp).1,hpz⟩
  rw [him]
  calc
    _ ≤ ∑ z ∈ I, ((J z).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ I, (2*W+4) := Finset.sum_le_sum hfib
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      dsimp [I]
      ring

/-- Every original subquery has an actual restricted scalar image controlled
by its original third projection. -/
theorem original_query_synthetic_cover (Q : Finset Point) {delta lam0 lam1 lam : ℝ}
    (hd : 0 < delta) (hneq : lam1≠lam0) :
    (((graph Q delta lam0 lam1).image
      (fun z => rounded delta (syntheticProjection delta lam0 lam1 lam z))).card : ℝ) ≤
      (2*(|leftWeight lam0 lam1 lam|+|rightWeight lam0 lam1 lam|)+4)*
        (alphabet Q delta lam).card := by
  have h := perturbed_floor_image_card Q (projection lam)
    (fun p => syntheticProjection delta lam0 lam1 lam (code delta lam0 lam1 p)) hd
    (show 0 ≤ |leftWeight lam0 lam1 lam|+|rightWeight lam0 lam1 lam| by positivity)
    (fun p _hp => by simpa only [abs_sub_comm,mul_comm] using synthetic_projection_error hd hneq p)
  change _ ≤ _ * ((Q.image (fun p => rounded delta (projection lam p))).card : ℝ)
  simpa only [graph,Finset.image_image,Function.comp_def] using h

lemma weights_le_of_transverse {h lam0 lam1 lam : ℝ} (hh : 0 < h)
    (htrans : h ≤ |lam1-lam0|) (h0 : |lam0| ≤ 1) (h1 : |lam1| ≤ 1) (hl : |lam| ≤ 1) :
    |leftWeight lam0 lam1 lam|+|rightWeight lam0 lam1 lam| ≤ 4/h := by
  have hden : 0 < |lam1-lam0| := hh.trans_le htrans
  have hnum0 : |lam1-lam| ≤ 2 := by
    have hx := abs_add_le lam1 (-lam)
    simp only [← sub_eq_add_neg,abs_neg] at hx
    linarith
  have hnum1 : |lam-lam0| ≤ 2 := by
    have hx := abs_add_le lam (-lam0)
    simp only [← sub_eq_add_neg,abs_neg] at hx
    linarith
  have hb0 : |leftWeight lam0 lam1 lam| ≤ 2/h := by
    dsimp [leftWeight]
    rw [abs_div]
    exact (div_le_div_of_nonneg_right hnum0 hden.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hh htrans)
  have hb1 : |rightWeight lam0 lam1 lam| ≤ 2/h := by
    dsimp [rightWeight]
    rw [abs_div]
    exact (div_le_div_of_nonneg_right hnum1 hden.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hh htrans)
  calc
    _ ≤ 2/h+2/h := add_le_add hb0 hb1
    _ = _ := by ring

theorem original_transverse_query_cover (Q : Finset Point) {delta h lam0 lam1 lam : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (htrans : h ≤ |lam1-lam0|)
    (h0 : |lam0| ≤ 1) (h1 : |lam1| ≤ 1) (hl : |lam| ≤ 1) :
    (((graph Q delta lam0 lam1).image
      (fun z => rounded delta (syntheticProjection delta lam0 lam1 lam z))).card : ℝ) ≤
      (8/h+4)*(alphabet Q delta lam).card := by
  have hn : lam1≠lam0 := by
    intro he
    rw [he,sub_self,abs_zero] at htrans
    linarith
  have hcover := original_query_synthetic_cover Q hd hn (lam := lam)
  have hw := weights_le_of_transverse hh htrans h0 h1 hl
  have hm := mul_le_mul_of_nonneg_right
    (show 2*(|leftWeight lam0 lam1 lam|+|rightWeight lam0 lam1 lam|)+4 ≤ 8/h+4 by
      calc
        _ ≤ 2*(4/h)+4 := by linarith only [hw]
        _ = _ := by ring)
    (Nat.cast_nonneg (alphabet Q delta lam).card)
  exact hcover.trans hm

end OriginalTwoProjectionCover
