import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_distance
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalExpandedBandCount
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalUnitNormals OriginalThreeDimensionalCapCount
open OriginalThreeDimensionalCapCoordinates OriginalThreeDimensionalCapDistance
open OriginalThreeDimensionalTubeSlab

private theorem expanded_integer_band (S : Finset ℤ) (rho Delta A c : ℝ)
    (hrho : 0 < rho) (hDelta : rho ≤ Delta) (hA : A ≠ 0) (hA2 : |A| ≤ 2)
    (hS : ∀ k∈S,|rho*(k:ℝ)*A+c| ≤ 10*Delta) :
    (S.card : ℝ)*rho*|A| ≤ 24*Delta := by
  have hAp : 0 < |A| := abs_pos.mpr hA
  have hDp : 0 < Delta := hrho.trans_le hDelta
  have hs (k : ℤ) (hk : k∈S) : |rho*(k:ℝ)-(-c/A)| ≤ 10*Delta/|A| := by
    have he : rho*(k:ℝ)-(-c/A)=(rho*(k:ℝ)*A+c)/A := by field_simp; ring
    rw [he,abs_div]
    exact div_le_div_of_nonneg_right (hS k hk) hAp.le
  have hc := integer_interval_mass S rho (10*Delta/|A|) (-c/A) hrho (by positivity) hs
  have hm := mul_le_mul_of_nonneg_right hc hAp.le
  have he : (2*(10*Delta/|A|)+2*rho)*|A|=20*Delta+2*rho*|A| := by field_simp; ring
  rw [he] at hm
  have hb := mul_le_mul_of_nonneg_left hA2 hrho.le
  nlinarith only [hm,hb,hDelta]

private theorem expanded_first_coefficient (S : Finset (ℤ×ℤ)) (rho Delta A B C D : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hDelta : rho ≤ Delta)
    (hD : 0 < D) (hDA : D ≤ 20*|A|) (hA2 : |A| ≤ 2)
    (hband : ∀ z∈S,|rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C| ≤ 10*Delta)
    (hgrid : ∀ z∈S,|rho*(z.2:ℝ)| ≤ 4) :
    (S.card : ℝ)*rho^2*D ≤ 4800*Delta := by
  have hDp : 0 < Delta := hrho.trans_le hDelta
  have hA : A ≠ 0 := by intro hz; rw [hz,abs_zero,mul_zero] at hDA; linarith only [hDA,hD]
  have hf : ∀ l∈S.image Prod.snd,((S.filter (fun z => z.2=l)).card : ℝ)*(rho*D) ≤ 480*Delta := by
    intro l _hl
    let F := S.filter (fun z => z.2=l)
    have hi : Set.InjOn Prod.fst (↑F : Set (ℤ×ℤ)) := by
      intro z hz z' hz' he
      exact Prod.ext he ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm)
    have hs (k : ℤ) (hk : k∈F.image Prod.fst) :
        |rho*(k:ℝ)*A+(rho*(l:ℝ)*B+C)| ≤ 10*Delta := by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hzS,hzl⟩ := Finset.mem_filter.mp hz
      simpa only [hzl,add_assoc] using hband z hzS
    have hc := expanded_integer_band (F.image Prod.fst) rho Delta A (rho*(l:ℝ)*B+C)
      hrho hDelta hA hA2 hs
    rw [Finset.card_image_of_injOn hi] at hc
    have hm := mul_le_mul_of_nonneg_left hDA (show 0 ≤ (F.card : ℝ)*rho by positivity)
    change (F.card : ℝ)*(rho*D) ≤ 480*Delta
    nlinarith only [hc,hm]
  have ht := weighted_fiber_count S Prod.snd (rho*D) (480*Delta) hf
  have hc := integer_interval_mass (S.image Prod.snd) rho 4 0 hrho (by norm_num) (by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    simpa only [sub_zero] using hgrid z hz)
  have hm := mul_le_mul_of_nonneg_right ht hrho.le
  have hq := mul_le_mul_of_nonneg_left hc (show 0 ≤ 480*Delta by positivity)
  nlinarith only [hm,hq,mul_le_mul_of_nonneg_left hrho1 (show 0 ≤ 960*Delta by positivity)]

private theorem expanded_rectangle_band (S : Finset (ℤ×ℤ)) (rho Delta A B C D : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hDelta : rho ≤ Delta)
    (hDsum : D ≤ |A|+|B|+|C|) (hA2 : |A| ≤ 2) (hB2 : |B| ≤ 2)
    (hgrid : ∀ z∈S,|rho*(z.1:ℝ)| ≤ 4 ∧ |rho*(z.2:ℝ)| ≤ 1)
    (hband : ∀ z∈S,|rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C| ≤ 10*Delta) :
    (S.card : ℝ)*rho^2*max D Delta ≤ 5000*Delta := by
  have hDp : 0 < Delta := hrho.trans_le hDelta
  by_cases hsmall : D ≤ 20*Delta
  · have hcoord (f : ℤ×ℤ → ℤ) (hg : ∀ z∈S,|rho*(f z:ℝ)| ≤ 4) :
        ((S.image f).card : ℝ)*rho ≤ 10 := by
      have hc := integer_interval_mass (S.image f) rho 4 0 hrho (by norm_num) (by
        intro k hk; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
        simpa only [sub_zero] using hg z hz)
      linarith only [hc,hrho1]
    have h1 := hcoord Prod.fst (fun z hz => (hgrid z hz).1)
    have h2 := hcoord Prod.snd (fun z hz => (hgrid z hz).2.trans (by norm_num))
    have hsub : S⊆(S.image Prod.fst).product (S.image Prod.snd) := by
      intro z hz; exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hz⟩
    have hc : (S.card : ℝ) ≤ ((S.image Prod.fst).card : ℝ)*(S.image Prod.snd).card := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
    have hh := mul_le_mul h1 h2 (by positivity : 0 ≤ (S.image Prod.snd).card*rho) (by norm_num : (0:ℝ) ≤ 10)
    have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg rho)
    have hcsmall : (S.card : ℝ)*rho^2 ≤ 100 := by nlinarith only [hh,hc']
    have hm : max D Delta ≤ 20*Delta := max_le hsmall (by linarith only [hDp])
    have hm' := mul_le_mul hcsmall hm (le_max_right D Delta |>.trans' hDp.le) (by norm_num : (0:ℝ) ≤ 100)
    nlinarith only [hm',hDp]
  · have hD : 0 < D := by linarith only [hsmall,hDp]
    have hDeltaD : Delta ≤ D := by linarith only [hsmall,hDp]
    rw [max_eq_left hDeltaD]
    by_cases hne : S.Nonempty
    · obtain ⟨z,hz⟩ := hne
      have hc := abs_sub (rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C)
        (rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B)
      have he : rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B+C-(rho*(z.1:ℝ)*A+rho*(z.2:ℝ)*B)=C := by ring
      rw [he] at hc
      have ht := abs_add_le (rho*(z.1:ℝ)*A) (rho*(z.2:ℝ)*B)
      rw [abs_mul (rho*(z.1:ℝ)) A,abs_mul (rho*(z.2:ℝ)) B] at ht
      have hga := mul_le_mul_of_nonneg_right (hgrid z hz).1 (abs_nonneg A)
      have hgb := mul_le_mul_of_nonneg_right (hgrid z hz).2 (abs_nonneg B)
      have hC : |C| ≤ 4*|A|+|B|+10*Delta := by linarith only [hc,ht,hga,hgb,hband z hz]
      have hchoice : D ≤ 20*|A| ∨ D ≤ 20*|B| := by
        by_contra hf; push Not at hf
        linarith only [hDsum,hC,lt_of_not_ge hsmall,hf.1,hf.2,hD]
      rcases hchoice with ha | hb
      · exact (expanded_first_coefficient S rho Delta A B C D hrho hrho1 hDelta hD ha hA2
          hband (fun z hz => (hgrid z hz).2.trans (by norm_num))).trans (by linarith only [hDp])
      · have hs : ∀ z∈S.image Prod.swap,
            |rho*(z.1:ℝ)*B+rho*(z.2:ℝ)*A+C| ≤ 10*Delta := by
          intro z hz
          obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
          simpa only [Prod.fst_swap,Prod.snd_swap,add_comm (rho*(w.2:ℝ)*B)] using hband w hw
        have hg : ∀ z∈S.image Prod.swap,|rho*(z.2:ℝ)| ≤ 4 := by
          intro z hz
          obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
          exact (hgrid w hw).1
        have hh := expanded_first_coefficient (S.image Prod.swap) rho Delta B A C D hrho hrho1 hDelta hD hb hB2 hs hg
        rw [Finset.card_image_of_injective _ Prod.swap_injective] at hh
        exact hh.trans (by linarith only [hDp])
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      simp only [zero_mul]
      positivity

/-- Actual original direction-grid labels satisfy the enlarged great-circle
band count, retaining both the normal mesh and the physical slice width. -/
theorem original_expanded_normal_band_count (S : Finset DirectionLabel)
    (rho Delta : ℝ) (p q : Point3)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hDelta : rho ≤ Delta)
    (hp : ∀ i,|p i| ≤ 1) (hq : ∀ i,|q i| ≤ 1)
    (hS : S⊆normalGrid rho)
    (hband : ∀ d∈S,|value rho d q-value rho d p| ≤ 10*Delta) :
    (S.card : ℝ)*rho^2*max (distance3 p q) Delta ≤ 60000*Delta := by
  have hDp : 0 < Delta := hrho.trans_le hDelta
  have hd2 (i : Fin 3) : |q i-p i| ≤ 2 := by
    have hh := abs_sub (q i) (p i)
    linarith only [hh,hp i,hq i]
  have hf : ∀ e∈S.image Prod.fst,
      ((S.filter (fun d => d.1=e)).card : ℝ)*(rho^2*max (pointGap p q) Delta) ≤ 5000*Delta := by
    intro e _he
    let F := S.filter (fun d => d.1=e)
    let T := F.image Prod.snd
    have hi : Set.InjOn Prod.snd (↑F : Set DirectionLabel) := by
      intro z hz z' hz' hzz
      exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) hzz
    have hc : T.card=F.card := Finset.card_image_of_injOn hi
    have hmem (z : ℤ×ℤ) (hz : z∈T) : (e,z)∈S := by
      obtain ⟨d,hd,hz⟩ := Finset.mem_image.mp hz
      obtain ⟨hdS,hde⟩ := Finset.mem_filter.mp hd
      have heq : d=(e,z) := Prod.ext hde hz
      simpa only [← heq] using hdS
    have hg (z : ℤ×ℤ) (hz : z∈T) : |rho*(z.1:ℝ)| ≤ 4 ∧ |rho*(z.2:ℝ)| ≤ 1 :=
      actual_grid_coefficients rho (e,z) hrho hrho1 (hS (hmem z hz))
    have hb (z : ℤ×ℤ) (hz : z∈T) :
        |rho*(z.1:ℝ)*(q (e 0)-p (e 0))+rho*(z.2:ℝ)*(q (e 1)-p (e 1))+
          (q (e 2)-p (e 2))| ≤ 10*Delta := by
      have hh := hband (e,z) (hmem z hz)
      have he : value rho (e,z) q-value rho (e,z) p=
          rho*(z.1:ℝ)*(q (e 0)-p (e 0))+rho*(z.2:ℝ)*(q (e 1)-p (e 1))+
            (q (e 2)-p (e 2)) := by dsimp [value,projection]; ring
      rwa [he] at hh
    have hh := expanded_rectangle_band T rho Delta (q (e 0)-p (e 0)) (q (e 1)-p (e 1))
      (q (e 2)-p (e 2)) (pointGap p q) hrho hrho1 hDelta (point_gap_chart_sum p q e)
      (hd2 _) (hd2 _) hg hb
    rw [hc] at hh
    nlinarith only [hh]
  have hh := weighted_fiber_count S Prod.fst (rho^2*max (pointGap p q) Delta) (5000*Delta) hf
  have he : (S.image Prod.fst).card ≤ 6 := by
    have hb := Finset.card_le_univ (S.image Prod.fst)
    simpa only [Fintype.card_perm,Fintype.card_fin,show Nat.factorial 3=6 by decide] using hb
  have heR : ((S.image Prod.fst).card : ℝ) ≤ 6 := by exact_mod_cast he
  have hm := mul_le_mul_of_nonneg_left heR (show 0 ≤ 5000*Delta by positivity)
  have hc : (S.card : ℝ)*rho^2*max (pointGap p q) Delta ≤ 30000*Delta := by nlinarith only [hh,hm]
  have hdist : distance3 p q ≤ 2*max (pointGap p q) Delta := by
    by_cases hd : 0 < distance3 p q
    · exact (separation_le_twice_gap p q (distance3 p q) hd le_rfl).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · exact (le_of_not_gt hd).trans (by positivity)
  have hdel : Delta ≤ 2*max (pointGap p q) Delta := by
    have hm := le_max_right (pointGap p q) Delta
    linarith only [hm,hDp]
  have ht := mul_le_mul_of_nonneg_left (max_le hdist hdel)
    (show 0 ≤ (S.card : ℝ)*rho^2 by positivity)
  nlinarith only [hc,ht]

end OriginalThreeDimensionalExpandedBandCount
