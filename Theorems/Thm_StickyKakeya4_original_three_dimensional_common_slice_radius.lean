import Theorems.Thm_StickyKakeya4_original_three_dimensional_large_slice_population
import Theorems.Thm_StickyKakeya4_original_three_dimensional_middle_slice_branch
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalCommonSliceRadius
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalPhysicalTubeScaleSelection
open OriginalThreeDimensionalLargeSlicePopulation OriginalThreeDimensionalMiddleSliceBranch

def chosenSliceIndex (P : Finset Point3) (z : Pair3) (k : DirectionLabel→ℤ)
    (rho D alpha : ℝ) (n : ℕ) (d : DirectionLabel) : ℕ :=
  Classical.choose (Finset.exists_max_image (Finset.range (n+1))
    (fun j => sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius j))
    ⟨0,Finset.mem_range.mpr (by omega)⟩)

theorem chosen_slice_index_spec (P : Finset Point3) (z : Pair3) (k : DirectionLabel→ℤ)
    (rho D alpha : ℝ) (n : ℕ) (d : DirectionLabel) :
    chosenSliceIndex P z k rho D alpha n d ≤ n ∧
      ∀ i ≤ n, sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius i) ≤
        sliceScore (enlargedSlice P rho d (k d) D) z alpha
          (dyadicRadius (chosenSliceIndex P z k rho D alpha n d)) := by
  have hs := Classical.choose_spec (Finset.exists_max_image (Finset.range (n+1))
    (fun j => sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius j))
    ⟨0,Finset.mem_range.mpr (by omega)⟩)
  change chosenSliceIndex P z k rho D alpha n d∈Finset.range (n+1) ∧ _ at hs
  refine ⟨by have hh := Finset.mem_range.mp hs.1; omega,?_⟩
  intro i hi
  exact hs.2 i (Finset.mem_range.mpr (by omega))

/-- Pigeonhole the actual original direction labels by their actual
maximizing radius. The selected fiber is whole and its true menu loss is
n+1, rather than an assumed retained-incidence budget. -/
theorem exists_original_common_slice_radius
    (P : Finset Point3) (z : Pair3) (F : Finset DirectionLabel) (k : DirectionLabel→ℤ)
    (rho D alpha : ℝ) (n : ℕ) (hF : F.Nonempty) :
    ∃ j : ℕ, j ≤ n ∧ ∃ S : Finset DirectionLabel,
      S=F.filter (fun d => chosenSliceIndex P z k rho D alpha n d=j) ∧
      S⊆F ∧ S.Nonempty ∧ F.card ≤ (n+1)*S.card ∧
      ∀ d∈S, ∀ i ≤ n, sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius i) ≤
        sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius j) := by
  let f := chosenSliceIndex P z k rho D alpha n
  have hf : ∀ d∈F, f d∈Finset.range (n+1) := by
    intro d _hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (chosen_slice_index_spec P z k rho D alpha n d).1)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range (n+1))
    (fun i => (F.filter (fun d => f d=i)).card) ⟨0,Finset.mem_range.mpr (by omega)⟩
  let S := F.filter (fun d => f d=j)
  have hsum : ∑ i∈Finset.range (n+1), (F.filter (fun d => f d=i)).card=F.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hf
  have hmass : F.card ≤ (n+1)*S.card := by
    calc
      _ = ∑ i∈Finset.range (n+1), (F.filter (fun d => f d=i)).card := hsum.symm
      _ ≤ ∑ _i∈Finset.range (n+1), S.card := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  have hSn : S.Nonempty := by
    apply Finset.card_pos.mp
    have hh := hF.card_pos
    by_contra hn
    have hz : S.card=0 := by omega
    rw [hz,mul_zero] at hmass
    omega
  refine ⟨j,by have hh := Finset.mem_range.mp hj; omega,S,rfl,Finset.filter_subset _ _,hSn,hmass,?_⟩
  intro d hd i hi
  have he := (Finset.mem_filter.mp hd).2
  have hh := (chosen_slice_index_spec P z k rho D alpha n d).2 i hi
  change f d=j at he
  change _ ≤ sliceScore _ _ _ (dyadicRadius (f d)) at hh
  simpa only [he] using hh

/-- A genuine finite concentrated direction family yields one common
physical radius and an actual original tube population. Its observed
cardinality and the exact n+1 direction-menu denominator are retained.
No discarded-pair budget or hairbrush conclusion is supplied. -/
theorem exists_original_concentrated_direction_radius
    (P : Finset Point3) (z : Pair3) (F : Finset DirectionLabel) (k : DirectionLabel→ℤ)
    (rho r eta1 e1 e2 : ℝ) (n M : ℕ)
    (hrho : 0 < rho) (hr : 0 < r) (hr1 : r ≤ 1) (he1 : 0 < e1) (he11 : e1 ≤ 1)
    (he2 : 0 < e2) (halpha : 200*e2/e1 ≤ 1) (hmesh : rho=dyadicRadius n)
    (hcontract : (dyadicRadius M)^(200*e2/e1) ≤ 1/2) (hDelta : 54*rho/r ≤ 1)
    (hbox : ∀ p∈P, ∀ i, |p i| ≤ 1) (hzP : z∈P.product P) (hsep : r ≤ distance3 z.1 z.2)
    (hF : F.Nonempty) (hband : F⊆pairBand rho z.1 z.2)
    (hslabs : ∀ d∈F, z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d))
    (hheavy : ∀ d∈F, rho^(1+eta1)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card)
    (hconc : ∀ d∈F, (54*rho/r)^e2*((enlargedSlice P rho d (k d) (54*rho/r)).card : ℝ) ≤
      (physicalPairTube3 (enlargedSlice P rho d (k d) (54*rho/r)) ((54*rho/r)^e1) z).card) :
    let D := 54*rho/r
    let alpha := 200*e2/e1
    let beta := min 1 ((F.card : ℝ)*rho/(n+1))
    let nu := beta*(dyadicRadius M*r^2/4665600000*rho^eta1*D^(e2+alpha*(1-e1)))
    0 < nu ∧ ∃ j : ℕ, j ≤ n ∧ ∃ S : Finset DirectionLabel,
      S=F.filter (fun d => chosenSliceIndex P z k rho D alpha n d=j) ∧
      S⊆F ∧ S.Nonempty ∧ F.card ≤ (n+1)*S.card ∧
      (∀ d∈S, ∀ i ≤ n, sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius i) ≤
        sliceScore (enlargedSlice P rho d (k d) D) z alpha (dyadicRadius j)) ∧
      nu*dyadicRadius j*P.card ≤ (physicalPairTube3 P (dyadicRadius j) z).card := by
  let D := 54*rho/r
  let alpha := 200*e2/e1
  let c := dyadicRadius M
  let E := e2+alpha*(1-e1)
  let beta := min 1 ((F.card : ℝ)*rho/(n+1))
  let B := c*r^2/4665600000*rho^eta1*D^E
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c,dyadicRadius]; positivity
  have hc1 : c ≤ 1 := by dsimp [c,dyadicRadius]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hN : 0 < (n:ℝ)+1 := by positivity
  have hFpos : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨mul_pos hbeta hB,?_⟩
  obtain ⟨j,hj,S,hSeq,hSF,hSn,hmass,hmax⟩ := exists_original_common_slice_radius P z F k rho D alpha n hF
  refine ⟨j,hj,S,hSeq,hSF,hSn,hmass,hmax,?_⟩
  have htau : 0 < dyadicRadius j := by dsimp [dyadicRadius]; positivity
  have hbeta1 : beta ≤ 1 := min_le_left _ _
  have hbetamass : beta ≤ (S.card : ℝ)*rho := by
    have hh : (F.card : ℝ) ≤ ((n:ℝ)+1)*S.card := by exact_mod_cast hmass
    have hmul := mul_le_mul_of_nonneg_right hh hrho.le
    have hq : (F.card : ℝ)*rho/((n:ℝ)+1) ≤ (S.card : ℝ)*rho := by
      apply (div_le_iff₀ hN).mpr
      nlinarith only [hmul]
    exact (min_le_right _ _).trans hq
  by_cases hsmall : dyadicRadius j ≤ (300/c)*D
  · obtain ⟨d,hd⟩ := hSn
    have hL : 1 ≤ 300/c := by
      apply (le_div_iff₀ hc).mpr
      linarith only [hc1]
    have hmid := original_selected_middle_slice_population P z rho r eta1 e1 e2 (300/c) d (k d) n j
      hrho hr hr1 he1 he11 he2 halpha hL hmesh hDelta (hheavy d (hSF hd)) (hconc d (hSF hd))
      (hmax d hd) hsmall
    have hscalar : B ≤ r^2/(108*(300/c))*rho^eta1*D^E := by
      have he : r^2/(108*(300/c))*rho^eta1*D^E=c*r^2/32400*rho^eta1*D^E := by field_simp; norm_num
      rw [he]
      dsimp [B]
      have hh := mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)/4665600000 ≤ 1/32400)
        (show 0 ≤ c*r^2*rho^eta1*D^E by positivity)
      nlinarith only [hh]
    have hcoef : beta*B ≤ r^2/(108*(300/c))*rho^eta1*D^E :=
      (mul_le_mul_of_nonneg_right hbeta1 hB.le).trans (by simpa only [one_mul] using hscalar)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef htau.le) (Nat.cast_nonneg P.card)
    exact hh.trans hmid
  · have hlarge : 300*D/c ≤ dyadicRadius j := by
      have hh := le_of_not_ge hsmall
      have he : 300*D/c=(300/c)*D := by ring
      rw [he]
      exact hh
    have hlargepop := original_large_common_slice_population P z S k rho r eta1 e1 e2 n M j
      hrho hr hr1 he1 he11 he2 halpha hmesh hcontract hDelta hlarge hbox hzP hsep
      (hSF.trans hband) (fun d hd => hslabs d (hSF hd)) (fun d hd => hheavy d (hSF hd))
      (fun d hd => hconc d (hSF hd)) hmax
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbetamass hB.le) htau.le) (Nat.cast_nonneg P.card)
    exact hh.trans hlargepop

end OriginalThreeDimensionalCommonSliceRadius
