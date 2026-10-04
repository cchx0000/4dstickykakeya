import Theorems.Thm_StickyKakeya4_original_source_edge_bsg
import Theorems.Thm_StickyKakeya4_original_native_recoded_query_cover
import Theorems.Thm_StickyKakeya4_original_native_transverse_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalNativeProjectionBSGCore
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph
open OriginalAffineAlphabetRecode OriginalNativeProjectionRecode OriginalNativeRecodedQueryCover
open OriginalSourceEdgeBSG

def restrictedSumLoss (h : ℝ) : ℝ := 10*(64/h^2+2)*(8/h+4)
def originalDensity (q N h M : ℝ) : ℝ := q*N/(fiberBound h*M^2)
def originalRetention (q N h M : ℝ) : ℝ := (originalDensity q N h M)^4/4096

/-- A genuine original third query produces a structured rectangle and
an original point core. Its graph density comes from native separated
point fibers, and its restricted sumset from the original projection cover. -/
theorem exists_original_native_bsg_core (P R Q0 : Finset Point)
    {delta h a b c0 q M : ℝ}
    (hP : P.Nonempty) (hd : 0<delta) (hh : 0<h) (hh1 : h≤1)
    (hq : 0<q) (hM : 0<M)
    (hab : h≤|b-a|) (ha : |a|≤1) (hb : |b|≤1) (hc0 : |c0|≤1)
    (h0a : h≤|c0-a|) (h0b : h≤|b-c0|)
    (hsep : ∀ p∈P, ∀ p'∈P, p≠p' → delta≤‖p-p'‖)
    (hRP : R⊆P) (hQ0R : Q0⊆R) (hQ0mass : q*(P.card:ℝ)≤Q0.card)
    (hA : ((realAlphabet R delta a).card:ℝ)≤M)
    (hB : ((realAlphabet R delta b).card:ℝ)≤M)
    (hcover : ((alphabet Q0 delta c0).card:ℝ)≤M) :
    ∃ A B : Finset ℤ,
      A⊆labels (realAlphabet R delta a) (h*delta/64) (leftWeight a b c0) ∧
      B⊆labels (realAlphabet R delta b) (h*delta/64) (rightWeight a b c0) ∧
      originalRetention q P.card h M*M≤(A.card:ℝ) ∧
      originalRetention q P.card h M*M≤(B.card:ℝ) ∧
      ((A+B).card:ℝ)≤(536870912*(restrictedSumLoss h)^3/(originalDensity q P.card h M)^9)*M ∧
      ∃ F : Finset Point, F⊆Q0 ∧ originalRetention q P.card h M*M^2≤(F.card:ℝ) ∧
        sourceGraph F delta (h*delta/64) a b (leftWeight a b c0) (rightWeight a b c0)⊆A.product B := by
  let sigma := h*delta/64
  let wa := leftWeight a b c0
  let wb := rightWeight a b c0
  let A0 := labels (realAlphabet R delta a) sigma wa
  let B0 := labels (realAlphabet R delta b) sigma wb
  let e := sourceCode delta sigma a b wa wb
  have hs : 0<sigma := by dsimp [sigma]; positivity
  have hweights := OriginalNativeTransverseQueries.weights_lower_of_three_transverse hh
    (by simpa only [abs_sub_comm] using hab) h0a (by simpa only [abs_sub_comm] using h0b) ha hb
  have hsa := original_transverse_recode_scale hd hh hweights.1
  have hsb := original_transverse_recode_scale hd hh hweights.2
  have hA0 : (A0.card:ℝ)≤M := by
    dsimp only [A0]
    rw [original_labels_card (realAlphabet R delta a) (by positivity : 0<delta/4)
      hs hsa (real_alphabet_separated R hd)]
    exact hA
  have hB0 : (B0.card:ℝ)≤M := by
    dsimp only [B0]
    rw [original_labels_card (realAlphabet R delta b) (by positivity : 0<delta/4)
      hs hsb (real_alphabet_separated R hd)]
    exact hB
  have hE : Q0.image e⊆A0.product B0 := original_source_graph_subset R Q0 delta sigma a b wa wb hQ0R
  have hcap : ∀ z∈Q0.image e, ((Q0.filter (fun p => e p=z)).card:ℝ)≤fiberBound h := by
    intro z hz
    exact original_source_code_fiber Q0 hd hs hh hh1 hab ha hsa hsb
      (fun p hp p' hp' hne => hsep p (hRP (hQ0R hp)) p' (hRP (hQ0R hp')) hne) hz
  have hJ : 0<fiberBound h := by unfold fiberBound; positivity
  have hK : 0<restrictedSumLoss h := by unfold restrictedSumLoss; positivity
  have hsum : (((Q0.image e).image (fun z => z.1+z.2)).card:ℝ)≤restrictedSumLoss h*M :=
    (original_native_restricted_sum_cover Q0 hd hh hab ha hb hc0 h0a h0b).trans
      (mul_le_mul_of_nonneg_left hcover hK.le)
  obtain ⟨A,B,hAA,hBB,hAc,hBc,hfull,F,_hFdef,hFQ,hFmass,_hFim,hqueries⟩ :=
    exists_original_source_edge_bsg Q0 e A0 B0 q P.card (fiberBound h) M (restrictedSumLoss h)
      hq (Nat.cast_pos.mpr hP.card_pos) hJ hM hK hQ0mass hA0 hB0 hE hcap hsum
  exact ⟨A,B,hAA,hBB,hAc,hBc,hfull,F,hFQ,hFmass,hqueries F (Finset.Subset.refl F)⟩

end OriginalNativeProjectionBSGCore
