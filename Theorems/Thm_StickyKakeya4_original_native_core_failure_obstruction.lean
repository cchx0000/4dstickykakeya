import Theorems.Thm_StickyKakeya4_original_native_structured_power_bounds
import Theorems.Thm_StickyKakeya4_original_recoded_alphabet_profile
import Theorems.Thm_StickyKakeya4_original_fresh_projection_queries
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalNativeCoreFailureObstruction
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph
open OriginalAffineAlphabetRecode OriginalRecodedAlphabetProfile OriginalNativeProjectionRecode
open OriginalNativeRecodedQueryCover OriginalNativeStructuredPowerBounds
open OriginalFreshProjectionQueries OriginalNormalizedFractionalCoefficientProfile
open IntegerBinRealNearEnergy GKZOriginalGapEnergy OriginalStructuredGraphGrowth

/-- A genuine BSG subalphabet inherits its profile from the actual
original rich projection alphabet, including the smaller-mesh cost. -/
theorem original_native_core_profile (R : Finset Point) (A : Finset ℤ)
    {delta h a w K u theta M : ℝ}
    (hd : 0<delta) (hh : 0<h) (hK : 1≤K) (hu : 0≤u) (htheta : 0<theta)
    (hw : h/2≤|w|)
    (hAsub : A⊆labels (realAlphabet R delta a) (h*delta/64) w)
    (hAmass : theta*M≤A.card) (hambient : ((realAlphabet R delta a).card:ℝ)≤M)
    (hprofile : ScalarFrostman (realAlphabet R delta a) (delta/4) K u) :
    ScalarFrostman (realGrid (h*delta/64) A) (h*delta/64) (K*(16/h)^u/theta) u := by
  have hs : 0<h*delta/64 := by positivity
  have hscale := original_transverse_recode_scale hd hh hw
  have hp := original_transverse_weighted_profile (realAlphabet R delta a) hd hh hK hu hw
    (real_alphabet_separated R hd) hprofile
  have hsub : realGrid (h*delta/64) A⊆realLabels (realAlphabet R delta a) (h*delta/64) w :=
    Finset.image_subset_image hAsub
  have hmass : theta*((realLabels (realAlphabet R delta a) (h*delta/64) w).card:ℝ)≤
      (realGrid (h*delta/64) A).card := by
    rw [original_real_labels_card (realAlphabet R delta a) (by positivity : 0<delta/4)
      hs hscale (real_alphabet_separated R hd),real_grid_card hs]
    exact (mul_le_mul_of_nonneg_left hambient htheta.le).trans hAmass
  exact original_scalar_profile_restrict _ _ hs.le (by positivity) htheta hsub hmass hp

/-- The nested-source failure hypothesis is tested on an actual retained
original core. Fresh original directions and queries are constructed inside
that core; the genuine scalar theorem then forces an explicit finite
inequality. No old third-query intersection is assumed to survive BSG. -/
theorem exists_original_native_core_failure_obstruction (u gap : ℝ)
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1) :
    ∃ epsilon eta delta0 : ℝ, 0<epsilon ∧ 0<eta ∧ 0<delta0 ∧ delta0≤1 ∧
      ∀ (P R F : Finset Point) (A B : Finset ℤ) (C : Finset ℝ)
        (delta h a b c0 mass q beta M theta K KA KC : ℝ),
        C.Nonempty → 0<delta → 0<h → h≤1 → delta≤h →
        0<q → 0<beta → beta≤1 → 0<M → 0<theta → 0<K → 1≤KA → 1≤KC →
        h≤|b-a| → |a|≤1 → |b|≤1 → |c0|≤1 → h≤|c0-a| → h≤|b-c0| →
        (∀ c∈C, |c|≤1) →
        (∀ p∈P, ∀ p'∈P, p≠p' → delta≤‖p-p'‖) →
        ScalarFrostman C delta KC u → KC*h^u≤beta/4 →
        ScalarFrostman (realAlphabet R delta a) (delta/4) KA u →
        ((realAlphabet R delta a).card:ℝ)≤M →
        A⊆labels (realAlphabet R delta a) (h*delta/64) (leftWeight a b c0) →
        theta*M≤A.card → theta*M≤B.card → ((A+B).card:ℝ)≤K*M →
        F⊆P → mass*(P.card:ℝ)≤F.card → theta*M^2≤F.card →
        sourceGraph F delta (h*delta/64) a b (leftWeight a b c0) (rightWeight a b c0)⊆A.product B →
        h*delta/64≤delta0 → M≤(h*delta/64)^(-1+gap) →
        KA*(16/h)^u/theta≤(h*delta/64)^(-eta) →
        (2*KC/beta)*(64/h^2)^u≤(h*delta/64)^(-eta) → 4/h^2≤(h*delta/64)^(-eta) →
        Failure P C mass q beta M (fun c Q => (alphabet Q delta c).card) →
        q*theta^3*(h*delta/64)^(-epsilon) <
          2*fiberBound h*(K/theta)^5*(12672/h^5) := by
  obtain ⟨epsilon,eta,delta0,heps,heta,hd0,hd01,hgrowth⟩ :=
    exists_original_structured_graph_growth u gap hu hu1 hgap hgap1
  refine ⟨epsilon,eta,delta0,heps,heta,hd0,hd01,?_⟩
  intro P R F A B C delta h a b c0 mass q beta M theta K KA KC hC hd hh hh1 hdh
    hq hbeta hbeta1 hM htheta hK hKA hKC hab ha hb hc0 h0a h0b hCbox hsep
    hCprofile hbudget hRprofile hRcard hAsub hAmass hBmass hsum hFP hFmass hFret hFG
    hsmall hcard hAbudget hDbudget hboxbudget hfailure
  let sigma := h*delta/64
  have hs : 0<sigma := by dsimp [sigma]; positivity
  have hwa : h/2≤|leftWeight a b c0| :=
    (OriginalNativeTransverseQueries.weights_lower_of_three_transverse hh
      (by simpa only [abs_sub_comm] using hab) h0a
      (by simpa only [abs_sub_comm] using h0b) ha hb).1
  have hwb : h/2≤|rightWeight a b c0| :=
    (OriginalNativeTransverseQueries.weights_lower_of_three_transverse hh
      (by simpa only [abs_sub_comm] using hab) h0a
      (by simpa only [abs_sub_comm] using h0b) ha hb).2
  have hsa := original_transverse_recode_scale hd hh hwa
  have hsb := original_transverse_recode_scale hd hh hwb
  have hAc : (A.card:ℝ)≤M := by
    have hc : (A.card:ℝ)≤(labels (realAlphabet R delta a) (h*delta/64) (leftWeight a b c0)).card :=
      Nat.cast_le.mpr (Finset.card_le_card hAsub)
    rw [original_labels_card (realAlphabet R delta a) (by positivity : 0<delta/4) hs
      hsa (real_alphabet_separated R hd)] at hc
    exact hc.trans hRcard
  have hApos : (0:ℝ)<A.card := (mul_pos htheta hM).trans_le hAmass
  have hAnon : A.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hApos)
  have hAprof0 := original_native_core_profile R A hd hh hKA hu.le htheta hwa
    hAsub hAmass hRcard hRprofile
  have hAprof : ScalarFrostman (realGrid sigma A) sigma (sigma^(-eta)) u := by
    intro center r hr hr1
    exact (hAprof0 center r hr hr1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAbudget
        (Real.rpow_nonneg (hs.le.trans hr) u)) (Nat.cast_nonneg _))
  obtain ⟨D,hDC,hDnon,_hDmass,hDprof,Q,hQ⟩ := exists_fresh_original_transverse_queries
    P F C (fun c Q => (alphabet Q delta c).card) (a:=a) (b:=b) hC hd.le
    (show 0≤KC by linarith only [hKC]) hbeta hdh hh1 hbudget hCprofile hfailure hFP hFmass
  have hKfresh : 1≤2*KC/beta := by
    apply (le_div_iff₀ hbeta).mpr
    nlinarith only [hKC,hbeta1]
  obtain ⟨_hDcard,hDrange,hDprofile⟩ := original_normalized_coefficient_image_profile D
    a b c0 h delta (2*KC/beta) u hh hh1 hd hKfresh hu.le ha hb hc0
    (by simpa only [abs_sub_comm] using hab) h0a h0b
    (fun c hc => hCbox c (hDC hc))
    (fun c hc => by simpa only [abs_sub_comm] using (hQ c hc).2.1) hDprof
  have hDprof' : ScalarFrostman (D.image (normalizedCoefficient a b c0)) sigma (sigma^(-eta)) u := by
    intro center r hr hr1
    exact (hDprofile center r hr hr1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDbudget
        (Real.rpow_nonneg (hs.le.trans hr) u)) (Nat.cast_nonneg _))
  have hsum' : ((A+B).card:ℝ)≤(K/theta)*A.card := by
    apply hsum.trans
    have hm := mul_le_mul_of_nonneg_left hAmass (show 0≤K/theta by positivity)
    have he : (K/theta)*(theta*M)=K*M := by field_simp
    rwa [he] at hm
  obtain ⟨x,hx,hgrow⟩ := hgrowth A B (D.image (normalizedCoefficient a b c0)) sigma
    (K/theta) theta hAnon (hDnon.image _) hs hsmall (by positivity) htheta
    ((mul_le_mul_of_nonneg_left hAc htheta.le).trans hBmass) hsum'
    (hAc.trans hcard) hAprof hDprof' (fun x hx => (hDrange x hx).trans hboxbudget)
  obtain ⟨c,hc,hcx⟩ := Finset.mem_image.mp hx
  have hproperties := hQ c hc
  have hQF := hproperties.2.2.1
  have hQmass := hproperties.2.2.2.1
  have hQcover := hproperties.2.2.2.2
  have hFpos : (0:ℝ)<F.card := (show 0<theta*M^2 by positivity).trans_le hFret
  have hQpos : (0:ℝ)<(Q c).card := (mul_pos hq hFpos).trans_le hQmass
  have hQnon : (Q c).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hQpos)
  let G := sourceGraph (Q c) delta sigma a b (leftWeight a b c0) (rightWeight a b c0)
  have hGsub : G⊆A.product B := (Finset.image_subset_image hQF).trans hFG
  have hGnon : G.Nonempty := hQnon.image _
  have hgain := hgrow G hGsub hGnon
  have hmass := original_source_query_mass P (Q c) hd hs hh hh1 hab ha hsa hsb hsep (hQF.trans hFP)
  have hnear := original_native_recoded_query_cover (Q c) hd hh hab ha hb hc0 (hCbox c (hDC hc))
    h0a h0b (by simpa only [abs_sub_comm] using hproperties.2.1)
  rw [hcx] at hnear
  have hLoss := (original_geometric_cover_power_bounds hh hh1 (hDrange x hx)).2.2
  have hcover : ((G.image (OriginalBourgainGraphTransfer.code x)).card:ℝ)≤(12672/h^5)*M := by
    apply hnear.trans
    exact mul_le_mul hLoss hQcover (Nat.cast_nonneg _) (by positivity)
  have hcount : q*theta*M^2≤fiberBound h*(G.card:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hFret hq.le
    nlinarith only [hm,hQmass,hmass]
  have hJ : 0<fiberBound h := by unfold fiberBound; positivity
  have hleft := mul_le_mul_of_nonneg_right hcount
    (show 0≤theta^2*sigma^(-epsilon) by positivity)
  have hupper := mul_le_mul hAc hcover (Nat.cast_nonneg _) hM.le
  have hright := mul_le_mul_of_nonneg_left hupper (show 0≤2*(K/theta)^5 by positivity)
  have hgainJ := mul_lt_mul_of_pos_left hgain hJ
  have hrightJ := mul_le_mul_of_nonneg_left hright hJ.le
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hM)).mp
  nlinarith only [hleft,hgainJ,hrightJ]

end OriginalNativeCoreFailureObstruction
