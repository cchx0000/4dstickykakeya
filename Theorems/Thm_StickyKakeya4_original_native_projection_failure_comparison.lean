import Theorems.Thm_StickyKakeya4_original_native_projection_bsg_core
import Theorems.Thm_StickyKakeya4_original_native_core_failure_obstruction
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalNativeProjectionFailureComparison
open ProjectionAnnulusEnergy GKZOriginalGapEnergy OriginalTwoProjectionCartesian
open OriginalTwoProjectionRealGraph OriginalProfiledThirdQueryFamily OriginalKaufmanSharedHost
open OriginalWeakAlphabetSelection OriginalFreshProjectionQueries OriginalRecodedAlphabetProfile
open OriginalNativeProjectionBSGCore OriginalNativeCoreFailureObstruction
open OriginalNativeStructuredPowerBounds

def originalAlphabetProfileCost (n : ℕ) (KP KC beta eps q N h M : ℝ) : ℝ :=
  max 1 (8*(1+stripConstant n KP (KC/beta) eps)*balanceLoss (q^3/8) N M (fiberBound h))

/-- Starting only from the ORIGINAL separated planar source, its point
profile, the original slope profile and literal failure of robust projection,
construct the actual transverse alphabets, original BSG core, fresh coefficient
family and fresh queries. The resulting inequality contains only explicit
native numerical budgets, with no supplied projected profile or graph density. -/
theorem exists_original_native_failure_comparison (u gap : ℝ)
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1) :
    ∃ epsilon eta delta0 : ℝ, 0<epsilon ∧ 0<eta ∧ 0<delta0 ∧ delta0≤1 ∧
      ∀ (P : Finset Point) (C : Finset ℝ) (n : ℕ)
        (KP KC mass q beta eps h M : ℝ),
        P.Nonempty → C.Nonempty → 1≤KP → 1≤KC → mass≤1 →
        0<q → 0<beta → beta≤1 → 0<eps → eps<1 → eps≤q^3/16 →
        0<h → h≤1 → mesh n≤h → 0<M →
        (∀ p∈P, |p.1|≤1 ∧ |p.2|≤1) → (∀ c∈C, |c|≤1) →
        (∀ p∈P, ∀ p'∈P, p≠p' → mesh n≤‖p-p'‖) →
        PointFrostman P (mesh n) KP u → ScalarFrostman C (mesh n) KC u →
        ((KC/beta)/(1-eps))*h^u≤q^3/16 → KC*h^u≤beta/4 →
        mass*(P.card:ℝ)≤originalRetention (q^3/16) P.card h M*M^2 →
        h*mesh n/64≤delta0 → M≤(h*mesh n/64)^(-1+gap) →
        originalAlphabetProfileCost n KP KC beta eps q P.card h M*(16/h)^u/
          originalRetention (q^3/16) P.card h M≤(h*mesh n/64)^(-eta) →
        (2*KC/beta)*(64/h^2)^u≤(h*mesh n/64)^(-eta) → 4/h^2≤(h*mesh n/64)^(-eta) →
        Failure P C mass q beta M (fun c Q => (alphabet Q (mesh n) c).card) →
        q*(originalDensity (q^3/16) P.card h M)^77*(h*mesh n/64)^(-epsilon) <
          (2:ℝ)^242*fiberBound h*(restrictedSumLoss h)^15*(12672/h^5) := by
  obtain ⟨epsilon,eta,delta0,hepsilon,heta,hd0,hd01,hcore⟩ :=
    exists_original_native_core_failure_obstruction u gap hu hu1 hgap hgap1
  refine ⟨epsilon,eta,delta0,hepsilon,heta,hd0,hd01,?_⟩
  intro P C n KP KC mass q beta eps h M hP hC hKP hKC hmass1 hq hbeta hbeta1
    heps heps1 hepsq hh hh1 hscale hM hPbox hCbox hsep hPprofile hCprofile
    hfirstbudget hfreshbudget hadmissible hsmall hcard hAbudget hDbudget hboxbudget hfailure
  let D0 := bad C P q M (fun c Q => (alphabet Q (mesh n) c).card)
  have hD0C : D0⊆C := original_bad_subset C P q M _
  have hD0mass : beta*(C.card:ℝ)≤D0.card := hfailure P (Finset.Subset.refl P)
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass1 (Nat.cast_nonneg P.card))
  have hD0non : D0.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hbeta (Nat.cast_pos.mpr hC.card_pos)).trans_le hD0mass))
  have hD0profile : ScalarFrostman D0 (mesh n) (KC/beta) u :=
    original_scalar_profile_restrict C D0 (mesh_pos n).le (show 0≤KC by linarith only [hKC])
      hbeta hD0C hD0mass hCprofile
  have hD0K : 1≤KC/beta := by
    apply (le_div_iff₀ hbeta).mpr
    linarith only [hbeta1,hKC]
  obtain ⟨Q,hQ⟩ := exists_original_bad_query_family C P q M
    (fun c Q => (alphabet Q (mesh n) c).card)
  have hQcover : ∀ c∈D0, ((realAlphabet (Q c) (mesh n) c).card:ℝ)≤M := by
    intro c hc
    rw [real_alphabet_card (Q c) (mesh_pos n)]
    exact (hQ c hc).2.2
  obtain ⟨a,haD,b,hbD,hab,C',hC'D,hC'mass,R,hRcommon,_hRmass,hthird,hRprofiles⟩ :=
    exists_original_profiled_third_queries P D0 Q n hP hD0non hKP hD0K hu.le hu1
      heps heps1 hq hM hepsq hh hscale hh1 hfirstbudget hPbox
      (fun c hc => hCbox c (hD0C hc)) hsep hPprofile hD0profile
      (fun c hc => (hQ c hc).1) (fun c hc => (hQ c hc).2.1) hQcover
  have hC'non : C'.Nonempty := by
    have hpos : 0<(q^3*(1-eps)/8)*(D0.card:ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hD0non.card_pos)
    exact Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le hC'mass))
  obtain ⟨c0,hc0C'⟩ := hC'non
  have hc0D := hC'D hc0C'
  have ha : |a|≤1 := hCbox a (hD0C haD)
  have hb : |b|≤1 := hCbox b (hD0C hbD)
  have hc0 : |c0|≤1 := hCbox c0 (hD0C hc0D)
  have hab' : h≤|b-a| := by simpa only [abs_sub_comm] using hab
  obtain ⟨h0a,h0b',hQ0mass⟩ := hthird c0 hc0C'
  have h0b : h≤|b-c0| := by simpa only [abs_sub_comm] using h0b'
  let Q0 := R∩Q c0
  have hRP : R⊆P := (hRcommon.trans Finset.inter_subset_left).trans (hQ a haD).1
  have hQ0R : Q0⊆R := Finset.inter_subset_left
  have hQ0cover : ((alphabet Q0 (mesh n) c0).card:ℝ)≤M :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
      (show Q0⊆Q c0 from Finset.inter_subset_right)))).trans (hQ c0 hc0D).2.2
  have hq0 : 0<q^3/16 := by positivity
  obtain ⟨A,B,hAsub,_hBsub,hAmass,hBmass,hsum,F,hFQ,hFret,hFG⟩ :=
    exists_original_native_bsg_core P R Q0 hP (mesh_pos n) hh hh1 hq0 hM
      hab' ha hb hc0 h0a h0b hsep hRP hQ0R hQ0mass
      (hRprofiles a (Or.inl rfl)).1 (hRprofiles b (Or.inr rfl)).1 hQ0cover
  let KA := originalAlphabetProfileCost n KP KC beta eps q P.card h M
  have hKA : 1≤KA := le_max_left _ _
  have hRprofile : ScalarFrostman (realAlphabet R (mesh n) a) (mesh n/4) KA u := by
    intro center r hr hr1
    have hp := (hRprofiles a (Or.inl rfl)).2 center r hr hr1
    exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_right (1:ℝ) _) (Real.rpow_nonneg ((div_nonneg (mesh_pos n).le (by norm_num) : 0 ≤ mesh n/4).trans hr) u))
      (Nat.cast_nonneg _))
  have hJ : 0<fiberBound h := by unfold fiberBound; positivity
  have hlam : 0<originalDensity (q^3/16) P.card h M := by
    unfold originalDensity
    exact div_pos (mul_pos hq0 (Nat.cast_pos.mpr hP.card_pos)) (mul_pos hJ (sq_pos_of_pos hM))
  have htheta : 0<originalRetention (q^3/16) P.card h M := by unfold originalRetention; positivity
  have hK : 0<536870912*(restrictedSumLoss h)^3/(originalDensity (q^3/16) P.card h M)^9 := by
    have hc : 0<restrictedSumLoss h := by unfold restrictedSumLoss; positivity
    positivity
  have hcomp := hcore P R F A B C (mesh n) h a b c0 mass q beta M
    (originalRetention (q^3/16) P.card h M)
    (536870912*(restrictedSumLoss h)^3/(originalDensity (q^3/16) P.card h M)^9) KA KC
    hC (mesh_pos n) hh hh1 hscale hq hbeta hbeta1 hM htheta hK hKA hKC
    hab' ha hb hc0 h0a h0b hCbox hsep hCprofile hfreshbudget hRprofile
    (hRprofiles a (Or.inl rfl)).1 hAsub hAmass hBmass hsum
    (hFQ.trans (hQ0R.trans hRP)) (hadmissible.trans hFret) hFret hFG
    hsmall hcard hAbudget hDbudget hboxbudget hfailure
  apply original_bsg_fixed_power_comparison hlam
  simpa only [originalRetention,div_div] using hcomp

end OriginalNativeProjectionFailureComparison
