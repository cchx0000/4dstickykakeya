import Theorems.Thm_StickyKakeya4_original_weak_alphabet_selection
import Theorems.Thm_StickyKakeya4_original_kaufman_shared_host
import Theorems.Thm_StickyKakeya4_original_native_transverse_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalProfiledThirdQueryFamily
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph
open OriginalWeakAlphabetSelection OriginalKaufmanSharedHost OriginalNativeTransverseQueries

lemma original_slope_profile_restrict (C D : Finset ℝ) {delta K u eps : ℝ}
    (hDC : D ⊆ C) (hd : 0 ≤ delta) (heps : eps < 1) (hK : 0 ≤ K)
    (hmass : (1-eps)*(C.card:ℝ) ≤ D.card)
    (hprofile : SlopeFrostman C delta K u) :
    SlopeFrostman D delta (K/(1-eps)) u := by
  intro c r hr hr1
  have hcoef : 0 ≤ K*r^u := mul_nonneg hK (Real.rpow_nonneg (hd.trans hr) _)
  have hc := (Nat.cast_le.mpr (Finset.card_le_card
    (Finset.filter_subset_filter (fun x => |x-c| ≤ r) hDC))).trans (hprofile c r hr hr1)
  have hp := mul_le_mul_of_nonneg_left hmass hcoef
  have hcomp : 0 < 1-eps := sub_pos.mpr heps
  apply (mul_le_mul_iff_left₀ hcomp).mp
  have hid : (K/(1-eps)*r^u*D.card)*(1-eps)=K*r^u*D.card := by field_simp
  rw [hid]
  have hc' := mul_le_mul_of_nonneg_left hc hcomp.le
  nlinarith only [hc',hp]

/-- Actual source profiles and all small original query covers construct
shared weak-profile scalar alphabets while retaining every selected third
query. No projected Frostman or post-pruning density premise is supplied. -/
theorem exists_original_profiled_third_queries
    (P : Finset Point) (C : Finset ℝ) (Q : ℝ → Finset Point) (n : ℕ)
    {KP KL u eps q h M : ℝ}
    (hPnon : P.Nonempty) (hCnon : C.Nonempty)
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (heps : 0 < eps) (heps1 : eps < 1) (hq : 0 < q) (hM : 0 < M)
    (hepsq : eps ≤ q^3/16) (hh : 0 < h) (hscale : mesh n ≤ h) (hh1 : h ≤ 1)
    (hbudget : (KL/(1-eps))*h^u ≤ q^3/16)
    (hP : ∀ p∈P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hC : ∀ lam∈C, |lam| ≤ 1)
    (hsep : ∀ p∈P, ∀ p'∈P, p≠p' → mesh n ≤ ‖p-p'‖)
    (hFP : PointFrostman P (mesh n) KP u)
    (hFL : SlopeFrostman C (mesh n) KL u)
    (hQ : ∀ c∈C, Q c ⊆ P)
    (hmass : ∀ c∈C, q*(P.card:ℝ) ≤ (Q c).card)
    (hcover : ∀ c∈C, ((realAlphabet (Q c) (mesh n) c).card:ℝ) ≤ M) :
    ∃ a∈C, ∃ b∈C, h ≤ |a-b| ∧ ∃ C' : Finset ℝ, C' ⊆ C ∧
      (q^3*(1-eps)/8)*(C.card:ℝ) ≤ C'.card ∧
      ∃ R : Finset Point, R ⊆ Q a ∩ Q b ∧
        (q^3/16)*(P.card:ℝ) ≤ R.card ∧
        (∀ c∈C', h ≤ |c-a| ∧ h ≤ |c-b| ∧
          (q^3/16)*(P.card:ℝ) ≤ (R∩Q c).card) ∧
        ∀ lam : ℝ, lam=a ∨ lam=b →
          ((realAlphabet R (mesh n) lam).card:ℝ) ≤ M ∧
          ∀ center r : ℝ, mesh n/4 ≤ r → r ≤ 1 →
            (((realAlphabet R (mesh n) lam).filter (fun x => |x-center| ≤ r)).card:ℝ) ≤
              (8*(1+stripConstant n KP KL eps)*
                balanceLoss (q^3/8) P.card M (fiberBound h))*
                r^u*(realAlphabet R (mesh n) lam).card := by
  have hKL0 : 0 ≤ KL := (by norm_num : (0:ℝ) ≤ 1).trans hKL
  have hcomp : 0 < 1-eps := sub_pos.mpr heps1
  have hN : 0 < (P.card:ℝ) := by exact_mod_cast hPnon.card_pos
  have hCpos : 0 < (C.card:ℝ) := by exact_mod_cast hCnon.card_pos
  obtain ⟨L,hLC,hLmass,hhost⟩ := exists_original_shared_profile_host P C n
    hPnon hKP hKL hu hu1 heps heps1 hP hC hFP hFL
  have hLnon : L.Nonempty := Finset.card_pos.mp (by
    have hp := (mul_pos hcomp hCpos).trans_le hLmass
    exact_mod_cast hp)
  have hFL' := original_slope_profile_restrict C L hLC (mesh_pos n).le heps1 hKL0 hLmass hFL
  obtain ⟨a,ha,b,hb,hab,D,hDL,hDmass,hP0P,hP0mass,hqueries⟩ :=
    exists_native_transverse_common_queries P L Q hPnon hLnon hq hscale hh1
      hFL' hbudget (fun c hc => hQ c (hLC hc)) (fun c hc => hmass c (hLC hc))
  let P0 := Q a∩Q b
  change (q^3/4)*(P.card:ℝ) ≤ (P0.card:ℝ) at hP0mass
  obtain ⟨S,hSP0,hSloss,hSprofile⟩ := hhost a ha b hb P0 hP0P
  let rho : ℝ := q^3/8
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hS : rho*(P.card:ℝ) ≤ S.card := by
    have hl := hSloss P0 Finset.Subset.rfl
    rw [Finset.inter_eq_right.mpr hSP0] at hl
    have he := mul_le_mul_of_nonneg_right hepsq hN.le
    dsimp [rho]
    nlinarith only [hl,hP0mass,he]
  have hScov : ∀ lam : ℝ, lam=a ∨ lam=b →
      ((realAlphabet S (mesh n) lam).card:ℝ) ≤ M := by
    intro lam hlam
    rcases hlam with rfl|rfl
    · rw [OriginalRichAlphabetProfile.realAlphabet_eq_image]
      exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
        (hSP0.trans Finset.inter_subset_left)))).trans
        (by simpa only [OriginalRichAlphabetProfile.realAlphabet_eq_image] using hcover lam (hLC ha))
    · rw [OriginalRichAlphabetProfile.realAlphabet_eq_image]
      exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
        (hSP0.trans Finset.inter_subset_right)))).trans
        (by simpa only [OriginalRichAlphabetProfile.realAlphabet_eq_image] using hcover lam (hLC hb))
  have hH : 0 ≤ stripConstant n KP KL eps := by
    unfold stripConstant
    positivity
  have hab' : h ≤ |b-a| := by simpa only [abs_sub_comm] using hab
  obtain ⟨R,hRS,hRmass,hRloss,hRprofile⟩ := exists_original_weak_alphabets P S
    (mesh_pos n) hh hh1 hab' (hC a (hLC ha)) hrho hM hH hu hu1
    hPnon (hSP0.trans hP0P) hS hsep hScov hSprofile
  have hDoriginal : (q^3*(1-eps)/8)*(C.card:ℝ) ≤ D.card := by
    have hh := mul_le_mul_of_nonneg_left hLmass (show 0 ≤ q^3/8 by positivity)
    nlinarith only [hh,hDmass]
  refine ⟨a,hLC ha,b,hLC hb,hab,D,hDL.trans hLC,hDoriginal,R,hRS.trans hSP0,?_,?_,?_⟩
  · dsimp [rho] at hRmass
    nlinarith only [hRmass]
  · intro c hc
    obtain ⟨hca,hcb,hQmass⟩ := hqueries c hc
    change (q^3/4)*(P.card:ℝ) ≤ ((P0∩Q c).card:ℝ) at hQmass
    refine ⟨hca,hcb,?_⟩
    have hl := hSloss (P0∩Q c) Finset.inter_subset_left
    have hr := hRloss ((P0∩Q c)∩S) Finset.inter_subset_right
    have hid : ((P0∩Q c)∩S)∩R=R∩Q c := by
      ext p
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨⟨_hp0,hpc⟩,_hpS⟩,hpR⟩
        exact ⟨hpR,hpc⟩
      · rintro ⟨hpR,hpc⟩
        exact ⟨⟨⟨hSP0 (hRS hpR),hpc⟩,hRS hpR⟩,hpR⟩
    rw [hid] at hr
    have he := mul_le_mul_of_nonneg_right hepsq hN.le
    dsimp [rho] at hr
    nlinarith only [hl,hr,hQmass,he]
  · intro lam hlam
    obtain ⟨hcard,_hbalance,hprof⟩ := hRprofile lam hlam
    exact ⟨hcard,hprof⟩

end OriginalProfiledThirdQueryFamily
