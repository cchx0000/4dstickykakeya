import Theorems.Thm_StickyKakeya4_original_rich_alphabet_profile
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace OriginalWeakAlphabetSelection
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalTwoProjectionRealGraph
open OriginalSharedFiberPruning OriginalRichAlphabetProfile

/-- The threshold is chosen from original source mass and actual projection
cover bounds. The same source pruning is used for every third query. -/
def fiberThreshold (rho N M : ℝ) : ℝ := rho*N/(4*M)
def balanceLoss (rho N M D : ℝ) : ℝ := 8*D*M^2/(rho^2*N)

lemma balanceLoss_mul_threshold {rho N M D : ℝ}
    (hrho : 0 < rho) (hN : 0 < N) (hM : 0 < M) :
    balanceLoss rho N M D*fiberThreshold rho N M=2*D*M/rho := by
  unfold balanceLoss fiberThreshold
  field_simp
  ring

/-- The opposite alphabet's actual cover bound and the original pair-code
packing bound force a lower population in each surviving alphabet. -/
lemma alphabet_balance {rho N M D R A B : ℝ}
    (hrho : 0 < rho) (hN : 0 < N) (hM : 0 < M)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : B ≤ M)
    (hret : rho*N/2 ≤ R) (hpair : R ≤ D*A*B) :
    N ≤ balanceLoss rho N M D*fiberThreshold rho N M*A := by
  rw [balanceLoss_mul_threshold hrho hN hM]
  have hupper := mul_le_mul_of_nonneg_left hB (mul_nonneg hD hA)
  apply (mul_le_mul_iff_left₀ hrho).mp
  have hid : (2*D*M/rho*A)*rho=2*D*A*M := by field_simp
  rw [hid]
  nlinarith only [hret,hpair,hupper]

/-- From two actual original strip profiles and small original projection
covers, construct shared scalar alphabets with a genuine unweighted weak
profile. Every original query loses at most half the prescribed original mass. -/
theorem exists_original_weak_alphabets (P S : Finset Point)
    {delta h lam0 lam1 rho M H u : ℝ}
    (hd : 0 < delta) (hh : 0 < h) (hh1 : h ≤ 1)
    (htrans : h ≤ |lam1-lam0|) (h0 : |lam0| ≤ 1)
    (hrho : 0 < rho) (hM : 0 < M) (hH : 0 ≤ H) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hPnon : P.Nonempty) (hSP : S ⊆ P)
    (hS : rho*(P.card:ℝ) ≤ S.card)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p≠q → delta ≤ ‖p-q‖)
    (hcover : ∀ lam : ℝ, lam=lam0 ∨ lam=lam1 →
      ((realAlphabet S delta lam).card:ℝ) ≤ M)
    (hprofile : ∀ lam : ℝ, lam=lam0 ∨ lam=lam1 →
      ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
        ((S.filter (fun p => |projection lam p-c| ≤ r)).card:ℝ) ≤ H*r^u*P.card) :
    ∃ R : Finset Point, R ⊆ S ∧ rho*(P.card:ℝ)/2 ≤ R.card ∧
      (∀ Q : Finset Point, Q ⊆ S →
        (Q.card:ℝ) ≤ (Q∩R).card+rho*(P.card:ℝ)/2) ∧
      (∀ lam : ℝ, lam=lam0 ∨ lam=lam1 →
        ((realAlphabet R delta lam).card:ℝ) ≤ M ∧
        (P.card:ℝ) ≤ balanceLoss rho P.card M (fiberBound h)*
          fiberThreshold rho P.card M*(realAlphabet R delta lam).card ∧
        ∀ c r : ℝ, delta/4 ≤ r → r ≤ 1 →
          (((realAlphabet R delta lam).filter (fun a => |a-c| ≤ r)).card:ℝ) ≤
            (8*(1+H)*balanceLoss rho P.card M (fiberBound h))*
              r^u*(realAlphabet R delta lam).card) := by
  let N : ℝ := P.card
  let m := fiberThreshold rho N M
  let f := scalarValue delta lam0
  let g := scalarValue delta lam1
  let R := rich S f m ∩ rich S g m
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hPnon.card_pos
  have hm : 0 < m := by dsimp [m,fiberThreshold]; positivity
  have hRS : R ⊆ S := Finset.inter_subset_left.trans (rich_subset S f m)
  have hRP : R ⊆ P := hRS.trans hSP
  have hf : ((S.image f).card:ℝ) ≤ M := by
    simpa only [realAlphabet_eq_image] using hcover lam0 (Or.inl rfl)
  have hg : ((S.image g).card:ℝ) ≤ M := by
    simpa only [realAlphabet_eq_image] using hcover lam1 (Or.inr rfl)
  have hscale : m*(2*M)=rho*N/2 := by
    dsimp [m,fiberThreshold]
    field_simp
    ring
  have hbudget : m*((S.image f).card+(S.image g).card) ≤ rho*N/2 := by
    have hb := mul_le_mul_of_nonneg_left (add_le_add hf hg) hm.le
    nlinarith only [hb,hscale]
  have hquery : ∀ Q : Finset Point, Q ⊆ S →
      (Q.card:ℝ) ≤ (Q∩R).card+rho*N/2 := by
    intro Q hQS
    have hq := original_two_fiber_query_retention S Q f g hm.le hQS
    change (Q.card:ℝ) ≤ (Q∩R).card+_ at hq
    exact hq.trans (add_le_add (le_refl _) hbudget)
  have hret : rho*N/2 ≤ (R.card:ℝ) := by
    have hb := hquery S Finset.Subset.rfl
    rw [Finset.inter_eq_right.mpr hRS] at hb
    change rho*N ≤ (S.card:ℝ) at hS
    linarith only [hb,hS]
  have hD : 0 ≤ fiberBound h := sq_nonneg _
  have hL : 0 ≤ balanceLoss rho N M (fiberBound h) := by
    unfold balanceLoss
    positivity
  have hupper : ∀ lam : ℝ, lam=lam0 ∨ lam=lam1 →
      ((realAlphabet R delta lam).card:ℝ) ≤ M := by
    intro lam hlam
    rw [realAlphabet_eq_image]
    exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRS))).trans
      (by simpa only [realAlphabet_eq_image] using hcover lam hlam)
  have hpair : (R.card:ℝ) ≤ fiberBound h*
      (realAlphabet R delta lam0).card*(realAlphabet R delta lam1).card := by
    have hp := original_query_graph_mass P hd hh hh1 htrans h0 hsep R hRP
    rw [← real_graph_card R hd] at hp
    have hcN := Finset.card_le_card (real_graph_subset_product R delta lam0 lam1)
    rw [Finset.product_eq_sprod,Finset.card_product] at hcN
    have hc : ((realGraph R delta lam0 lam1).card:ℝ) ≤
        (realAlphabet R delta lam0).card*(realAlphabet R delta lam1).card := by
      exact_mod_cast hcN
    exact hp.trans (by nlinarith only [mul_le_mul_of_nonneg_left hc hD])
  have hbalance : ∀ lam : ℝ, lam=lam0 ∨ lam=lam1 →
      N ≤ balanceLoss rho N M (fiberBound h)*m*(realAlphabet R delta lam).card := by
    intro lam hlam
    rcases hlam with rfl|rfl
    · exact alphabet_balance hrho hN hM hD (Nat.cast_nonneg _)
        (hupper lam1 (Or.inr rfl)) hret hpair
    · apply alphabet_balance hrho hN hM hD (Nat.cast_nonneg _)
        (hupper lam0 (Or.inl rfl)) hret
      nlinarith only [hpair]
  refine ⟨R,hRS,hret,hquery,?_⟩
  intro lam hlam
  refine ⟨hupper lam hlam,hbalance lam hlam,?_⟩
  apply original_rich_alphabet_profile S R hd hH hu hu1 hN.le hm hL
    (Nat.cast_le.mpr (Finset.card_le_card hSP)) (hprofile lam hlam)
  · rcases hlam with rfl|rfl
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
  · exact hbalance lam hlam

end OriginalWeakAlphabetSelection
