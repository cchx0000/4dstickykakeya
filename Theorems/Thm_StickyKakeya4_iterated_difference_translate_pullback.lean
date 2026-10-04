import Theorems.Thm_StickyKakeya4_original_difference_translate_pullback

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped BigOperators

noncomputable section

namespace IteratedDifferenceTranslatePullback

open OriginalDifferenceTranslatePullback

/-- Backward original-fiber averaging over an actual finite difference chain.
Only the displayed sigma factors multiply; the terminal beta occurs once. -/
theorem pullback_chain
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (J : ℕ) (B : ℕ → Finset G) (E : ℕ → Finset (G × G))
    (L sigma : ℕ → ℝ) (H : Finset G)
    (hB : ∀ i ≤ J, (B i).Nonempty)
    (hE : ∀ i < J, E i ⊆ (B i).product (B i))
    (himage : ∀ i < J, (E i).image difference = B (i + 1))
    (hL : ∀ i < J, 0 ≤ L i)
    (hsigma : ∀ i < J, 0 ≤ sigma i)
    (hfiber : ∀ i < J, ∀ d ∈ (E i).image difference,
      L i ≤ (((E i).filter (fun p => difference p = d)).card : ℝ))
    (hscale : ∀ i < J, sigma i * ((B i).card : ℝ) ^ 2 ≤
      L i * (B (i + 1)).card)
    (beta : ℝ) (hbeta : 0 ≤ beta) (x : G)
    (hcapture : beta * ((B J).card : ℝ) ≤ (translatedSource (B J) H x).card) :
    ∃ x0 : G, beta * (∏ i ∈ Finset.range J, sigma i) * ((B 0).card : ℝ) ≤
      (translatedSource (B 0) H x0).card := by
  induction J generalizing beta x with
  | zero =>
      exact ⟨x, by simpa using hcapture⟩
  | succ J ih =>
      have hidx : J < J + 1 := by omega
      have hcapE : beta * (((E J).image difference).card : ℝ) ≤
          (captured ((E J).image difference) H x).card := by
        rw [himage J hidx]
        exact hcapture
      have hscaleE : sigma J * ((B J).card : ℝ) ^ 2 ≤
          L J * ((E J).image difference).card := by
        rw [himage J hidx]
        exact hscale J hidx
      obtain ⟨t, _ht, hstep⟩ := exists_original_translate_pullback_density
        (B J) (E J) H x (L J) beta (sigma J) (hB J (by omega)) (hE J hidx)
        (hL J hidx) hbeta (hfiber J hidx) hcapE hscaleE
      obtain ⟨x0, hx0⟩ := ih
        (fun i hi => hB i (by omega))
        (fun i hi => hE i (by omega))
        (fun i hi => himage i (by omega))
        (fun i hi => hL i (by omega))
        (fun i hi => hsigma i (by omega))
        (fun i hi => hfiber i (by omega))
        (fun i hi => hscale i (by omega))
        (beta * sigma J) (mul_nonneg hbeta (hsigma J hidx)) (x + t) hstep
      refine ⟨x0, ?_⟩
      rw [Finset.prod_range_succ]
      convert hx0 using 1
      ring

end IteratedDifferenceTranslatePullback
