import Theorems.Thm_StickyKakeya4_original_common_scalar_growth
import Theorems.Thm_StickyKakeya4_vector_original_graph_bsg
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open Finset
noncomputable section
open Classical
namespace OriginalGraphRadialGrowth
open OriginalCommonScalarGrowth VectorOriginalGraphBSG VectorGraphCollisionEnergy
open DyadicOriginalFiberSelection PlanarShiftedNearEnergy OriginalPhysicalPairTube
abbrev Point := ℝ × ℝ

/-- Original G -> graph-weighted planar BSG -> literal common-C fibers ->
separated original A-pair collisions -> actual B-pair tube double counting.
The radial premise is explicitly an ORIGINAL physical-pair tube count; the
currently open all-scale radial theorem is not asserted or hidden here.
K and n0 are chosen before all source populations and native cap parameters. -/
theorem original_graph_growth_of_original_radial_cap {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ beta M : ℝ, 0 < beta → 0 < M →
      ∀ A B : Finset Point, ∀ C : Finset ℝ,
      ∀ G : Finset (Point × (Point × ℝ)), A.Nonempty → B.Nonempty → C.Nonempty →
      (∀ a ∈ A, |a.1| ≤ 1 ∧ |a.2| ≤ 1) →
      (∀ b ∈ B, |b.1| ≤ 1 ∧ |b.2| ≤ 1) → (∀ c ∈ C, |c| ≤ 1) →
      (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → ((2:ℝ)^n)⁻¹/2 ≤ ‖a-a'‖) →
      (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ((2:ℝ)^n)⁻¹ ≤ |c-c'|) →
      G ⊆ A ×ˢ (B ×ˢ C) → beta*A.card*(B ×ˢ C).card ≤ (G.card : ℝ) →
      ((G.image (fun e => roundPoint (((2:ℝ)^n)⁻¹) (e.1+productValue e.2))).card : ℝ) ≤ M*A.card →
      let delta : ℝ := ((2:ℝ)^n)⁻¹
      let alpha := sourceDensity (B ×ˢ C) beta M
      let r := alpha^K*delta^epsilon
      let tau := r*(beta^2/M)/(196*(levelCount (B ×ˢ C) : ℝ))
      let Q := 49*(delta^(-2*epsilon)/alpha^(2*K))
      ∀ H : Finset (Point × Point), ∀ d t s chi mu kappa cap : ℝ,
      0 < d → 0 ≤ t → 0 < s → 0 ≤ chi → 0 ≤ cap →
      H ⊆ B ×ˢ B →
      (((B ×ˢ B) \ H).card : ℝ) ≤ mu*(B.card : ℝ)^2 →
      (∀ b ∈ B, ((B.filter (fun b' => ‖b'-b‖ ≤ d)).card : ℝ) ≤ kappa*B.card) →
      mu+kappa ≤ tau^2/4 →
      (∀ bb ∈ H, ((physicalPairTube B (4*delta/s) bb).card : ℝ) ≤ cap*B.card) →
      s+delta/2 ≤ d*t →
      (∀ c ∈ C, ((C.filter (fun c' => |c'-c| ≤ t)).card : ℝ) ≤ chi*C.card) →
      32*chi ≤ r*(tau^2/2)^2/Q →
      (tau^2/4)*((r*(tau^2/2)^2/Q)/(2*(1/d+2)))*C.card ≤ cap*A.card := by
  obtain ⟨K,n0,hK,hBSG⟩ := original_ABC_dyadic_bsg hepsilon
  refine ⟨K,n0,hK,?_⟩
  intro n hn beta M hb hM A B C G hA hB hC hAbound hBbound hCbound hAsep hCsep hG hdense hcover
  let delta : ℝ := ((2:ℝ)^n)⁻¹
  let alpha := sourceDensity (B ×ˢ C) beta M
  let r := alpha^K*delta^epsilon
  let tau := r*(beta^2/M)/(196*(levelCount (B ×ˢ C) : ℝ))
  let Q := 49*(delta^(-2*epsilon)/alpha^(2*K))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hlevels : 0 < (levelCount (B ×ˢ C) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 (B ×ˢ C).card)
  have halpha : 0 < alpha := by dsimp [alpha,sourceDensity]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  obtain ⟨_j,_hj,A',F,hA'sub,hF,_hFbin,_hbin,_hGbin,hAmass,hFmass,_hwhole,hFcover⟩ :=
    hBSG n hn beta M hb hM A B C G hA hB hC hAbound hBbound hCbound hAsep hG hdense hcover
  have hA' : A'.Nonempty := by
    have hc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
    have hh : 0 < (A'.card : ℝ) := (mul_pos hr hc).trans_le hAmass
    exact Finset.card_pos.mp (by exact_mod_cast hh)
  have hFmass' : tau*B.card*C.card ≤ (F.card : ℝ) := by
    simpa only [tau,r,alpha,delta,Finset.card_product,Nat.cast_mul,mul_assoc] using hFmass
  have hA'sep : ∀ a ∈ A', ∀ a' ∈ A', a ≠ a' → delta/2 ≤ ‖a-a'‖ :=
    fun a ha a' ha' hne => hAsep a (hA'sub ha) a' (hA'sub ha') hne
  have hboxB : ∀ b ∈ B, ‖b‖ ≤ 1 := by
    intro b hbB
    simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hBbound b hbB
  dsimp only
  intro H d t s chi mu kappa cap hd ht hs hchi hcap0 hH hmissing hBballs hpairbudget hradial hscale hCcap hscalarbudget
  have hwidth : 8*(delta/2)/s=4*delta/s := by ring
  have hradial' : ∀ bb ∈ H, ((physicalPairTube B (8*(delta/2)/s) bb).card : ℝ) ≤ cap*B.card := by
    simpa only [hwidth] using hradial
  have hh := original_common_scalar_growth A' B C F H (by positivity : 0 < delta/2)
    hdelta hd ht hs hr hQ htau hchi hcap0 hA' hB hC hF hFmass' hH hmissing hBballs
    hpairbudget hboxB hradial' hscale hA'sep hCsep hCcap hAmass hFcover hscalarbudget
  have hpacking : 2*(((delta/2)/d)/delta)+2=1/d+2 := by field_simp
  rw [hpacking] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_card hA'sub)) hcap0)
end OriginalGraphRadialGrowth
