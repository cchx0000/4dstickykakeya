import Theorems.Thm_StickyKakeya4_original_source_log_budgets
import Theorems.Thm_StickyKakeya4_native_original_coarse_tube_family
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPruningLoss
open OriginalSourceLogBudgets OriginalPairStripGeometry OriginalPhysicalTubeScaleSelection
open DyadicOriginalFiberSelection PlanarFrostmanBallConversion

lemma original_annular_exponent_ge (t sigma eta : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (ha : sigma<t) (heta : 0<eta) :
    eta≤2*((4+12/t)*eta)/(t-sigma) := by
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  have hq : 0≤12/t := by positivity
  nlinarith only [ht2,hsigma,heta,hq,mul_nonneg hq heta.le]

/-- Actual packing and the original scale menu absorb all near-diagonal,
annular and angular pruning errors before the retained graph is selected. -/
theorem exists_original_pruning_loss_cutoff (t sigma eta : ℝ)
    (ht : 0<t) (ht2 : t≤2) (hsigma : 0≤sigma) (ha : sigma<t) (heta : 0<eta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ n : ℕ,
        delta≤dyadicRadius n → dyadicRadius n≤2*delta →
        ∀ Pts : Finset Point,
          (∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1) →
          (∀ x∈Pts, ∀ y∈Pts, x≠y → delta≤euclideanDistance x y) →
          delta^eta+(((n+1)*levelCount Pts:ℕ):ℝ)*
            (delta^(2*eta)+400*delta^(2*((4+12/t)*eta)/(t-sigma)))≤
              delta^(eta/2)/2 := by
  obtain ⟨delta0,hd0,hd01,hlog⟩ := exists_original_logarithmic_power_cutoff
    804 (by norm_num) 1 1 (eta/2) (by positivity)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall n hmesh hbottom Pts hbox hsep
  have hd1 := hsmall.trans hd01
  have hh := hlog delta hd hsmall n hmesh hbottom Pts hbox hsep
  simp only [pow_one] at hh
  let H : ℝ := (((n+1)*levelCount Pts:ℕ):ℝ)
  have hH : 1≤H := by
    have hl : 1≤levelCount Pts := by unfold levelCount; omega
    have hm : 1≤(n+1)*levelCount Pts := by nlinarith only [hl]
    dsimp [H]
    exact_mod_cast hm
  have hHhi : H≤((n:ℝ)+5)*(levelCount Pts:ℝ) := by
    dsimp [H]
    push_cast
    have hl : (0:ℝ)≤levelCount Pts := by positivity
    nlinarith only [hl]
  have haexp := original_annular_exponent_ge t sigma eta ht ht2 hsigma ha heta
  have h2 : delta^(2*eta)≤delta^eta :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [heta])
  have htail : delta^(2*((4+12/t)*eta)/(t-sigma))≤delta^eta :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 haexp
  have hp : 0<delta^(eta/2) := Real.rpow_pos_of_pos hd _
  have he : delta^eta=delta^(eta/2)*delta^(eta/2) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hlogH : 804*H*delta^(eta/2)≤1 := by
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHhi (by norm_num : (0:ℝ)≤804)) hp.le
    nlinarith only [hmul,hh]
  have hlog2 := mul_le_mul_of_nonneg_right hlogH hp.le
  have hinner : delta^(2*eta)+400*delta^(2*((4+12/t)*eta)/(t-sigma))≤401*delta^eta := by
    linarith only [h2,htail]
  have hprod := mul_le_mul_of_nonneg_left hinner (by linarith only [hH] : 0≤H)
  have hunit := mul_le_mul_of_nonneg_right hH (Real.rpow_pos_of_pos hd eta).le
  change delta^eta+H*(delta^(2*eta)+400*delta^(2*((4+12/t)*eta)/(t-sigma)))≤delta^(eta/2)/2
  rw [he] at hprod hunit ⊢
  nlinarith only [hprod,hunit,hlog2]

/-- Once the original graph exceeds the target error, more than half of
its mass is charged to the actual retained graph, with the true menu factor. -/
theorem original_retained_graph_half (g g4 p H err target : ℝ)
    (hp : 0≤p) (herr : err≤target/2)
    (hlarge : target*p<g) (hretain : g≤H*g4+err*p) :
    g/2<H*g4 := by
  have hh := mul_le_mul_of_nonneg_right herr hp
  nlinarith only [hh,hlarge,hretain]

end NativeOriginalPruningLoss
