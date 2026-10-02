import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
Scalar estimates for the original-data excessive local seed.  These lemmas
absorb fixed constants only after a positive small-scale threshold has been
chosen; they do not assume or manufacture geometric source certificates.
-/

open Filter Set
open scoped Topology

namespace StickyKakeya4.LocalSeedAbsorption

/-- A fixed nonnegative coefficient is absorbed by a positive power on an
arbitrarily small interval. -/
theorem exists_rpow_threshold
    {a coefficient target cap : ℝ}
    (ha : 0 < a) (hcoefficient : 0 ≤ coefficient)
    (htarget : 0 < target) (hcap : 0 < cap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ cap ∧
      ∀ r : ℝ, 0 < r → r ≤ epsilon → coefficient * r ^ a ≤ target := by
  have hfull : Tendsto (fun r : ℝ => coefficient * r ^ a) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow ha.ne'] using
      tendsto_const_nhds.mul ((Real.continuous_rpow_const ha.le).tendsto 0)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, coefficient * r ^ a < target :=
    (tendsto_order.1 (hfull.mono_left inf_le_left)).2 _ htarget
  have hrange : Set.Ioc (0 : ℝ) cap ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT hcap
  obtain ⟨epsilon, hsmallEpsilon, hepsilon, hepsilonCap⟩ := (hsmall.and hrange).exists
  refine ⟨epsilon, hepsilon, hepsilonCap, ?_⟩
  intro r hr hrepsilon
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hr.le hrepsilon ha.le) hcoefficient).trans hsmallEpsilon.le

/-- One uniform threshold absorbs both the density normalization constant
and the hereditary source cost.  Its upper cap may be arbitrarily small. -/
theorem exists_threshold
    {eta C F cap : ℝ} (heta : 0 < eta) (hC : 0 < C)
    (hF : 0 ≤ F) (hcap : 0 < cap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ cap ∧
      ∀ r : ℝ, 0 < r → r ≤ epsilon →
        C * r ^ (eta / 4) ≤ (2 : ℝ) ^ (-eta / 2) ∧
          F * r ^ (eta / 16) ≤ 1 := by
  obtain ⟨e₁, he₁, he₁cap, hdensity⟩ := exists_rpow_threshold
    (show 0 < eta / 4 by positivity) hC.le
    (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (-eta / 2)) hcap
  obtain ⟨e₂, he₂, _he₂cap, hcost⟩ := exists_rpow_threshold
    (show 0 < eta / 16 by positivity) hF (show (0 : ℝ) < 1 by norm_num) hcap
  refine ⟨min e₁ e₂, lt_min he₁ he₂, (min_le_left _ _).trans he₁cap, ?_⟩
  intro r hr hre
  exact ⟨hdensity r hr (hre.trans (min_le_left _ _)),
    hcost r hr (hre.trans (min_le_right _ _))⟩

/-- Rescaling a shell lower bound by the block volume preserves a fixed
positive multiple of the same ratio power.  The upper shell scale is two. -/
theorem shell_density_lower_bound
    {eta C rho tau Z M : ℝ} (heta : 0 ≤ eta) (hC : 0 < C)
    (hrho : 0 < rho) (htau : 0 < tau) (htauTwo : tau ≤ 2)
    (hshell : rho ^ (2 - eta / 2) < Z)
    (hdensity : Z / (C * tau ^ 2) ≤ M) :
    ((2 : ℝ) ^ (-eta / 2) / C) * (rho / tau) ^ (2 - eta / 2) ≤ M := by
  have hscale : (2 : ℝ) ^ (-eta / 2) ≤ tau ^ (-eta / 2) :=
    Real.rpow_le_rpow_of_nonpos htau htauTwo (by linarith)
  have hsplit : tau ^ (2 - eta / 2) = tau ^ (-eta / 2) * tau ^ (2 : ℕ) := by
    rw [show (2 - eta / 2 : ℝ) = -eta / 2 + 2 by ring,
      Real.rpow_add htau, Real.rpow_two]
  have hidentity :
      (tau ^ (-eta / 2) / C) * (rho / tau) ^ (2 - eta / 2) =
        rho ^ (2 - eta / 2) / (C * tau ^ (2 : ℕ)) := by
    rw [Real.div_rpow hrho.le htau.le, hsplit]
    field_simp
  calc
    ((2 : ℝ) ^ (-eta / 2) / C) * (rho / tau) ^ (2 - eta / 2)
        ≤ (tau ^ (-eta / 2) / C) * (rho / tau) ^ (2 - eta / 2) := by
          exact mul_le_mul_of_nonneg_right
            ((div_le_div_iff_of_pos_right hC).mpr hscale)
            (Real.rpow_nonneg (div_nonneg hrho.le htau.le) _)
    _ = rho ^ (2 - eta / 2) / (C * tau ^ 2) := hidentity
    _ ≤ Z / (C * tau ^ 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr hshell.le
    _ ≤ M := hdensity

/-- The density exponent improves from `2 - eta/2` to `2 - eta/4`
after the fixed normalization constant is absorbed. -/
theorem absorb_density
    {eta C r M : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hsmall : C * r ^ (eta / 4) ≤ (2 : ℝ) ^ (-eta / 2))
    (hdensity : ((2 : ℝ) ^ (-eta / 2) / C) * r ^ (2 - eta / 2) ≤ M) :
    r ^ (2 - eta / 4) ≤ M := by
  have hcoefficient : r ^ (eta / 4) ≤ (2 : ℝ) ^ (-eta / 2) / C := by
    apply (le_div_iff₀ hC).mpr
    simpa [mul_comm] using hsmall
  calc
    r ^ (2 - eta / 4) = r ^ (eta / 4) * r ^ (2 - eta / 2) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    _ ≤ ((2 : ℝ) ^ (-eta / 2) / C) * r ^ (2 - eta / 2) :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.rpow_nonneg hr.le _)
    _ ≤ M := hdensity

/-- The manuscript's choice `zeta = eta²/64` gives tax exponent `eta/16`. -/
theorem tax_exponent {eta zeta : ℝ} (heta : 0 < eta)
    (hzeta : zeta = eta ^ 2 / 64) : 4 * zeta / eta = eta / 16 := by
  rw [hzeta]
  field_simp
  ring

/-- Absorb the finite cost into the remaining half of the allowed tax
exponent. -/
theorem absorb_cost
    {eta zeta r tau F cost : ℝ} (heta : 0 < eta)
    (hzeta : zeta = eta ^ 2 / 64) (hr : 0 < r) (hF : 0 ≤ F)
    (hsmall : F * r ^ (eta / 16) ≤ 1)
    (htax : tau ^ (-zeta) ≤ r ^ (-(4 * zeta / eta)))
    (hcost : cost ≤ F * tau ^ (-zeta)) : cost ≤ r ^ (-eta / 8) := by
  have hFbound : F ≤ r ^ (-(eta / 16)) := by
    rw [Real.rpow_neg hr.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hr _)).mpr hsmall
  rw [tax_exponent heta hzeta] at htax
  calc
    cost ≤ F * tau ^ (-zeta) := hcost
    _ ≤ F * r ^ (-(eta / 16)) := mul_le_mul_of_nonneg_left htax hF
    _ ≤ r ^ (-(eta / 16)) * r ^ (-(eta / 16)) :=
      mul_le_mul_of_nonneg_right hFbound (Real.rpow_nonneg hr.le _)
    _ = r ^ (-eta / 8) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring

/-- Uniform small-scale local seed bounds from the original shell mass,
block normalization, and scale tax. -/
theorem exists_local_seed_threshold
    {eta C F cap : ℝ} (heta : 0 < eta) (hC : 0 < C)
    (hF : 0 ≤ F) (hcap : 0 < cap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ cap ∧
      ∀ rho tau Z M cost zeta : ℝ,
        0 < rho → 0 < tau → tau ≤ 2 → rho / tau ≤ epsilon →
        rho ^ (2 - eta / 2) < Z → Z / (C * tau ^ 2) ≤ M →
        zeta = eta ^ 2 / 64 →
        tau ^ (-zeta) ≤ (rho / tau) ^ (-(4 * zeta / eta)) →
        cost ≤ F * tau ^ (-zeta) →
        (rho / tau) ^ (2 - eta / 4) ≤ M ∧
          cost ≤ (rho / tau) ^ (-eta / 8) := by
  obtain ⟨epsilon, hepsilon, hepsilonCap, hsmall⟩ := exists_threshold heta hC hF hcap
  refine ⟨epsilon, hepsilon, hepsilonCap, ?_⟩
  intro rho tau Z M cost zeta hrho htau htauTwo hratio hshell hdensity hzeta htax hcost
  have hr : 0 < rho / tau := div_pos hrho htau
  obtain ⟨hsmallDensity, hsmallCost⟩ := hsmall (rho / tau) hr hratio
  exact ⟨absorb_density hC hr hsmallDensity
      (shell_density_lower_bound heta.le hC hrho htau htauTwo hshell hdensity),
    absorb_cost heta hzeta hr hF hsmallCost htax hcost⟩

end StickyKakeya4.LocalSeedAbsorption
