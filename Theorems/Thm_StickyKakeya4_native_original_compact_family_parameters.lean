import Theorems.Thm_StickyKakeya4_original_critical_population_range
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeOriginalCompactFamilyParameters
open OriginalPairStripGeometry OriginalCriticalWidthBound OriginalCriticalCapParameterTransfer
open OriginalClippedUnitTube OriginalArbitraryStripCapCharge OriginalCriticalPopulationRange

/-- The actual critical query and critical cap pin the effective tube
population exponent to a fixed compact range. The width is the actual
coarse scale 3rho and the cardinality identity is exact. -/
theorem exists_original_compact_family_parameter_cutoff
    (eps1 kappa C0 chi : ℝ) (heps : 0<eps1) (hkappa : 0<kappa)
    (hC0 : 0≤C0) (hchi : 0<chi) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
      ∀ (rho : ℝ) (S : Finset Pair), delta≤rho → rho≤delta^kappa →
        S.Nonempty → (∀ z∈S, z.1≠z.2) →
        432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1) →
        (∀ (nx ny c : ℝ) (A : Set Point), nx^2+ny^2=1 →
          (∀ p∈A, |nx*p.1+ny*p.2-c|≤criticalWidth rho S) →
          ((containedInSet S (3*rho) A).card : ℝ)≤delta^chi*S.card) →
        ∃ tbar : ℝ, 0<3*rho ∧ 3*rho≤1/2 ∧
          (3*rho)^(-tbar)=(S.card : ℝ) ∧ chi≤tbar ∧ tbar≤2-7*eps1 ∧
          0<tbar ∧ tbar<2 ∧
          0<min (chi/2) (7*eps1/2) ∧
          min (chi/2) (7*eps1/2)≤min tbar (2-tbar) := by
  obtain ⟨delta0,hd0,hd01,hupper⟩ := exists_original_population_upper_cutoff
    eps1 kappa C0 heps hkappa hC0
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho S hmesh hdecay hS hdistinct hquery hcap
  obtain ⟨hr,hrhalf,hpopUpper⟩ := hupper delta hd hsmall rho S hmesh hdecay hquery
  have hcoarse := original_critical_cap_coarse_exponent S rho delta chi chi hd
    (hsmall.trans hd01) hmesh hchi.le le_rfl hcap
  have hlower := (original_critical_cap_population S rho (3*rho) chi
    (hd.trans_le hmesh) hr hS hdistinct hcoarse).2
  obtain ⟨tbar,heq,hlo,hhi,ht,ht2,hu,huBound⟩ := original_effective_family_exponent
    S (3*rho) chi eps1 hr (by linarith only [hrhalf]) hchi heps hS hlower hpopUpper
  exact ⟨tbar,hr,hrhalf,heq,hlo,hhi,ht,ht2,hu,huBound⟩

end NativeOriginalCompactFamilyParameters
