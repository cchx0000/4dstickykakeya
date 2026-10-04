import Theorems.Thm_StickyKakeya4_original_native_numeric_budgets
import Theorems.Thm_StickyKakeya4_original_native_cover_scale_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048
noncomputable section

namespace OriginalNativeUniformBudget
open ProjectionAnnulusEnergy OriginalNativeProjectionPowerCutoff
open OriginalNativeNumericBudgets OriginalNativeCoverScaleBudget
open OriginalNativeProjectionBSGCore OriginalNativeProjectionFailureComparison
open OriginalTwoProjectionCartesian

/-- The concrete numerical input list for the original-source robust
comparison, at its genuine finer mesh. Every field is supplied uniformly
by the theorem below, before the finite source is chosen. -/
structure Budgets (n : ℕ) (N u gap eta epsilon scalarCutoff e : ℝ) : Prop where
  coefficient_ge_one : 1≤1/(mesh n)^e
  source_mass_le_one : (mesh n)^((20+64/u)*e)≤1
  query_pos : 0<(mesh n)^e
  query_le_one : (mesh n)^e≤1
  host_pos : 0<((mesh n)^e)^4/32
  host_lt_one : ((mesh n)^e)^4/32<1
  host_budget : ((mesh n)^e)^4/32≤((mesh n)^e)^3/16
  angle_pos : 0<(mesh n)^(8*e/u)
  angle_le_one : (mesh n)^(8*e/u)≤1
  angle_mesh : mesh n≤(mesh n)^(8*e/u)
  cover_pos : 0<(mesh n)^(-e)*Real.sqrt N
  first_angles : (((1/(mesh n)^e)/(mesh n)^e)/(1-((mesh n)^e)^4/32))*
    ((mesh n)^(8*e/u))^u≤((mesh n)^e)^3/16
  fresh_angles : (1/(mesh n)^e)*((mesh n)^(8*e/u))^u≤(mesh n)^e/4
  retained_admissibility : (mesh n)^((20+64/u)*e)*N≤
    originalRetention (((mesh n)^e)^3/16) N ((mesh n)^(8*e/u))
      ((mesh n)^(-e)*Real.sqrt N)*((mesh n)^(-e)*Real.sqrt N)^2
  scalar_mesh_small : (mesh n)^(8*e/u)*mesh n/64 ≤ scalarCutoff
  cover_cardinality : (mesh n)^(-e)*Real.sqrt N≤
    ((mesh n)^(8*e/u)*mesh n/64)^(-1+gap)
  alphabet_profile :
    originalAlphabetProfileCost n (1/(mesh n)^e) (1/(mesh n)^e) ((mesh n)^e)
      (((mesh n)^e)^4/32) ((mesh n)^e) N ((mesh n)^(8*e/u))
      ((mesh n)^(-e)*Real.sqrt N)*(16/((mesh n)^(8*e/u)))^u/
      originalRetention (((mesh n)^e)^3/16) N ((mesh n)^(8*e/u))
        ((mesh n)^(-e)*Real.sqrt N)≤((mesh n)^(8*e/u)*mesh n/64)^(-eta)
  coefficient_profile : (2*(1/(mesh n)^e)/(mesh n)^e)*
    (64/((mesh n)^(8*e/u))^2)^u≤((mesh n)^(8*e/u)*mesh n/64)^(-eta)
  coefficient_box : 4/((mesh n)^(8*e/u))^2≤((mesh n)^(8*e/u)*mesh n/64)^(-eta)
  reverse_comparison :
    (2:ℝ)^242*fiberBound ((mesh n)^(8*e/u))*(restrictedSumLoss ((mesh n)^(8*e/u)))^15*
      (12672/((mesh n)^(8*e/u))^5)≤
    (mesh n)^e*(originalDensity (((mesh n)^e)^3/16) N ((mesh n)^(8*e/u))
      ((mesh n)^(-e)*Real.sqrt N))^77*((mesh n)^(8*e/u)*mesh n/64)^(-epsilon)

theorem exists_original_native_uniform_budget {u gap eta epsilon scalarCutoff : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1/4)
    (heta : 0<eta) (hepsilon : 0<epsilon) (hcutoff : 0<scalarCutoff) :
    ∃ e d : ℝ, 0<e ∧ 0<d ∧ d≤1 ∧ d ≤ scalarCutoff ∧
      ∀ (n : ℕ) (N : ℝ), mesh n≤d → 0<N → N≤(mesh n)^(-2+4*gap) →
        (mesh n)^(e/4)≤1/4 ∧ Budgets n N u gap eta epsilon scalarCutoff e := by
  obtain ⟨e,d,he,heu,heg,hd,hd1,hdcut,hall⟩ :=
    exists_native_power_cutoff hu hgap heta hepsilon hcutoff
  refine ⟨e,d,he,hd,hd1,hdcut,?_⟩
  intro n N hn hN hNcard
  have hδ := mesh_pos n
  have hδ1 := hn.trans hd1
  obtain ⟨hsmall,ht2,hlog,hprofile,hcomparison⟩ := hall n hn
  let t := (mesh n)^e
  let h := (mesh n)^(8*e/u)
  let M := (mesh n)^(-e)*Real.sqrt N
  have ht : 0<t := Real.rpow_pos_of_pos hδ _
  have ht1 : t≤1 := Real.rpow_le_one hδ.le hδ1 he.le
  have htsmall : t≤1/64 :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show e/4≤e by linarith only [he])).trans hsmall
  have hexp : 0<8*e/u := by positivity
  have hh : 0<h := Real.rpow_pos_of_pos hδ _
  have hh1 : h≤1 := Real.rpow_le_one hδ.le hδ1 hexp.le
  have hangle : mesh n≤h := by
    have hp := (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mp heu
    have hb : 8*e/u≤1 := (div_le_iff₀ hu).mpr (by nlinarith only [hp,hu])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hb
  have hscale := native_cover_scale_square (e:=e) hδ hN.le
  have hmpos := native_cover_scale_pos (e:=e) hδ hN
  have hanglePow : h^u=t^8 := by
    dsimp [h,t]
    rw [←Real.rpow_mul hδ.le,←Real.rpow_natCast,←Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    field_simp
  have hquery := native_small_query_budgets ht htsmall hh hanglePow
  have hprof := native_profile_and_comparison_budgets n hδ ht ht1 hh hh1 hN hscale
    hu1 heta hepsilon hlog hprofile hcomparison
  have hmass : (mesh n)^((20+64/u)*e)≤1 :=
    Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hsmall2 : t^2≤1/(2:ℝ)^52 := by
    dsimp [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    convert ht2 using 1 <;> norm_num [mul_comm]
  have hadm := native_source_mass_admissible ht hh hh1 hN hscale hsmall2
  have hsmallmesh : h*mesh n/64 ≤ scalarCutoff := by
    have hp := mul_le_mul_of_nonneg_right hh1 hδ.le
    have hdlt := hn.trans hdcut
    nlinarith only [hp,hdlt,hδ]
  refine ⟨by linarith only [hsmall],{
    coefficient_ge_one := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using ht1)
    source_mass_le_one := hmass
    query_pos := ht
    query_le_one := ht1
    host_pos := hquery.1
    host_lt_one := hquery.2.1
    host_budget := hquery.2.2.1
    angle_pos := hh
    angle_le_one := hh1
    angle_mesh := hangle
    cover_pos := hmpos
    first_angles := hquery.2.2.2.1
    fresh_angles := hquery.2.2.2.2
    retained_admissibility := ?_
    scalar_mesh_small := hsmallmesh
    cover_cardinality := native_cover_scale_cardinality hδ hδ1 hh hh1 hgap hgap1 heg hNcard
    alphabet_profile := hprof.1
    coefficient_profile := hprof.2.1
    coefficient_box := hprof.2.2.1
    reverse_comparison := hprof.2.2.2 }⟩
  simpa only [native_source_mass_identity hδ] using hadm

end OriginalNativeUniformBudget
