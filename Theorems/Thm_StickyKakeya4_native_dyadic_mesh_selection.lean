import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeDyadicMeshSelection
open Classical
/-- Select a dyadic projection mesh within a factor two of the actual
 spatial mesh, after the analytic theorem's integer cutoff is fixed. -/
theorem exists_nearby_dyadic_mesh {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n0 : ℕ) (hsmall : t ≤ ((2:ℝ)^n0)⁻¹) :
    ∃ m : ℕ, n0 ≤ m ∧ t/2 ≤ ((2:ℝ)^m)⁻¹ ∧ ((2:ℝ)^m)⁻¹ < t := by
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one ht ht1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hpow (j : ℕ) : (1/2:ℝ)^j=((2:ℝ)^j)⁻¹ := by simp only [one_div,inv_pow]
  have hhalf : t/2 ≤ (1/2:ℝ)^(k+1) := by
    rw [pow_succ]
    linarith only [hhi]
  have hsmall' : (1/2:ℝ)^(k+1) ≤ (1/2:ℝ)^n0 := by
    have hh : ((2:ℝ)^(k+1))⁻¹ ≤ t := by simpa only [hpow] using hlo.le
    simpa only [hpow] using hh.trans hsmall
  have hn : n0 ≤ k+1 := (pow_le_pow_iff_right_of_lt_one₀
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hsmall'
  exact ⟨k+1,hn,by simpa only [hpow] using hhalf,by simpa only [hpow] using hlo⟩
/-- The balanced normalization preserves the exact dyadic form. -/
theorem balanced_dyadic_mesh (m : ℕ) : ((2:ℝ)^m)⁻¹/8=((2:ℝ)^(m+3))⁻¹ := by
  rw [pow_add]
  norm_num
  ring
/-- Lowering a spatial scale preserves a point-centered absolute KT1 law.
 Radii between the new and old meshes are handled using the original law
 at the original mesh, not a new population certificate. -/
theorem original_KT_at_finer_mesh {X : Type*} (P : Finset X) (d : X → X → ℝ)
    {t rho K : ℝ} (ht : 0 < t) (hrho : 0 < rho) (hscale : rho ≤ t) (hK : 0 ≤ K)
    (hKT : ∀ i ∈ P, ∀ R : ℝ, t ≤ R →
      ((P.filter (fun k => d i k ≤ R)).card : ℝ) ≤ K*R/t) :
    ∀ i ∈ P, ∀ R : ℝ, rho ≤ R →
      ((P.filter (fun k => d i k ≤ R)).card : ℝ) ≤ K*R/rho := by
  intro i hi R hR
  by_cases hRt : t ≤ R
  · exact (hKT i hi R hRt).trans
      (div_le_div_of_nonneg_left (mul_nonneg hK (hrho.le.trans hR)) hrho hscale)
  · have hRt' := (lt_of_not_ge hRt).le
    have hsub : P.filter (fun k => d i k ≤ R) ⊆ P.filter (fun k => d i k ≤ t) := by
      intro k hk
      obtain ⟨hk,hkR⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hk,hkR.trans hRt'⟩
    have hc : ((P.filter (fun k => d i k ≤ R)).card : ℝ) ≤
        ((P.filter (fun k => d i k ≤ t)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hbase : ((P.filter (fun k => d i k ≤ t)).card : ℝ) ≤ K := by
      simpa only [mul_div_cancel_right₀ K ht.ne'] using hKT i hi t le_rfl
    exact hc.trans (hbase.trans ((le_div_iff₀ hrho).mpr (mul_le_mul_of_nonneg_left hR hK)))
/-- The actual original B population loses at most a factor two when the
 projection mesh is the nearby lower dyadic. -/
theorem original_mass_at_nearby_mesh {t rho mass N : ℝ} (hhalf : t/2 ≤ rho)
    (hN : 0 ≤ N) (hmass : mass ≤ t*N) : mass/2 ≤ rho*N := by
  have hh := mul_le_mul_of_nonneg_right hhalf hN
  nlinarith only [hh,hmass]
/-- Original endpoint errors are unchanged; their mesh ratio pays only the
 actual dyadic rounding factor. -/
theorem error_ratio_at_nearby_mesh {t rho error : ℝ} (ht : 0 < t) (hrho : 0 < rho)
    (hhalf : t/2 ≤ rho) (he : 0 ≤ error) : error/rho ≤ 2*(error/t) := by
  apply (div_le_iff₀ hrho).mpr
  have hh := mul_le_mul_of_nonneg_left hhalf (div_nonneg he ht.le)
  have hid : (error/t)*(t/2)=error/2 := by field_simp
  rw [hid] at hh
  nlinarith only [hh]
/-- The exact dyadic form supplied to the balanced actual ABC constructor,
 with the analytic threshold already fixed. -/
theorem exists_balanced_nearby_dyadic_mesh {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (n0 : ℕ) (hsmall : t ≤ ((2:ℝ)^n0)⁻¹) :
    ∃ n : ℕ, ∃ rho : ℝ, n0 ≤ n ∧ 0 < rho ∧ rho/8=((2:ℝ)^n)⁻¹ ∧
      t/2 ≤ rho ∧ rho < t := by
  obtain ⟨m,hm,hlo,hhi⟩ := exists_nearby_dyadic_mesh ht ht1 n0 hsmall
  exact ⟨m+3,((2:ℝ)^m)⁻¹,by omega,by positivity,balanced_dyadic_mesh m,hlo,hhi⟩
/-- The original finite population itself supplies the KT and lower mass
 inputs at the chosen dyadic mesh; no new population is selected here. -/
theorem exists_dyadic_original_population {X : Type*} (P : Finset X) (d : X → X → ℝ)
    {t K mass : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 ≤ K)
    (n0 : ℕ) (hsmall : t ≤ ((2:ℝ)^n0)⁻¹)
    (hKT : ∀ i ∈ P, ∀ R : ℝ, t ≤ R →
      ((P.filter (fun k => d i k ≤ R)).card : ℝ) ≤ K*R/t)
    (hmass : mass ≤ t*(P.card:ℝ)) :
    ∃ m : ℕ, n0 ≤ m ∧ t/2 ≤ ((2:ℝ)^m)⁻¹ ∧ ((2:ℝ)^m)⁻¹ < t ∧
      mass/2 ≤ ((2:ℝ)^m)⁻¹*(P.card:ℝ) ∧
      ∀ i ∈ P, ∀ R : ℝ, ((2:ℝ)^m)⁻¹ ≤ R →
        ((P.filter (fun k => d i k ≤ R)).card : ℝ) ≤ K*R/((2:ℝ)^m)⁻¹ := by
  obtain ⟨m,hm,hlo,hhi⟩ := exists_nearby_dyadic_mesh ht ht1 n0 hsmall
  exact ⟨m,hm,hlo,hhi,
    original_mass_at_nearby_mesh hlo (Nat.cast_nonneg _) hmass,
    original_KT_at_finer_mesh P d ht (by positivity) hhi.le hK hKT⟩
end NativeDyadicMeshSelection
