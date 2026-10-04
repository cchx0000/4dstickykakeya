import Theorems.Thm_StickyKakeya4_original_three_dimensional_finite_shade_union
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalShadeGroupConcentration
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalFiniteShadeUnion

private theorem group_weighted_pigeonhole {ι : Type*} (J : Finset ι)
    (n u : ι → ℝ) (rho h B : ℝ) (hrho : 0 < rho) (hh : 0 < h) (hB : 0 < B)
    (hn : ∀ k ∈ J, 0 ≤ n k) (hu : ∀ k ∈ J, 0 ≤ u k)
    (hpop : h ≤ rho^2 * ∑ k ∈ J, n k)
    (hunion : rho^2 * ∑ k ∈ J, u k ≤ B) :
    ∃ k ∈ J, 0 < n k ∧ h * u k ≤ B * n k := by
  have hex : ∃ k ∈ J, 0 < n k := by
    by_contra hf
    push Not at hf
    have he : (∑ k ∈ J, n k) = 0 := Finset.sum_eq_zero (fun k hk => le_antisymm (hf k hk) (hn k hk))
    rw [he,mul_zero] at hpop
    exact (not_le_of_gt hh) hpop
  by_contra hf
  push Not at hf
  have hle (k : ι) (hk : k ∈ J) : B*n k ≤ h*u k := by
    by_cases hp : 0 < n k
    · exact (hf k hk hp).le
    · have he : n k=0 := le_antisymm (le_of_not_gt hp) (hn k hk)
      rw [he,mul_zero]
      exact mul_nonneg hh.le (hu k hk)
  obtain ⟨k,hk,hkp⟩ := hex
  have hs := Finset.sum_lt_sum hle ⟨k,hk,hf k hk hkp⟩
  simp only [← Finset.mul_sum] at hs
  have hs' := mul_lt_mul_of_pos_left hs (sq_pos_of_pos hrho)
  have hlo := mul_le_mul_of_nonneg_left hpop hB.le
  have hhi := mul_le_mul_of_nonneg_left hunion hh.le
  nlinarith only [hs',hlo,hhi]

/-- Actual finite tube shades force a dense pencil group. The only aggregate
inputs are the literal total group count and union-overlap budget; each
individual group's inverse-square union inequality is proved from its
original tube geometry, not supplied as a desired estimate. -/
theorem exists_original_dense_shade_group {ι : Type*} (J : Finset ι)
    (R : ι → Finset Pair3) (Y : Pair3 → Finset Point3)
    (rho b h B : ℝ) (i : Fin 3) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hb : 0 < b) (hsmall : rho ≤ b/4800) (hh : 0 < h) (hB : 0 < B)
    (hne : ∀ k ∈ J, ∀ z ∈ R k, z.2 i-z.1 i ≠ 0)
    (hmax : ∀ k ∈ J, ∀ z ∈ R k, ∀ j, |z.2 j-z.1 j| ≤ |z.2 i-z.1 i|)
    (hcell : ∀ k ∈ J, Set.InjOn (parameterCell rho i) (R k))
    (hshade : ∀ k ∈ J, ∀ z ∈ R k, ∀ x ∈ Y z, x ∈ physicalTube3 z.1 z.2 (4*rho))
    (hbox : ∀ k ∈ J, ∀ z ∈ R k, ∀ x ∈ Y z, ∀ j, |x j| ≤ 1)
    (hinj : ∀ k ∈ J, ∀ z ∈ R k, Set.InjOn (cell rho) (Y z))
    (hmass : ∀ k ∈ J, ∀ z ∈ R k, b ≤ rho*(Y z).card)
    (hpop : h ≤ rho^2 * ∑ k ∈ J, ((R k).card : ℝ))
    (hunion : rho^2 * ∑ k ∈ J, (((R k).biUnion Y).card : ℝ) ≤ B) :
    ∃ k ∈ J, (R k).Nonempty ∧
      h^2*b^4 ≤ 100000000000000000*B^2*rho^2*(R k).card := by
  obtain ⟨k,hk,hnpos,hratio⟩ := group_weighted_pigeonhole J
    (fun k => ((R k).card : ℝ)) (fun k => (((R k).biUnion Y).card : ℝ))
    rho h B hrho hh hB (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    hpop hunion
  have hfinite := original_finite_shade_union (R k) Y rho b i hrho hrho1 hb hsmall
    (hne k hk) (hmax k hk) (hcell k hk) (hshade k hk) (hbox k hk) (hinj k hk) (hmass k hk)
  have hratio2 := pow_le_pow_left₀
    (mul_nonneg hh.le (Nat.cast_nonneg ((R k).biUnion Y).card)) hratio 2
  have h1 := mul_le_mul_of_nonneg_left hfinite (sq_nonneg h)
  have h2 := mul_le_mul_of_nonneg_left hratio2
    (show (0:ℝ) ≤ 100000000000000000*rho^2 by positivity)
  refine ⟨k,hk,Finset.card_pos.mp (by exact_mod_cast hnpos),?_⟩
  apply (mul_le_mul_iff_of_pos_right hnpos).mp
  nlinarith only [h1,h2]

end OriginalThreeDimensionalShadeGroupConcentration
