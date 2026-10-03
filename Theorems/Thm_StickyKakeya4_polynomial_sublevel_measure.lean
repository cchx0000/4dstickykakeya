import Mathlib

open MeasureTheory Set
open scoped BigOperators

namespace PolynomialSublevelMeasure

/-- A product of complex numbers whose norms are at least `R` has norm at least `R^n`. -/
theorem pow_card_le_norm_prod (s : Multiset ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h : ∀ z ∈ s, R ≤ ‖z‖) : R ^ s.card ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.card_cons, Multiset.prod_cons, pow_succ, norm_mul]
    have hz : R ≤ ‖z‖ := h z (by simp)
    have hs : R ^ s.card ≤ ‖s.prod‖ := ih (fun w hw => h w (by simp [hw]))
    simpa only [mul_comm] using mul_le_mul hz hs (pow_nonneg hR _) (norm_nonneg _)

/-- A polynomial value below the product threshold lies within `R` of a complex root. -/
theorem exists_root_close (p : Polynomial ℂ) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h : ‖p.eval z‖ < ‖p.leadingCoeff‖ * R ^ p.natDegree) :
    ∃ w ∈ p.roots, ‖z - w‖ < R := by
  by_contra! hn
  have hp := pow_card_le_norm_prod (p.roots.map (z - ·)) R hR (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hw
    exact hn v hv)
  rw [Multiset.card_map, ← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hp
  have heq := (IsAlgClosed.splits p).eval_eq_prod_roots z
  have heqn := congrArg norm heq
  rw [norm_mul] at heqn
  have := mul_le_mul_of_nonneg_left hp (norm_nonneg p.leadingCoeff)
  linarith

/-- Cover the real sublevel set by intervals centered at real parts of complex roots. -/
theorem volume_sublevel_mul_pow (p : Polynomial ℝ) (R : ℝ) (hR : 0 ≤ R) :
    volume {x : ℝ | |p.eval x| < |p.leadingCoeff| * R ^ p.natDegree} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * R) := by
  classical
  let q := p.map Complex.ofRealHom
  let roots := q.roots.toFinset
  let intervals := fun z : ℂ => Ioo (z.re - R) (z.re + R)
  have hcover : {x : ℝ | |p.eval x| < |p.leadingCoeff| * R ^ p.natDegree} ⊆
      ⋃ z ∈ roots, intervals z := by
    intro x hx
    have hx' : ‖q.eval (x : ℂ)‖ < ‖q.leadingCoeff‖ * R ^ q.natDegree := by
      have heval : q.eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
        simpa only [q, Complex.ofRealHom_eq_coe] using
          (Polynomial.eval_map_apply (p := p) Complex.ofRealHom x)
      rw [heval]
      simpa only [Set.mem_ofPred_eq, q, Polynomial.leadingCoeff_map, Polynomial.natDegree_map,
        Complex.norm_real, Real.norm_eq_abs, Complex.ofRealHom_eq_coe] using hx
    obtain ⟨z, hz, hdist⟩ := exists_root_close q (x : ℂ) R hR hx'
    refine mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simpa [roots] using hz
    have habs : |x - z.re| < R := by
      have hh := (Complex.abs_re_le_norm ((x : ℂ) - z)).trans_lt hdist
      simpa using hh
    change z.re - R < x ∧ x < z.re + R
    rcases abs_lt.mp habs with ⟨ha, hb⟩
    constructor <;> linarith
  have hcard : roots.card ≤ p.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (by
      simpa [q] using q.card_roots')
  calc
    volume {x : ℝ | |p.eval x| < |p.leadingCoeff| * R ^ p.natDegree}
      ≤ volume (⋃ z ∈ roots, intervals z) := measure_mono hcover
    _ ≤ ∑ z ∈ roots, volume (intervals z) := measure_biUnion_finset_le roots intervals
    _ = ENNReal.ofReal ((roots.card : ℝ) * (2 * R)) := by
      simp only [intervals, Real.volume_Ioo]
      have hlength (z : ℂ) : z.re + R - (z.re - R) = 2 * R := by ring
      simp only [hlength, Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * R) := by
      apply ENNReal.ofReal_le_ofReal
      have hc : (roots.card : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hcard
      nlinarith

/-- Quantitative Lebesgue sublevel bound for every nonconstant real polynomial. -/
theorem volume_sublevel (p : Polynomial ℝ) (hd : 0 < p.natDegree)
    (δ : ℝ) (hδ : 0 < δ) :
    volume {x : ℝ | |p.eval x| < δ} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) *
        (δ / |p.leadingCoeff|) ^ (1 / (p.natDegree : ℝ))) := by
  have hc : 0 < |p.leadingCoeff| := abs_pos.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hd))
  let R := (δ / |p.leadingCoeff|) ^ (1 / (p.natDegree : ℝ))
  have hR : 0 ≤ R := Real.rpow_nonneg (le_of_lt (div_pos hδ hc)) _
  have hpow : R ^ p.natDegree = δ / |p.leadingCoeff| := by
    simpa only [R, one_div] using
      Real.rpow_inv_natCast_pow (le_of_lt (div_pos hδ hc)) (Nat.ne_of_gt hd)
  have hδeq : |p.leadingCoeff| * R ^ p.natDegree = δ := by
    rw [hpow, mul_div_cancel₀ _ (ne_of_gt hc)]
  have hm := volume_sublevel_mul_pow p R hR
  rw [hδeq] at hm
  exact hm


end PolynomialSublevelMeasure
