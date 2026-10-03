import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite


open Polynomial Matrix

noncomputable section

namespace RankOneFeedbackPolynomials

def denominator (L : Matrix (Fin 3) (Fin 3) ℝ) : Polynomial ℝ := (-L).charpoly

def numerator (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) : Polynomial ℝ :=
  ∑ i, ∑ j, C (v i) * (-L).charmatrix.adjugate i j * C (u j)

lemma denominator_eval (L : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (denominator L).eval t = (L + t • 1).det := by
  rw [denominator, Matrix.eval_charpoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.scalar_apply, add_comm]

lemma denominator_monic (L : Matrix (Fin 3) (Fin 3) ℝ) :
    (denominator L).Monic := Matrix.charpoly_monic (-L)

lemma denominator_natDegree (L : Matrix (Fin 3) (Fin 3) ℝ) :
    (denominator L).natDegree = 3 := by
  simp [denominator]

lemma adjugate_natDegree (L : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    ((-L).charmatrix.adjugate i j).natDegree ≤ 2 := by
  have he (a b : Fin 3) : ((-L).charmatrix a b).natDegree ≤ 1 := by
    exact (Matrix.charmatrix_apply_natDegree_le a b).trans (by split_ifs <;> omega)
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_two]
  refine Polynomial.natDegree_mul_le.trans ?_
  have hs : ((-1 : Polynomial ℝ) ^ (j + i : ℕ)).natDegree = 0 := by simp
  rw [hs, zero_add]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (by simpa using Nat.add_le_add (he _ _) (he _ _))
  · exact Polynomial.natDegree_mul_le.trans (by simpa using Nat.add_le_add (he _ _) (he _ _))

lemma numerator_natDegree (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    (numerator L u v).natDegree ≤ 2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_mul_C_le _ _).trans
    ((Polynomial.natDegree_C_mul_le _ _).trans (adjugate_natDegree L i j))

lemma eval_charmatrix (L : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (Polynomial.evalRingHom t).mapMatrix (-L).charmatrix = L + t • 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [h, Matrix.charmatrix, Matrix.scalar_apply, add_comm]

lemma numerator_eval (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) (t : ℝ) :
    (numerator L u v).eval t = dotProduct v ((L + t • 1).adjugate.mulVec u) := by
  have hadj := (Polynomial.evalRingHom t).map_adjugate (-L).charmatrix
  rw [eval_charmatrix] at hadj
  simp only [numerator, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hentry := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hadj
  change ((-L).charmatrix.adjugate i j).eval t = (L + t • 1).adjugate i j at hentry
  rw [hentry]
  ring

lemma inverse_feedback (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) (t : ℝ) :
    dotProduct v ((L + t • 1)⁻¹.mulVec u) =
      (numerator L u v).eval t / (denominator L).eval t := by
  rw [numerator_eval, denominator_eval, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, div_eq_mul_inv]
  ring

end RankOneFeedbackPolynomials


open Set
open scoped Matrix.Norms.Operator

namespace StickyKakeya4.RationalFeedbackTimeWindow

lemma matrix_inverse_bounded_on_closed_interval
    (L : Matrix (Fin 3) (Fin 3) ℝ) {a b : ℝ}
    (hdet : ∀ t ∈ Icc a b, (L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ‖(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹‖ ≤ B := by
  have hM : Continuous (fun t : ℝ => L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hi : ContinuousOn (fun t : ℝ => (L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹)
      (Icc a b) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    exact (hM.matrix_det.continuousOn.inv₀ hdet).smul hM.matrix_adjugate.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  exact ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun t ht => (hB t ht).trans (le_max_left _ _)⟩

end StickyKakeya4.RationalFeedbackTimeWindow


open Set Filter Polynomial
open scoped Topology

namespace StickyKakeya4.RationalFeedbackTimeWindow

lemma polynomial_wronskian_ne_zero
    (p q : Polynomial ℝ) (hp : p ≠ 0) (hdeg : p.natDegree < q.natDegree) :
    q.derivative * p - q * p.derivative ≠ 0 := by
  have hq : q ≠ 0 := by
    intro hq
    simp [hq] at hdeg
  intro h
  have heq := congrArg Polynomial.leadingCoeff (sub_eq_zero.mp h)
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_derivative] at heq
  have hp' : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hq' : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hn : (q.natDegree : ℝ) = p.natDegree := by
    apply mul_left_cancel₀ (mul_ne_zero hq' hp')
    nlinarith [heq]
  have hlt : (p.natDegree : ℝ) < q.natDegree := by exact_mod_cast hdeg
  linarith

lemma abs_image_sub_ge_of_abs_deriv_ge
    {f d : ℝ → ℝ} {a b c : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hlower : ∀ t ∈ Icc a b, c ≤ |d t|) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      c * |t - s| ≤ |f t - f s| := by
  suffices h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t →
      c * |t - s| ≤ |f t - f s| by
    intro s hs t ht
    rcases lt_trichotomy s t with hst | hst | hst
    · exact h s hs t ht hst
    · simp [hst]
    · simpa only [abs_sub_comm t s, abs_sub_comm (f t) (f s)] using h t ht s hs hst
  intro s hs t ht hst
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope f d hst
    (hcont.mono hsub) (fun x hx => hderiv x (hsub (Ioo_subset_Icc_self hx)))
  have hlow := hlower x (hsub (Ioo_subset_Icc_self hx))
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hst)] at hlow
  rw [abs_of_pos (sub_pos.mpr hst)]
  exact (le_div_iff₀ (sub_pos.mpr hst)).mp hlow

lemma abs_image_sub_le_of_abs_deriv_le
    {f d : ℝ → ℝ} {a b c : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hupper : ∀ t ∈ Icc a b, |d t| ≤ c) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |f t - f s| ≤ c * |t - s| := by
  suffices h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t →
      |f t - f s| ≤ c * |t - s| by
    intro s hs t ht
    rcases lt_trichotomy s t with hst | hst | hst
    · exact h s hs t ht hst
    · simp [hst]
    · simpa only [abs_sub_comm t s, abs_sub_comm (f t) (f s)] using h t ht s hs hst
  intro s hs t ht hst
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope f d hst
    (hcont.mono hsub) (fun x hx => hderiv x (hsub (Ioo_subset_Icc_self hx)))
  have hupp := hupper x (hsub (Ioo_subset_Icc_self hx))
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hst)] at hupp
  rw [abs_of_pos (sub_pos.mpr hst)]
  exact (div_le_iff₀ (sub_pos.mpr hst)).mp hupp

lemma exists_closed_interval_eventually {P : ℝ → Prop} {x : ℝ}
    (h : ∀ᶠ t in 𝓝 x, P t) :
    ∃ a b : ℝ, a < b ∧ ∀ t ∈ Icc a b, P t := by
  obtain ⟨l, u, hx, hsub⟩ := h.exists_Ioo_subset
  refine ⟨(l + x) / 2, (x + u) / 2, by linarith [hx.1, hx.2], ?_⟩
  intro t ht
  exact hsub ⟨by linarith [ht.1, hx.1], by linarith [ht.2, hx.2]⟩

/-- Every actual open time interval contains a nontrivial closed interval where a
strictly proper nonzero rational function is bounded away from zero, and its
reciprocal is bi-Lipschitz. No good-time interval is assumed. -/
theorem exists_rational_time_window
    (p q : Polynomial ℝ) (hp : p ≠ 0) (hdeg : p.natDegree < q.natDegree)
    {u v : ℝ} (huv : u < v) :
    ∃ a b δ kmin kmax c C : ℝ,
      u < a ∧ a < b ∧ b < v ∧
      0 < δ ∧ 0 < kmin ∧ 0 < kmax ∧ 0 < c ∧ 0 < C ∧
      (∀ t ∈ Icc a b, δ ≤ |q.eval t| ∧
        kmin ≤ |p.eval t / q.eval t| ∧ |p.eval t / q.eval t| ≤ kmax) ∧
      ContinuousOn (fun t => q.eval t / p.eval t) (Icc a b) ∧
      Measurable (fun t => q.eval t / p.eval t) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        c * |t - s| ≤ |q.eval t / p.eval t - q.eval s / p.eval s|) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |q.eval t / p.eval t - q.eval s / p.eval s| ≤ C * |t - s|) := by
  have hq : q ≠ 0 := by intro h; simp [h] at hdeg
  let r := q.derivative * p - q * p.derivative
  have hr : r ≠ 0 := polynomial_wronskian_ne_zero p q hp hdeg
  obtain ⟨x, hx, hxroot⟩ := (Ioo_infinite huv).exists_notMem_finite
    (Polynomial.finite_setOfPred_isRoot (mul_ne_zero (mul_ne_zero hp hq) hr))
  have hxprod : (p.eval x * q.eval x) * r.eval x ≠ 0 := by
    simpa only [mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_mul] using hxroot
  have hpx : p.eval x ≠ 0 := fun h => hxprod (by simp [h])
  have hqx : q.eval x ≠ 0 := fun h => hxprod (by simp [h])
  have hrx : r.eval x ≠ 0 := fun h => hxprod (by simp [h])
  let k : ℝ → ℝ := fun t => p.eval t / q.eval t
  let d : ℝ → ℝ := fun t => r.eval t / p.eval t ^ 2
  have hkx : k x ≠ 0 := div_ne_zero hpx hqx
  have hdx : d x ≠ 0 := div_ne_zero hrx (pow_ne_zero 2 hpx)
  have hkcont : ContinuousAt k x := p.continuous.continuousAt.div q.continuous.continuousAt hqx
  have hdcont : ContinuousAt d x :=
    r.continuous.continuousAt.div (p.continuous.continuousAt.pow 2) (pow_ne_zero 2 hpx)
  have hδ : 0 < |q.eval x| / 2 := half_pos (abs_pos.mpr hqx)
  have hkmin : 0 < |k x| / 2 := half_pos (abs_pos.mpr hkx)
  have hc : 0 < |d x| / 2 := half_pos (abs_pos.mpr hdx)
  have hqevent : ∀ᶠ t in 𝓝 x, |q.eval x| / 2 < |q.eval t| :=
    (continuousAt_const.eventually_lt (q.continuous.continuousAt.abs)
      (by linarith [abs_pos.mpr hqx]))
  have hkevent : ∀ᶠ t in 𝓝 x, |k x| / 2 < |k t| ∧ |k t| < |k x| + 1 := by
    filter_upwards [(show ∀ᶠ t in 𝓝 x, |k x| / 2 < |k t| from
      continuousAt_const.eventually_lt hkcont.abs (by linarith [abs_pos.mpr hkx])),
      (show ∀ᶠ t in 𝓝 x, |k t| < |k x| + 1 from
      hkcont.abs.eventually_lt continuousAt_const (by linarith))] with t ht₁ ht₂
    exact ⟨ht₁, ht₂⟩
  have hdevent : ∀ᶠ t in 𝓝 x, |d x| / 2 < |d t| ∧ |d t| < |d x| + 1 := by
    filter_upwards [(show ∀ᶠ t in 𝓝 x, |d x| / 2 < |d t| from
      continuousAt_const.eventually_lt hdcont.abs (by linarith [abs_pos.mpr hdx])),
      (show ∀ᶠ t in 𝓝 x, |d t| < |d x| + 1 from
      hdcont.abs.eventually_lt continuousAt_const (by linarith))] with t ht₁ ht₂
    exact ⟨ht₁, ht₂⟩
  have hevent : ∀ᶠ t in 𝓝 x,
      t ∈ Ioo u v ∧ p.eval t ≠ 0 ∧ |q.eval x| / 2 < |q.eval t| ∧
      (|k x| / 2 < |k t| ∧ |k t| < |k x| + 1) ∧
      (|d x| / 2 < |d t| ∧ |d t| < |d x| + 1) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2,
      p.continuous.continuousAt.eventually_ne hpx, hqevent, hkevent, hdevent]
      with t ht hp' hq' hk' hd'
    exact ⟨ht, hp', hq', hk', hd'⟩
  obtain ⟨a, b, hab, hgood⟩ := exists_closed_interval_eventually hevent
  have hcont : ContinuousOn (fun t => q.eval t / p.eval t) (Icc a b) :=
    q.continuous.continuousOn.div p.continuous.continuousOn (fun t ht => (hgood t ht).2.1)
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun t => q.eval t / p.eval t) (d t) t := by
    intro t ht
    simpa only [d, r, Polynomial.eval_sub, Polynomial.eval_mul] using
      (q.hasDerivAt t).fun_div (p.hasDerivAt t) (hgood t ht).2.1
  refine ⟨a, b, |q.eval x| / 2, |k x| / 2, |k x| + 1, |d x| / 2, |d x| + 1,
    (hgood a (left_mem_Icc.mpr hab.le)).1.1, hab,
    (hgood b (right_mem_Icc.mpr hab.le)).1.2, hδ, hkmin,
    by positivity, hc, by positivity, ?_, hcont,
    q.continuous.measurable.div p.continuous.measurable, ?_, ?_⟩
  · intro t ht
    exact ⟨(hgood t ht).2.2.1.le, (hgood t ht).2.2.2.1.1.le,
      (hgood t ht).2.2.2.1.2.le⟩
  · exact abs_image_sub_ge_of_abs_deriv_ge hcont hderiv
      (fun t ht => (hgood t ht).2.2.2.2.1.le)
  · exact abs_image_sub_le_of_abs_deriv_le hcont hderiv
      (fun t ht => (hgood t ht).2.2.2.2.2.le)

end StickyKakeya4.RationalFeedbackTimeWindow


namespace StickyKakeya4.RationalFeedbackTimeWindow

open Set Matrix
open scoped Matrix.Norms.Operator

noncomputable def feedbackScalar
    (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  dotProduct v ((L + t • 1)⁻¹.mulVec u)

lemma feedbackScalar_eq_rational
    (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) (t : ℝ) :
    feedbackScalar L u v t = (RankOneFeedbackPolynomials.numerator L u v).eval t /
      (RankOneFeedbackPolynomials.denominator L).eval t :=
  RankOneFeedbackPolynomials.inverse_feedback L u v t

/-- A real 3×3 affine matrix pencil admits a uniformly invertible positive time
window inside every specified actual open interval. -/
theorem exists_matrix_time_window
    (L : Matrix (Fin 3) (Fin 3) ℝ) {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ a b δ B : ℝ, lo < a ∧ a < b ∧ b < hi ∧ 0 < δ ∧ 0 < B ∧
      (∀ t ∈ Icc a b, δ ≤ |(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det|) ∧
      (∀ t ∈ Icc a b, ‖(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹‖ ≤ B) := by
  obtain ⟨a,b,δ,kmin,kmax,c,C,hla,hab,hbh,hδ,hkmin,hkmax,hc,hC,hbounds,_⟩ :=
    exists_rational_time_window 1 (RankOneFeedbackPolynomials.denominator L) one_ne_zero
      (by simp [RankOneFeedbackPolynomials.denominator_natDegree]) hlohi
  have hdet : ∀ t ∈ Icc a b, δ ≤ |(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det| := by
    intro t ht
    simpa only [RankOneFeedbackPolynomials.denominator_eval] using (hbounds t ht).1
  obtain ⟨B,hB,hbound⟩ := matrix_inverse_bounded_on_closed_interval L
    (fun t ht => abs_pos.mp (lt_of_lt_of_le hδ (hdet t ht)))
  exact ⟨a,b,δ,B,hla,hab,hbh,hδ,hB,hdet,hbound⟩

/-- Actual rank-one feedback has either a globally vanishing scalar coefficient,
or a positive actual time window on which its reciprocal is bi-Lipschitz.
All interval, nonsingularity, scalar lower bounds, and inverse operator bounds
are derived from the fixed 3×3 matrix and vectors. -/
theorem actual_feedback_zero_or_time_window
    (L : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ)
    {lo hi : ℝ} (hlohi : lo < hi) :
    (∀ t : ℝ, feedbackScalar L u v t = 0) ∨
    ∃ a b δ kmin kmax c C B : ℝ,
      lo < a ∧ a < b ∧ b < hi ∧
      0 < δ ∧ 0 < kmin ∧ 0 < kmax ∧ 0 < c ∧ 0 < C ∧ 0 < B ∧
      (∀ t ∈ Icc a b, δ ≤ |(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det| ∧
        kmin ≤ |feedbackScalar L u v t| ∧ |feedbackScalar L u v t| ≤ kmax) ∧
      ContinuousOn (fun t => (feedbackScalar L u v t)⁻¹) (Icc a b) ∧
      Measurable (fun t => (feedbackScalar L u v t)⁻¹) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        c * |t - s| ≤ |(feedbackScalar L u v t)⁻¹ - (feedbackScalar L u v s)⁻¹|) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |(feedbackScalar L u v t)⁻¹ - (feedbackScalar L u v s)⁻¹| ≤ C * |t - s|) ∧
      (∀ t ∈ Icc a b, ‖(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹‖ ≤ B) := by
  by_cases hp : RankOneFeedbackPolynomials.numerator L u v = 0
  · left
    intro t
    simp only [feedbackScalar_eq_rational, hp, Polynomial.eval_zero, zero_div]
  right
  have hdeg : (RankOneFeedbackPolynomials.numerator L u v).natDegree <
      (RankOneFeedbackPolynomials.denominator L).natDegree := by
    rw [RankOneFeedbackPolynomials.denominator_natDegree]
    exact (RankOneFeedbackPolynomials.numerator_natDegree L u v).trans_lt (by decide)
  obtain ⟨a,b,δ,kmin,kmax,c,C,hla,hab,hbh,hδ,hkmin,hkmax,hc,hC,hbounds,hcont,hmeas,hco,hLip⟩ :=
    exists_rational_time_window (RankOneFeedbackPolynomials.numerator L u v)
      (RankOneFeedbackPolynomials.denominator L) hp hdeg hlohi
  have hdet : ∀ t ∈ Icc a b, δ ≤ |(L + t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det| := by
    intro t ht
    simpa only [RankOneFeedbackPolynomials.denominator_eval] using (hbounds t ht).1
  obtain ⟨B,hB,hbound⟩ := matrix_inverse_bounded_on_closed_interval L
    (fun t ht => abs_pos.mp (lt_of_lt_of_le hδ (hdet t ht)))
  refine ⟨a,b,δ,kmin,kmax,c,C,B,hla,hab,hbh,hδ,hkmin,hkmax,hc,hC,hB,?_,?_,?_,?_,?_,hbound⟩
  · intro t ht
    exact ⟨hdet t ht, by simpa only [feedbackScalar_eq_rational] using (hbounds t ht).2⟩
  · simpa only [feedbackScalar_eq_rational, inv_div] using hcont
  · simpa only [feedbackScalar_eq_rational, inv_div] using hmeas
  · simpa only [feedbackScalar_eq_rational, inv_div] using hco
  · simpa only [feedbackScalar_eq_rational, inv_div] using hLip

end StickyKakeya4.RationalFeedbackTimeWindow
