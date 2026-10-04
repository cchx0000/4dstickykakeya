import Theorems.Thm_StickyKakeya4_gkz_grid_code_perturbation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalPolynomialElimination
open ActualRoundedAdditiveEnergy GKZGridCodePerturbation

/-- Eliminate one actual coefficient using the original approximate linear
relation. The identity retains the full error term. -/
lemma original_coefficient_elimination {I : Type*} [Fintype I] [DecidableEq I]
    (v c a : I → ℝ) (j : I) :
    c j*(∑ i, v i*a i)-
      (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j))=
        a j*(∑ i, v i*c i) := by
  have hsum : (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j))=
      ∑ i, v i*(c j*a i-c i*a j) := by
    have he := Finset.sum_erase_add Finset.univ (fun i => v i*(c j*a i-c i*a j))
      (Finset.mem_univ j)
    simpa only [sub_self,mul_zero,add_zero] using he
  rw [hsum]
  have htotal : (∑ i, v i*(c j*a i-c i*a j))=
      c j*(∑ i, v i*a i)-a j*(∑ i, v i*c i) := by
    calc
      _ = ∑ i, (c j*(v i*a i)-a j*(v i*c i)) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
  rw [htotal]
  ring

/-- A nonzero original dilation followed by a bounded perturbation retains
an explicit fraction of the actual original occupied floor cells. -/
theorem original_dilation_perturbation_cover {X : Type*} (P : Finset X)
    (f g : X → ℝ) {delta e E : ℝ} (hd : 0 < delta) (he : e≠0) (hE : 0 ≤ E)
    (herr : ∀ p∈P, |e*f p-g p| ≤ E*delta) :
    |e| *((P.image (fun p => rounded delta (f p))).card:ℝ) ≤
      (2+2*|e|)*(2*E+4)*(P.image (fun p => rounded delta (g p))).card := by
  have hpert := floor_image_le_code_image P (fun p => e*f p)
    (fun p => rounded delta (g p)) hd (show 0 ≤ E+1 by linarith) (by
      intro p hp
      have hh := herr p hp
      have hr := round_error hd (g p)
      have hr' : |g p-delta*(rounded delta (g p):ℝ)| ≤ delta := by
        rw [abs_of_nonneg hr.1]
        exact hr.2.le
      have ht := abs_sub_le (e*f p) (g p) (delta*(rounded delta (g p):ℝ))
      nlinarith only [hh,hr',ht])
  have hinv : |e⁻¹| ≤ |e|⁻¹ := by rw [abs_inv]
  have hdil := bounded_dilation_floor_image P (fun p => e*f p) hd
    (show 0 ≤ |e|⁻¹ by positivity) hinv
  have hid (p : X) : e⁻¹*(e*f p)=f p := by field_simp
  simp only [hid] at hdil
  have hepos : 0 < |e| := abs_pos.mpr he
  have hchain := hdil.trans (mul_le_mul_of_nonneg_left hpert
    (show 0 ≤ 2*|e|⁻¹+2 by positivity))
  have hh := mul_le_mul_of_nonneg_left hchain hepos.le
  have hfactor : |e| *((2*|e|⁻¹+2)*(2*(E+1)+2))=(2+2*|e|)*(2*E+4) := by
    field_simp
    ring
  have hfactor' := congrArg (fun t : ℝ =>
    t*(P.image (fun p => rounded delta (g p))).card) hfactor
  nlinarith only [hh,hfactor']

/-- Finite dimension reduction at the same literal mesh: every new value
uses the original coordinates and the original relation coefficients. -/
theorem original_polynomial_projection_elimination
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Finset (I → ℝ)) (v c : I → ℝ) (j : I)
    {delta B : ℝ} (hd : 0 < delta) (hB : 0 ≤ B) (hc : c j≠0)
    (hbox : ∀ a∈P, |a j| ≤ B) (hrelation : |∑ i, v i*c i| ≤ delta) :
    |c j| *((P.image (fun a => rounded delta (∑ i, v i*a i))).card:ℝ) ≤
      (2+2*|c j|)*(2*B+4)*
        (P.image (fun a => rounded delta
          (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j)))).card := by
  apply original_dilation_perturbation_cover P _ _ hd hc hB
  intro a ha
  rw [original_coefficient_elimination,abs_mul]
  exact mul_le_mul (hbox a ha) hrelation (abs_nonneg _) hB

end OriginalPolynomialElimination
