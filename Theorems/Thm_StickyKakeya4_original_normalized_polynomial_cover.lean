import Theorems.Thm_StickyKakeya4_original_uniform_polynomial_iteration
import Theorems.Thm_StickyKakeya4_original_tensor_projection_selection
import Theorems.Thm_StickyKakeya4_original_coefficient_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped Pointwise BigOperators
namespace OriginalNormalizedPolynomialCover
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy OriginalTensorFrostman
open OriginalTensorProjectionSelection OriginalUniformPolynomialIteration OriginalPolynomialWordLength

def initialCover (n : ℕ) : ℝ := 1/(128*(2:ℝ)^(n+1))

/-- The literal K*=2 original normalized scalar profile supplies the
initial tensor image internally. The total word length, homogeneous degree
2^n and positive interval-cover constant are all chosen before the dyadic
mesh, original carrier and its actual endpoints. -/
theorem exists_fixed_polynomial_cover_of_normalized_profile (n : ℕ) (u d0 : ℝ)
    (hmu : 2 ≤ u*((n+1:ℕ):ℝ)) (hd0 : 0 < d0) :
    ∃ T : ℕ,0 < T ∧ ∃ C : ℝ,0 < C ∧
      ∀ (k : ℕ) (A : Finset ℝ) (lo d : ℝ),
        lo∈A → lo+d∈A → d0 ≤ d →
        (∀ a∈A,lo ≤ a ∧ a ≤ lo+d) → (∀ a∈A,|a| ≤ 1) →
        ScalarFrostman A (ProjectionAnnulusEnergy.mesh k) 2 u →
        C ≤ ProjectionAnnulusEnergy.mesh k*
          ((polynomialWords A T (2^n)).image (rounded (ProjectionAnnulusEnergy.mesh k))).card := by
  have hL : 0 < initialCover n := by unfold initialCover; positivity
  obtain ⟨T,hT,C,hC,hcover⟩ := exists_fixed_original_polynomial_word_cover n 1 d0 (initialCover n)
    (by norm_num) hd0 hL
  refine ⟨T,hT,C,hC,?_⟩
  intro k A lo d hlo hhi hdiam hbox habs hprofile
  obtain ⟨v,_hvgrid,hv,himage⟩ := exists_original_tensor_projection A n k
    ⟨lo,hlo⟩ (by norm_num : (1:ℝ) ≤ 2) hmu habs hprofile
  have hmesh1 : ProjectionAnnulusEnergy.mesh k ≤ 1 := by
    unfold ProjectionAnnulusEnergy.mesh
    exact pow_le_one₀ (by norm_num) (by norm_num)
  exact hcover (ProjectionAnnulusEnergy.mesh k) A v lo d (ProjectionAnnulusEnergy.mesh_pos k)
    hmesh1 hv hlo hhi hdiam hbox habs himage

/-- The absolute profile at an available fixed radius constructs genuine
original extrema with the required diameter, without a diameter input. -/
theorem exists_original_profile_interval_endpoints (A : Finset ℝ) (delta u d0 : ℝ)
    (hA : A.Nonempty) (hmesh : delta ≤ d0) (hd01 : d0 ≤ 1)
    (hsmall : 2*d0^u < 1) (hprofile : ScalarFrostman A delta 2 u) :
    ∃ lo d : ℝ,lo∈A ∧ lo+d∈A ∧ d0 ≤ d ∧
      (∀ a∈A,lo ≤ a ∧ a ≤ lo+d) := by
  obtain ⟨x,hx,y,hy,hsep⟩ := OriginalCoefficientNormalization.exists_original_profile_separated_pair
    A hA hmesh hd01 hsmall hprofile
  let lo := A.min' hA
  let hi := A.max' hA
  have hlo : lo∈A := Finset.min'_mem A hA
  have hhi : hi∈A := Finset.max'_mem A hA
  have hb (a : ℝ) (ha : a∈A) : lo ≤ a ∧ a ≤ hi :=
    ⟨Finset.min'_le A a ha,Finset.le_max' A a ha⟩
  have hxy : |x-y| ≤ hi-lo := by
    apply abs_le.mpr
    constructor <;> linarith only [(hb x hx).1,(hb x hx).2,(hb y hy).1,(hb y hy).2]
  have he : lo+(hi-lo)=hi := by ring
  refine ⟨lo,hi-lo,hlo,?_,hsep.le.trans hxy,?_⟩
  · simpa only [he] using hhi
  · intro a ha
    rw [he]
    exact hb a ha

/-- A fixed absolute normalized profile constructs the original scalar
polynomial cover, including its initial diameter and tensor projection.
Only n and the positive profile exponent precede the fixed word constants. -/
theorem exists_fixed_polynomial_cover_of_absolute_profile (n : ℕ) (u : ℝ)
    (hu : 0 < u) (hmu : 2 ≤ u*((n+1:ℕ):ℝ)) :
    ∃ T : ℕ,0 < T ∧ ∃ C : ℝ,0 < C ∧
      ∀ (k : ℕ) (A : Finset ℝ),A.Nonempty →
        ProjectionAnnulusEnergy.mesh k ≤ (1/4:ℝ)^(1/u) →
        (∀ a∈A,|a| ≤ 1) → ScalarFrostman A (ProjectionAnnulusEnergy.mesh k) 2 u →
        C ≤ ProjectionAnnulusEnergy.mesh k*
          ((polynomialWords A T (2^n)).image (rounded (ProjectionAnnulusEnergy.mesh k))).card := by
  have hd := OriginalCoefficientNormalization.absolute_diameter_threshold hu
  obtain ⟨T,hT,C,hC,hcover⟩ := exists_fixed_polynomial_cover_of_normalized_profile n u
    ((1/4:ℝ)^(1/u)) hmu hd.1
  refine ⟨T,hT,C,hC,?_⟩
  intro k A hA hmesh habs hprofile
  obtain ⟨lo,d,hlo,hhi,hdiam,hbox⟩ := exists_original_profile_interval_endpoints A
    (ProjectionAnnulusEnergy.mesh k) u ((1/4:ℝ)^(1/u)) hA hmesh hd.2.1 hd.2.2 hprofile
  exact hcover k A lo d hlo hhi hdiam hbox habs hprofile

end OriginalNormalizedPolynomialCover
