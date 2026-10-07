import Theorems.Thm_StickyKakeya4_native_reference_slice_ad
import Theorems.Thm_StickyKakeya4_native_combined_parent_profiles

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceSliceBudgetAlgebra
open NativeReferenceColumnExponents NativeAnisotropicGlobalSourceBridge
open NativeAnisotropicPairNumerator NativeActivePhasePopulation

def population (delta eta lambda b F G : ℝ) : ℝ := lambda*b*delta^eta/(2*F*G)
def columnEpsilon (delta lambda c1 c2 : ℝ) : ℝ := lambda*delta^(c1+3*c2)
def profileLower (delta mu eps tau c1 w : ℝ) : ℝ :=
  (eps/comparisonCost)*(mu/rowConstant)*delta^(tau+c1+10*w)
def profileUpper (delta eps tau : ℝ) : ℝ := (comparisonCost/eps)*delta^(-3*tau)
def ratioConstant : ℝ := 4*43904*pairUpperConstant*rowConstant*comparisonCost^2

lemma ratioConstant_pos : 0 < ratioConstant := by
  have hA := pairUpperConstant_pos
  have hB := rowConstant_pos
  have hC := comparisonCost_pos
  unfold ratioConstant
  positivity

/-- Exact ratio of the actual reference count coefficients. Both occurrences
of the selected-parent population remain visible. -/
lemma reference_ratio {delta zeta mu eps tau c1 w : ℝ}
    (hd : 0 < delta) (hmu : 0 < mu) (heps : 0 < eps) :
    upperCountCoefficient delta zeta (profileLower delta mu eps tau c1 w)/
        lowerCountCoefficient delta zeta mu (profileUpper delta eps tau) =
      (43904*pairUpperConstant*rowConstant*comparisonCost^2)*
        delta^(-(4*zeta+4*tau+c1+10*w))/(mu^2*eps^2) := by
  have hC := comparisonCost_pos
  have hrow := rowConstant_pos
  have hp : delta^(-2*zeta)*delta^(-3*tau)/
      (delta^(2*zeta)*delta^(tau+c1+10*w))=delta^(-(4*zeta+4*tau+c1+10*w)) := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd,←Real.rpow_sub hd]
    congr 1
    ring
  calc
    _ = (43904*pairUpperConstant*rowConstant*comparisonCost^2)*
        (delta^(-2*zeta)*delta^(-3*tau)/(delta^(2*zeta)*delta^(tau+c1+10*w)))/(mu^2*eps^2) := by
      unfold upperCountCoefficient lowerCountCoefficient profileLower profileUpper
      field_simp
    _ = _ := by rw [hp]

/-- Substitute the actual population and short-row retention. Writing the
two eta powers inside the first-cost square prevents a sign loss. -/
lemma actual_reference_ratio {delta eta zeta lambda b F G Q tau c1 c2 w : ℝ}
    (hd : 0 < delta) (hlambda : 0 < lambda) (hb : 0 < b) (hF : 0 < F) (hG : 0 < G) :
    Q^4*(upperCountCoefficient delta zeta
        (profileLower delta (population delta eta lambda b F G)
          (columnEpsilon delta lambda c1 c2) tau c1 w)/
      lowerCountCoefficient delta zeta (population delta eta lambda b F G)
        (profileUpper delta (columnEpsilon delta lambda c1 c2) tau)) =
      ratioConstant*(F*delta^(-eta))^2*(G*Q^2)^2*
        delta^(-(4*zeta+4*tau+3*c1+6*c2+10*w))/(lambda^4*b^2) := by
  have hmu : 0 < population delta eta lambda b F G := by unfold population; positivity
  have heps : 0 < columnEpsilon delta lambda c1 c2 := by unfold columnEpsilon; positivity
  rw [reference_ratio hd hmu heps]
  have hp : delta^(-(4*zeta+4*tau+c1+10*w))/(delta^(c1+3*c2))^2 =
      delta^(-(4*zeta+4*tau+3*c1+6*c2+10*w)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hd.le,←Real.rpow_sub hd]
    congr 1
    ring
  calc
    _ = ratioConstant*(F*delta^(-eta))^2*(G*Q^2)^2*
        (delta^(-(4*zeta+4*tau+c1+10*w))/(delta^(c1+3*c2))^2)/(lambda^4*b^2) := by
      unfold population columnEpsilon ratioConstant
      rw [Real.rpow_neg hd.le eta]
      field_simp
      ring
    _ = _ := by rw [hp]

end NativeReferenceSliceBudgetAlgebra
