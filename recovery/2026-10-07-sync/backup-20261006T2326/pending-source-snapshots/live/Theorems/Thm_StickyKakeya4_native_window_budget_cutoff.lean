import Theorems.Thm_StickyKakeya4_native_window_power_payment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
namespace NativeWindowBudgetCutoff
open NativeWindowPowerPayment

/-- Chosen before the native source. The exponent 36*geometryTolerance
remains in the source power payment, rather than hidden in this constant. -/
def sourceCutoff (epsilon c geometryTolerance : ℝ) (he : 0 < epsilon) (hc : 0 < c) : ℝ :=
  Classical.choose (exists_source_product_cutoff (epsilon / 4) c 3 (2 * geometryTolerance)
    (by positivity) hc (by norm_num))

lemma sourceCutoff_spec (epsilon c geometryTolerance : ℝ) (he : 0 < epsilon) (hc : 0 < c) :
    0 < sourceCutoff epsilon c geometryTolerance he hc ∧
    sourceCutoff epsilon c geometryTolerance he hc ≤ 1 ∧
    ∀ delta : ℝ, 0 < delta → delta ≤ sourceCutoff epsilon c geometryTolerance he hc →
      ∀ rho r a : ℝ, 0 < rho → c ^ 3 / 8 ≤ a → r ≤ delta ^ a → rho ^ 2 ≤ 6144 * r →
        productCost 3 (2 * geometryTolerance) ≤ rho ^ (-(epsilon / 4)) :=
  Classical.choose_spec (exists_source_product_cutoff (epsilon / 4) c 3 (2 * geometryTolerance)
    (by positivity) hc (by norm_num))

end NativeWindowBudgetCutoff
