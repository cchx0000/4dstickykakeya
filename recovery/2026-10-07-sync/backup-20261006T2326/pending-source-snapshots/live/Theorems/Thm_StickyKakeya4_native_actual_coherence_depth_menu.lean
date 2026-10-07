import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points

/- A fixed-cardinality coherence menu, chosen before rank parameters.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualCoherenceDepthMenu
open NativeFixedSizeScaleMenu NativeReferenceXYGridPoints

/-- J is fixed before the source. Only the endpoint u changes with the source. -/
def depth (J u : ℕ) (i : Fin (J+1)) : ℕ :=
  6+(schedule J u i).val

lemma depth_bounds (J u : ℕ) (i : Fin (J+1)) :
    6 ≤ depth J u i ∧ depth J u i ≤ u+6 := by
  have hh := (schedule J u i).isLt
  unfold depth
  omega

lemma depth_zero (J u : ℕ) : depth J u 0=6 := by
  simp [depth,schedule_zero]

lemma depth_last (J u : ℕ) (hJ : 0 < J) : depth J u (Fin.last J)=u+6 := by
  simp only [depth,schedule_last J u hJ]
  omega

/-- Every selected physical width lies above the actual base. -/
lemma base_le_width (J u : ℕ) (i : Fin (J+1)) :
    (2:ℝ)⁻¹^u ≤ 64/((2^(depth J u i):ℕ):ℝ) := by
  have heq : (2:ℝ)⁻¹^u=64/((2^(u+6):ℕ):ℝ) := by
    push_cast
    simp only [pow_add,inv_pow]
    norm_num
    field_simp
  rw [heq]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) (depth_bounds J u i).2

/-- The actual base envelope supplies every menu guard in the one-T
constructor; no source-dependent menu count or extra geometry premise occurs. -/
theorem source_guards (J u m R0 : ℕ) (epsilon : ℝ)
    (hum : u+6 ≤ m) (hbase : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (herror : (5/4:ℝ)*(rho m)^(1-2*epsilon) ≤ mu m*(R0:ℝ)) :
    (∀i,6 ≤ depth J u i ∧ depth J u i ≤ m+6) ∧
    (∀i,(5/4:ℝ)*(rho m)^(1-2*epsilon) ≤ 64/((2^(depth J u i):ℕ):ℝ)) := by
  refine ⟨?_,?_⟩
  · intro i
    have hh := depth_bounds J u i
    omega
  · intro i
    rw [hbase] at herror
    exact herror.trans (base_le_width J u i)

/-- The logarithmic gap is paid using fixed J, independently of the
first-source menu size g. -/
theorem exists_preceding_depth (J u m : ℕ) (hJ : 0 < J) (hu : 0 < u)
    (hm0 : 6 ≤ m) (hmu : m ≤ u+6) :
    ∃i : Fin (J+1),depth J u i ≤ m ∧ m-depth J u i ≤ u/J+1 := by
  obtain ⟨i,hlo,hgap,_hgapReal⟩ := exists_predecessor J u (m-6) hJ hu (by omega)
  refine ⟨i,?_,?_⟩ <;> unfold depth <;> omega

end NativeActualCoherenceDepthMenu
