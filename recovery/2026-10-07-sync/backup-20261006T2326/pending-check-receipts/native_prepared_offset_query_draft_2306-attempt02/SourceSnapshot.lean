import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu
import Theorems.Thm_StickyKakeya4_native_actual_configured_base

/- UNVERIFIED fixed-size pre-T coherence query for the actual later d.
Only G+1 depths are installed. Their values may use the already chosen
base exponent u; no log(source)-sized relation menu is introduced.
The actual later intermediate thickness is d=64/2^b. Its512d query is
bracketed from the original prepared menu, and the gap remains explicit.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativePreparedOffsetQueryDraft2306
open NativeFixedSizeScaleMenu

def depth (G u : ℕ) (j : Fin (G+1)) : ℕ := 6+(schedule G u j).val

/-- Actual tau<=1 and final native sigma<=1 force the intermediate dyadic
depth into the queried range. Here tau=4096w and sigma=d/w literally. -/
theorem intermediate_depth_lower (b c : ℕ)
    (hSigma : (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64) ≤ 1)
    (hTau : 4096*(64/((2^c:ℕ):ℝ)) ≤ 1) : 18 ≤ b := by
  have hProduct := mul_le_mul hSigma hTau
    (by positivity : (0:ℝ) ≤ 4096*(64/((2^c:ℕ):ℝ))) (by norm_num : (0:ℝ) ≤ 1)
  have hIdentity : (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)*
      (4096*(64/((2^c:ℕ):ℝ)))=262144/((2^b:ℕ):ℝ) := by
    have hc : ((2^c:ℕ):ℝ)≠0 := by positivity
    field_simp [hc]
    ring
  rw [hIdentity,one_mul] at hProduct
  have hPow : (262144:ℝ) ≤ ((2^b:ℕ):ℝ) := (div_le_one (by positivity)).mp hProduct
  have hNat : (2:ℕ)^18 ≤ 2^b := by norm_num; exact_mod_cast hPow
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1<(2:ℕ))).mp hNat

/-- The actual base chooser gives error<=base and u+6<=m. Thus EVERY
prepared depth satisfies the original one-T coherence query guards. -/
theorem coherence_depth_guards (G u m : ℕ) (hu : u+6 ≤ m) (error : ℝ)
    (hError : error ≤ (2:ℝ)⁻¹^u) (j : Fin (G+1)) :
    6 ≤ depth G u j ∧ depth G u j ≤ m+6 ∧
      error ≤ 64/((2^(depth G u j):ℕ):ℝ) := by
  have hj : (schedule G u j).val ≤ u := Nat.le_of_lt_succ (schedule G u j).isLt
  refine ⟨by dsimp only [depth]; omega,by dsimp only [depth]; omega,?_⟩
  have hScale : (2:ℝ)⁻¹^u=64/((2^(u+6):ℕ):ℝ) := by
    push_cast
    rw [pow_add,inv_pow]
    norm_num
    ring
  apply hError.trans
  rw [hScale]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ))
    (show depth G u j ≤ u+6 by dsimp only [depth]; omega)

/-- The prepared predecessor is chosen only after d exists, while the
menu itself was fixed before T. The real radius ratio is512 times its
literal dyadic gap, and therefore at most1024 base^(-1/G). -/
theorem exists_actual_offset_query (G u b : ℕ) (hG : 0<G) (hu : 0<u)
    (hb : 15 ≤ b) (hbu : b ≤ u+15) :
    ∃j : Fin (G+1),depth G u j ≤ b-9 ∧
      (b-9)-depth G u j ≤ u/G+1 ∧
      512*(64/((2^b:ℕ):ℝ)) ≤ 64/((2^(depth G u j):ℕ):ℝ) ∧
      (64/((2^(depth G u j):ℕ):ℝ))/(64/((2^b:ℕ):ℝ)) ≤ 
        1024*((2:ℝ)⁻¹^u)^(-(1/(G:ℝ))) := by
  obtain ⟨j,hPred,hGap,hGapReal⟩ := exists_predecessor G u (b-15) hG hu (by omega)
  have hDb : depth G u j ≤ b := by dsimp only [depth]; omega
  have hGapEq : b-depth G u j=9+((b-15)-(schedule G u j).val) := by
    dsimp only [depth]
    omega
  have hRatio : (64/((2^(depth G u j):ℕ):ℝ))/(64/((2^b:ℕ):ℝ))=
      512*((2^((b-15)-(schedule G u j).val):ℕ):ℝ) := by
    have hPow : (2^b:ℕ)=2^(depth G u j)*2^(b-depth G u j) := by
      rw [←pow_add,Nat.add_sub_of_le hDb]
    rw [hPow,hGapEq,pow_add]
    push_cast
    norm_num
    field_simp
  have hPower := dyadic_gap_power u (b-15) (schedule G u j).val G hG rfl hGapReal
  have hRlo : (1:ℝ) ≤ ((2^((b-15)-(schedule G u j).val):ℕ):ℝ) := by
    exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
  refine ⟨j,by dsimp only [depth]; omega,by dsimp only [depth]; omega,?_,?_⟩
  · have hLower : (512:ℝ) ≤ (64/((2^(depth G u j):ℕ):ℝ))/(64/((2^b:ℕ):ℝ)) := by
      rw [hRatio]
      nlinarith only [hRlo]
    exact (le_div_iff₀ (by positivity : (0:ℝ)<64/((2^b:ℕ):ℝ))).mp hLower
  · rw [hRatio]
    exact (mul_le_mul_of_nonneg_left hPower (by norm_num)).trans_eq (by ring)

/-- The real alignment output pays the fixed-menu gap at native sigma.
This uses base=64eps and sigma<=eps^(chi/2), with no parent-input window. -/
theorem gap_at_native_mesh (G : ℕ) (hG : 0<G) {base eps sigma chi : ℝ}
    (hEps : 0<eps) (hSigma : 0<sigma) (hChi : 0<chi)
    (hBase : base=64*eps) (hOutput : sigma ≤ eps^(chi/2)) :
    base^(-(1/(G:ℝ))) ≤ sigma^(-(2/((G:ℝ)*chi))) := by
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hBaseLower : eps ≤ base := by rw [hBase]; linarith only [hEps]
  have hFirst := Real.rpow_le_rpow_of_nonpos hEps hBaseLower
    (show -(1/(G:ℝ)) ≤ 0 from neg_nonpos.mpr (by positivity))
  have hSecond := Real.rpow_le_rpow_of_nonpos hSigma hOutput
    (show -(2/((G:ℝ)*chi)) ≤ 0 from neg_nonpos.mpr (by positivity))
  have hIdentity : (eps^(chi/2))^(-(2/((G:ℝ)*chi)))=eps^(-(1/(G:ℝ))) := by
    rw [←Real.rpow_mul hEps.le]
    congr 1
    field_simp [hGr.ne',hChi.ne']
  rw [hIdentity] at hSecond
  exact hFirst.trans hSecond

/-- Source-scale version of the actual prepared query. Its squared offset
menu cost is still the square of this explicit ratio; no subpower cost is
asserted without a numerical lower bound on the pre-source G. -/
theorem exists_native_paid_query (G u b : ℕ) (hG : 0<G) (hu : 0<u)
    (hb : 15 ≤ b) (hbu : b ≤ u+15) {eps sigma chi : ℝ}
    (hEps : 0<eps) (hSigma : 0<sigma) (hChi : 0<chi)
    (hBase : (2:ℝ)⁻¹^u=64*eps) (hOutput : sigma ≤ eps^(chi/2)) :
    ∃j : Fin (G+1),depth G u j ≤ b-9 ∧
      (b-9)-depth G u j ≤ u/G+1 ∧
      512*(64/((2^b:ℕ):ℝ)) ≤ 64/((2^(depth G u j):ℕ):ℝ) ∧
      (64/((2^(depth G u j):ℕ):ℝ))/(64/((2^b:ℕ):ℝ)) ≤ 
        1024*sigma^(-(2/((G:ℝ)*chi))) := by
  obtain ⟨j,hDepth,hGap,hQuery,hRatio⟩ := exists_actual_offset_query G u b hG hu hb hbu
  exact ⟨j,hDepth,hGap,hQuery,hRatio.trans
    (mul_le_mul_of_nonneg_left (gap_at_native_mesh G hG hEps hSigma hChi hBase hOutput) (by norm_num))⟩

end NativePreparedOffsetQueryDraft2306
