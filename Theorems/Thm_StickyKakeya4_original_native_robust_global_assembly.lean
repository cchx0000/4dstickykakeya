import Theorems.Thm_StickyKakeya4_original_native_robust_residuals
import Theorems.Thm_StickyKakeya4_original_local_to_global_robust_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open Classical

namespace OriginalNativeRobustGlobalAssembly
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian OriginalNativeRobustResiduals
open OriginalLocalToGlobalRobustProjection

/-- Apply a uniform native local theorem to actual residuals, paying
their profile loss and square-root population loss explicitly. The final
statement is robust for EVERY dense original query and most original slopes. -/
theorem original_global_of_uniform_local (P : Finset Point) (C : Finset ℝ)
    {delta e u : ℝ} (hP : P.Nonempty) (hd : 0<delta) (hd1 : delta≤1)
    (he : 0<e) (hsmall : delta^(e/4)≤1/4)
    (hprofile : PointFrostman P delta (delta^(-e/4)) u)
    (hlocal : ∀ R : Finset Point, R.Nonempty → R⊆P →
      PointFrostman R delta (delta^(-e)) u →
      ∃ F : Finset Point, F⊆R ∧ F.Nonempty ∧
        ∃ Good : Finset ℝ, Good⊆C ∧ (1-delta^e)*(C.card:ℝ)≤Good.card ∧
          ∀ c∈Good, ∀ Q : Finset Point, Q⊆F → delta^e*(F.card:ℝ)≤Q.card →
            delta^(-e)*Real.sqrt R.card < (alphabet Q delta c).card) :
    ∃ Good : Finset ℝ, Good⊆C ∧ (1-delta^(e/4))*(C.card:ℝ)≤Good.card ∧
      ∀ c∈Good, ∀ Q : Finset Point, Q⊆P → delta^(e/4)*(P.card:ℝ)≤Q.card →
        delta^(-e/4)*Real.sqrt P.card < (alphabet Q delta c).card := by
  have hlocal' : ∀ R : Finset Point, R⊆P → delta^(e/2)*(P.card:ℝ)≤R.card →
      ∃ F : Finset Point, F⊆R ∧ F.Nonempty ∧
        ∃ Good : Finset ℝ, Good⊆C ∧ (1-delta^e)*(C.card:ℝ)≤Good.card ∧
          ∀ c∈Good, ∀ Q : Finset Point, Q⊆F → delta^e*(F.card:ℝ)≤Q.card →
            delta^(-e/4)*Real.sqrt P.card < (alphabet Q delta c).card := by
    intro R hRP hRmass
    have hRpos : (0:ℝ)<R.card := (mul_pos (Real.rpow_pos_of_pos hd _)
      (Nat.cast_pos.mpr hP.card_pos)).trans_le hRmass
    have hRnon : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hRpos)
    have hRprofile := original_robust_residual_profile P R hd hd1 he hRP hRmass hprofile
    obtain ⟨F,hFR,hFnon,Good,hGC,hGmass,hgood⟩ := hlocal R hRnon hRP hRprofile
    have hthreshold := original_robust_residual_threshold hd hd1 he (Nat.cast_nonneg P.card) hRmass
    exact ⟨F,hFR,hFnon,Good,hGC,hGmass,fun c hc Q hQ hmass =>
      hthreshold.trans_lt (hgood c hc Q hQ hmass)⟩
  obtain ⟨Good,hGC,hGmass,hgood⟩ := exists_original_global_robust_projection P C
    (fun c Q => (alphabet Q delta c).card) hP (Real.rpow_nonneg hd.le e)
    (Real.rpow_pos_of_pos hd (e/2)) (Real.rpow_nonneg hd.le e)
    (original_robust_global_query_slack hd hsmall)
    (fun c Q R hQR => original_projection_cover_mono Q R delta c hQR) hlocal'
  have hid : delta^e/delta^(e/2)=delta^(e/2) := by
    rw [← Real.rpow_sub hd]
    congr 1
    ring
  rw [hid] at hGmass
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 (show e/4≤e/2 by linarith only [he])
  have hm := mul_le_mul_of_nonneg_right (show 1-delta^(e/4)≤1-delta^(e/2) by linarith only [hp])
    (Nat.cast_nonneg C.card)
  exact ⟨Good,hGC,hm.trans hGmass,hgood⟩

end OriginalNativeRobustGlobalAssembly
