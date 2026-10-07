import Theorems.Thm_StickyKakeya4_actual_slope_source
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeEqualRankPlaneTransfer
open Classical StickyKakeya4

lemma projection_residual_eq_infDist (P : Submodule ℝ E4) (v : E4) :
    ‖v-P.starProjection v‖=Metric.infDist v (P:Set E4) := by
  apply le_antisymm
  · apply (Metric.le_infDist (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mpr
    intro y hy
    rw [Submodule.starProjection_minimal,dist_eq_norm]
    have hb : BddBelow (Set.range (fun z : P => ‖v-(z:E4)‖)) := by
      refine ⟨0,?_⟩
      rintro _ ⟨z,rfl⟩
      exact norm_nonneg _
    exact ciInf_le hb ⟨y,hy⟩
  · simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (show P.starProjection v∈P from (P.orthogonalProjectionOnto v).property))

/-- Equal finite dimensions turn a small forward gap into controlled lifting
through the actual orthogonal projection. Injectivity and surjectivity are
proved from the gap, rather than supplied as an inverse-frame certificate. -/
theorem controlled_projection_lift (P Q : Submodule ℝ E4) (epsilon : ℝ)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (he : epsilon ≤ 1/2)
    (hforward : ∀v∈Q,Metric.infDist v (P:Set E4) ≤ epsilon*‖v‖) :
    ∀p : P,∃v : Q,P.orthogonalProjectionOnto (v:E4)=p ∧ ‖v‖ ≤ 2*‖p‖ := by
  let T : Q →ₗ[ℝ] P := P.orthogonalProjectionOnto.toLinearMap.comp Q.subtype
  have hco (v : Q) : ‖v‖ ≤ 2*‖T v‖ := by
    have hf := hforward v v.property
    rw [←projection_residual_eq_infDist] at hf
    have heq : (v:E4)=((v:E4)-P.starProjection v)+P.starProjection v := by abel
    have hn : ‖(v:E4)‖ ≤ ‖(v:E4)-P.starProjection v‖+‖P.starProjection v‖ := by
      exact (congrArg norm heq).le.trans (norm_add_le _ _)
    have hT : ‖P.starProjection v‖=‖T v‖ := rfl
    rw [hT] at hn
    change ‖v‖ ≤ _ at hn
    change _ ≤ epsilon*‖v‖ at hf
    nlinarith [norm_nonneg v]
  have hinj : Function.Injective T := by
    intro v w hvw
    have hz : T (v-w)=0 := by rw [map_sub,hvw,sub_self]
    have hn := hco (v-w)
    rw [hz,norm_zero,mul_zero] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hinj
  intro p
  obtain ⟨v,hv⟩ := hsurj p
  refine ⟨v,hv,?_⟩
  simpa only [hv] using hco v

/-- A forward span bound controls the whole equal-dimensional old plane.
The large-gap case is handled by the zero point; no extra smallness or
unverified invertibility assumption is needed in this final estimate. -/
theorem transfer_near_plane (P Q : Submodule ℝ E4) (epsilon r : ℝ)
    (he : 0 ≤ epsilon) (hr : 0 ≤ r)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q)
    (hforward : ∀v∈Q,Metric.infDist v (P:Set E4) ≤ epsilon*‖v‖)
    (w : E4) (hw : Metric.infDist w (P:Set E4) ≤ r) :
    Metric.infDist w (Q:Set E4) ≤ r+2*epsilon*‖w‖ := by
  by_cases hsmall : epsilon ≤ 1/2
  · let p : P := P.orthogonalProjectionOnto w
    obtain ⟨v,hv,hvnorm⟩ := controlled_projection_lift P Q epsilon hdim hsmall hforward p
    have hp : (p:E4)=P.starProjection w := rfl
    have hpv : P.starProjection (v:E4)=(p:E4) := congrArg (fun z : P => (z:E4)) hv
    have hpnorm : ‖p‖ ≤ ‖w‖ := P.norm_orthogonalProjectionOnto_apply_le w
    have hvbound : ‖v‖ ≤ 2*‖w‖ := hvnorm.trans (mul_le_mul_of_nonneg_left hpnorm (by norm_num))
    have hfirst : ‖w-(p:E4)‖ ≤ r := by rw [hp,projection_residual_eq_infDist]; exact hw
    have hsecond : ‖(p:E4)-(v:E4)‖ ≤ epsilon*‖v‖ := by
      rw [norm_sub_rev,←hpv,projection_residual_eq_infDist]
      exact hforward v v.property
    apply (Metric.infDist_le_dist_of_mem v.property).trans
    rw [dist_eq_norm]
    have heq : w-(v:E4)=(w-(p:E4))+((p:E4)-(v:E4)) := by abel
    rw [heq]
    calc
      _ ≤ ‖w-(p:E4)‖+‖(p:E4)-(v:E4)‖ := norm_add_le _ _
      _ ≤ r+epsilon*‖v‖ := add_le_add hfirst hsecond
      _ ≤ r+epsilon*(2*‖w‖) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hvbound he)
      _ = _ := by ring
  · have hehalf : 1/2 ≤ epsilon := (lt_of_not_ge hsmall).le
    apply (Metric.infDist_le_dist_of_mem Q.zero_mem).trans
    rw [dist_zero_right]
    nlinarith [norm_nonneg w]

end NativeEqualRankPlaneTransfer
