import Theorems.Thm_StickyKakeya4_native_projector_cell_chart
import Theorems.Thm_StickyKakeya4_native_horizontal_grain_slice

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeProjectorGraphMap
open Classical Finset StickyKakeya4 NativeEqualRankPlaneTransfer NativeProjectorCellChart
open NativeHorizontalGrainSlice SelfUniform
open scoped BigOperators

/-- Actual orthogonal projection restricted to the candidate plane. -/
def projectionMap (P Q : Submodule ℝ E4) : Q →ₗ[ℝ] P :=
  P.orthogonalProjectionOnto.toLinearMap.comp Q.subtype

lemma projectionMap_bijective (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) :
    Function.Bijective (projectionMap P Q) := by
  have hsurj : Function.Surjective (projectionMap P Q) := by
    intro p
    obtain ⟨v,hv,_hnorm⟩ := same_cell_projection_lift P Q hdim hcell p
    exact ⟨v,hv⟩
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mpr hsurj,hsurj⟩

def projectionEquiv (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) : Q ≃ₗ[ℝ] P :=
  LinearEquiv.ofBijective (projectionMap P Q) (projectionMap_bijective P Q hdim hcell)

lemma projectionEquiv_apply (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (v : Q) :
    projectionEquiv P Q hdim hcell v=P.orthogonalProjectionOnto (v:E4) := rfl

/-- Norm control for the derived inverse, with no inverse-frame assumption. -/
lemma inverse_norm (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (p : P) :
    ‖(projectionEquiv P Q hdim hcell).symm p‖ ≤ 2*‖p‖ := by
  obtain ⟨v,hv,hnorm⟩ := same_cell_projection_lift P Q hdim hcell p
  have hv' : projectionEquiv P Q hdim hcell v=p := hv
  rw [←hv',LinearEquiv.symm_apply_apply]
  simpa only [hv'] using hnorm

lemma inverse_projection (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (p : P) :
    P.starProjection (((projectionEquiv P Q hdim hcell).symm p:Q):E4)=(p:E4) :=
  congrArg (fun u : P => (u:E4)) ((projectionEquiv P Q hdim hcell).apply_symm_apply p)

/-- The canonical graph into the orthogonal complement of the actual reference plane. -/
def graphMap (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) : P →ₗ[ℝ] Pᗮ :=
  (Pᗮ.orthogonalProjectionOnto.toLinearMap.comp Q.subtype).comp
    (projectionEquiv P Q hdim hcell).symm.toLinearMap

lemma graphMap_val (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (p : P) :
    (graphMap P Q hdim hcell p:E4)=
      (((projectionEquiv P Q hdim hcell).symm p:Q):E4)-(p:E4) := by
  change Pᗮ.starProjection (((projectionEquiv P Q hdim hcell).symm p:Q):E4)=_
  rw [Submodule.starProjection_orthogonal_val,inverse_projection]

lemma graphMap_decomposition (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (p : P) :
    (p:E4)+(graphMap P Q hdim hcell p:E4)=
      (((projectionEquiv P Q hdim hcell).symm p:Q):E4) := by
  rw [graphMap_val]
  abel

/-- Every selected plane is an actual bounded graph, with norm at most1/4. -/
theorem graphMap_norm (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (p : P) :
    ‖graphMap P Q hdim hcell p‖ ≤ (1/4:ℝ)*‖p‖ := by
  let v : Q := (projectionEquiv P Q hdim hcell).symm p
  have hproj := inverse_projection P Q hdim hcell p
  have hv := inverse_norm P Q hdim hcell p
  have hgap := same_cell_forward_gap P Q hcell v v.property
  change ‖v‖ ≤ _ at hv
  change _ ≤ (1/8:ℝ)*‖v‖ at hgap
  calc
    _ = ‖(v:E4)-(p:E4)‖ := by change ‖(graphMap P Q hdim hcell p:E4)‖=_; rw [graphMap_val]
    _ = Metric.infDist (v:E4) (P:Set E4) := by rw [←hproj,projection_residual_eq_infDist]
    _ ≤ (1/8:ℝ)*‖v‖ := hgap
    _ ≤ _ := by linarith only [hv]

lemma graphMap_characterization (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q) (v : E4) :
    v∈Q ↔ ∃p : P,(p:E4)+(graphMap P Q hdim hcell p:E4)=v := by
  constructor
  · intro hv
    refine ⟨projectionEquiv P Q hdim hcell ⟨v,hv⟩,?_⟩
    rw [graphMap_decomposition,LinearEquiv.symm_apply_apply]
  · rintro ⟨p,rfl⟩
    rw [graphMap_decomposition]
    exact ((projectionEquiv P Q hdim hcell).symm p).property

lemma graphMap_horizontal (P Q : Submodule ℝ E4)
    (hdim : Module.finrank ℝ P=Module.finrank ℝ Q) (hcell : cell P=cell Q)
    (hP : P≤heightKernel) (hQ : Q≤heightKernel) (p : P) :
    (graphMap P Q hdim hcell p:E4)∈heightKernel := by
  rw [graphMap_val]
  exact heightKernel.sub_mem (hQ ((projectionEquiv P Q hdim hcell).symm p).property) (hP p.property)

/-- A previously proved forward plane gap transfers to graph-map variation
in the fixed actual chart. Both inverse maps are constructed above. -/
theorem graphMap_variation (P Q R : Submodule ℝ E4)
    (hdQ : Module.finrank ℝ P=Module.finrank ℝ Q) (hcQ : cell P=cell Q)
    (hdR : Module.finrank ℝ P=Module.finrank ℝ R) (hcR : cell P=cell R)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hgap : ∀v∈Q,Metric.infDist v (R:Set E4) ≤ epsilon*‖v‖) (p : P) :
    ‖graphMap P Q hdQ hcQ p-graphMap P R hdR hcR p‖ ≤ 6*epsilon*‖p‖ := by
  let TQ := projectionEquiv P Q hdQ hcQ
  let TR := projectionEquiv P R hdR hcR
  let v : Q := TQ.symm p
  let y : R := R.orthogonalProjectionOnto (v:E4)
  let t : P := TR y
  have hproj : P.starProjection (v:E4)=(p:E4) := inverse_projection P Q hdQ hcQ p
  have ht : P.starProjection (y:E4)=(t:E4) := rfl
  have hres : ‖(v:E4)-(y:E4)‖ ≤ epsilon*‖v‖ := by
    change ‖(v:E4)-R.starProjection (v:E4)‖ ≤ _
    rw [projection_residual_eq_infDist]
    exact hgap v v.property
  have hpt : ‖p-t‖ ≤ ‖(v:E4)-(y:E4)‖ := by
    change ‖(p:E4)-(t:E4)‖ ≤ _
    have hh := P.norm_starProjection_apply_le ((v:E4)-(y:E4))
    simpa only [map_sub,hproj,ht] using hh
  have hwy : ‖TR.symm p-y‖ ≤ 2*‖p-t‖ := by
    have hh := inverse_norm P R hdR hcR (p-t)
    change ‖TR.symm (p-t)‖ ≤ _ at hh
    rw [map_sub] at hh
    have hyt : TR.symm t=y := TR.symm_apply_apply y
    rwa [hyt] at hh
  have hv : ‖v‖ ≤ 2*‖p‖ := inverse_norm P Q hdQ hcQ p
  have heq : ((graphMap P Q hdQ hcQ p-graphMap P R hdR hcR p:Pᗮ):E4)=
      (v:E4)-((TR.symm p:R):E4) := by
    change (graphMap P Q hdQ hcQ p:E4)-(graphMap P R hdR hcR p:E4)=_
    rw [graphMap_val,graphMap_val]
    change ((v:E4)-(p:E4))-(((TR.symm p:R):E4)-(p:E4))=_
    abel
  calc
    _ = ‖(v:E4)-((TR.symm p:R):E4)‖ := by
      change ‖((graphMap P Q hdQ hcQ p-graphMap P R hdR hcR p:Pᗮ):E4)‖=_
      rw [heq]
    _ ≤ ‖(v:E4)-(y:E4)‖+‖(y:E4)-((TR.symm p:R):E4)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖(v:E4)-(y:E4)‖+‖TR.symm p-y‖ := by rw [norm_sub_rev (y:E4)]; rfl
    _ ≤ 3*(epsilon*‖v‖) := by linarith only [hres,hpt,hwy]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hv he
      nlinarith only [hh]

end NativeProjectorGraphMap
