import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace FinePointSlabGeometry
open scoped BigOperators
open Classical
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every proper subspace of the finite-dimensional parameter space has an
actual norm-one continuous annihilating functional. It is constructed here. -/
theorem exists_unit_annihilator [FiniteDimensional ℝ E]
    (L : Submodule ℝ E) (hL : L ≠ ⊤) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖=1 ∧ ∀ y ∈ L, f y=0 := by
  obtain ⟨f,hf,hker⟩ := L.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hL)
  let g : E →L[ℝ] ℝ := f.toContinuousLinearMap
  have hg : g ≠ 0 := by
    intro heq
    apply hf
    change g.toLinearMap=0
    rw [heq]
    rfl
  have hnorm : 0 < ‖g‖ := norm_pos_iff.mpr hg
  refine ⟨‖g‖⁻¹ • g, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
  · intro y hy
    have hy₀ : f y=0 := hker hy
    change ‖g‖⁻¹ * f y=0
    rw [hy₀,mul_zero]

theorem annihilator_abs_le_infDist (L : Submodule ℝ E) (f : E →L[ℝ] ℝ)
    (hunit : ‖f‖=1) (hzero : ∀ y ∈ L, f y=0) (x : E) :
    |f x| ≤ Metric.infDist x (L : Set E) := by
  apply (Metric.le_infDist ⟨0,L.zero_mem⟩).mpr
  intro y hy
  calc
    |f x| = ‖f (x-y)‖ := by rw [map_sub,hzero y hy,sub_zero,Real.norm_eq_abs]
    _ ≤ ‖f‖*‖x-y‖ := f.le_opNorm _
    _ = dist x y := by rw [hunit,one_mul,dist_eq_norm]

/-- Keep the approximation error explicit. A coarse difference within h of
the proper subspace gives a slab on the ORIGINAL fine second direction,
centered at the ORIGINAL fine first direction at the SAME point. -/
theorem coarse_bad_implies_fine_affine_slab (L : Submodule ℝ E)
    (f : E →L[ℝ] ℝ) (hunit : ‖f‖=1) (hzero : ∀ y ∈ L, f y=0)
    (fine₁ fine₂ coarse₁ coarse₂ : E) {e h R : ℝ}
    (he₁ : dist fine₁ coarse₁ ≤ e) (he₂ : dist fine₂ coarse₂ ≤ e)
    (hbad : Metric.infDist (coarse₂-coarse₁) (L : Set E) < h)
    (hwidth : h+2*e ≤ R) :
    |f fine₂-f fine₁| ≤ R := by
  have hd : dist (fine₂-fine₁) (coarse₂-coarse₁) ≤ 2*e := by
    have ht := dist_sub_sub_le fine₂ fine₁ coarse₂ coarse₁
    have hs := add_le_add he₂ he₁
    linarith
  have hf : |f (fine₂-fine₁)-f (coarse₂-coarse₁)| ≤ 2*e := by
    rw [← map_sub, ← Real.norm_eq_abs]
    have hop := f.le_opNorm ((fine₂-fine₁)-(coarse₂-coarse₁))
    rw [hunit,one_mul] at hop
    exact hop.trans (by simpa only [dist_eq_norm] using hd)
  have hc := annihilator_abs_le_infDist L f hunit hzero (coarse₂-coarse₁)
  calc
    |f fine₂-f fine₁| = |(f (fine₂-fine₁)-f (coarse₂-coarse₁))+f (coarse₂-coarse₁)| := by
      rw [sub_add_cancel,map_sub]
    _ ≤ |f (fine₂-fine₁)-f (coarse₂-coarse₁)|+|f (coarse₂-coarse₁)| := abs_add_le _ _
    _ ≤ R := by linarith

omit [NormedSpace ℝ E] in
/-- The two native errors (fine graph incidence and deterministic coarse
quantization) combine without dropping either parameter. -/
theorem fine_coarse_error_of_actual_direction (fine actual coarse : E)
    {eFine eGrid : ℝ} (hf : dist fine actual ≤ eFine) (hg : dist actual coarse ≤ eGrid) :
    dist fine coarse ≤ eFine+eGrid :=
  (dist_triangle fine actual coarse).trans (add_le_add hf hg)

lemma card_le_real_mul_of_fibers {S T : Type*} [DecidableEq T]
    (P : Finset S) (Q : Finset T) (f : S → T) (B : ℝ)
    (hmaps : ∀ p ∈ P, f p ∈ Q)
    (hfib : ∀ q ∈ Q, ((P.filter (fun p => f p=q)).card : ℝ) ≤ B) :
    (P.card : ℝ) ≤ (Q.card : ℝ)*B := by
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (P.card : ℝ) = ∑ q ∈ Q, ((P.filter (fun p => f p=q)).card : ℝ) := by exact_mod_cast hpart
    _ ≤ ∑ _q ∈ Q, B := Finset.sum_le_sum hfib
    _ = (Q.card : ℝ)*B := by simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Transfer an original fine-label population bound through bounded original
tube-label fibers. This is a pointwise count, before any W restriction. -/
theorem fine_label_population_pullback {T : Type*} [DecidableEq T]
    (tubes : Finset T) (Phi : Finset E) (fine : T → E) (test : E → Prop)
    {mu B : ℝ} (hmu : 0 ≤ mu)
    (hmaps : ∀ t ∈ tubes, fine t ∈ Phi)
    (hfiber : ∀ u ∈ Phi, ((tubes.filter (fun t => fine t=u)).card : ℝ) ≤ mu)
    (hpopulation : ((Phi.filter test).card : ℝ) ≤ B) :
    ((tubes.filter (fun t => test (fine t))).card : ℝ) ≤ mu*B := by
  let S := tubes.filter (fun t => test (fine t))
  let Q := Phi.filter test
  have hmap : ∀ t ∈ S, fine t ∈ Q := by
    intro t ht
    obtain ⟨htT,htest⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨hmaps t htT,htest⟩
  have hfib : ∀ u ∈ Q, ((S.filter (fun t => fine t=u)).card : ℝ) ≤ mu := by
    intro u hu
    have hsub : S.filter (fun t => fine t=u) ⊆ tubes.filter (fun t => fine t=u) := by
      intro t ht
      obtain ⟨htS,heq⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp htS).1,heq⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hfiber u (Finset.mem_filter.mp hu).1)
  have hc := card_le_real_mul_of_fibers S Q fine mu hmap hfib
  have hh := mul_le_mul_of_nonneg_right hpopulation hmu
  change (S.card : ℝ) ≤ mu*B
  nlinarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The full-reference original tube degree follows from its original fine
direction labels and bounded label fibers. -/
theorem tube_degree_of_fine_labels {T : Type*} [DecidableEq T]
    (tubes : Finset T) (Phi : Finset E) (fine : T → E) {mu D : ℝ}
    (hmaps : ∀ t ∈ tubes, fine t ∈ Phi)
    (hfiber : ∀ u ∈ Phi, ((tubes.filter (fun t => fine t=u)).card : ℝ) ≤ mu)
    (hpopulation : mu*(Phi.card : ℝ) ≤ D) : (tubes.card : ℝ) ≤ D := by
  have hc := card_le_real_mul_of_fibers tubes Phi fine mu hmaps hfiber
  nlinarith

/-- Literal fine-point slab Frostman, normalized by the full reference degree.
No selected W family or coarse angular union appears in this theorem. The
fine slab law is used at exactly the stated original admissible width R. -/
theorem tube_slab_of_fine_frostman {T : Type*} [DecidableEq T]
    (tubes : Finset T) (Phi : Finset E) (fine : T → E)
    (f : E →L[ℝ] ℝ) (c : ℝ) {mu D F gamma delta R : ℝ}
    (hmu : 0 ≤ mu) (hF : 0 ≤ F) (hR : 0 < R) (hdelta : delta ≤ R) (hRone : R ≤ 1)
    (hunit : ‖f‖=1)
    (hmaps : ∀ t ∈ tubes, fine t ∈ Phi)
    (hfiber : ∀ u ∈ Phi, ((tubes.filter (fun t => fine t=u)).card : ℝ) ≤ mu)
    (hpopulation : mu*(Phi.card : ℝ) ≤ D)
    (hslab : ∀ g : E →L[ℝ] ℝ, ‖g‖=1 → ∀ b r : ℝ, delta ≤ r → r ≤ 1 →
      ((Phi.filter (fun u => |g u-b| ≤ r)).card : ℝ) ≤ F*r^gamma*(Phi.card : ℝ)) :
    ((tubes.filter (fun t => |f (fine t)-c| ≤ R)).card : ℝ) ≤ F*R^gamma*D := by
  have hc := fine_label_population_pullback tubes Phi fine (fun u => |f u-c| ≤ R)
    hmu hmaps hfiber (hslab f hunit c R hdelta hRone)
  have hp := mul_le_mul_of_nonneg_left hpopulation
    (show 0 ≤ F*R^gamma by positivity)
  nlinarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Count the ORIGINAL fine direction family using its actual realizing tubes.
The comparison direction is derived: |Phi| <= nu * |tubes|. Neither bounded
tube-to-label fibers nor a selected-family population is used to reverse it. -/
theorem fine_population_of_realizing_tubes {T : Type*} [DecidableEq T]
    (tubes : Finset T) (Phi : Finset E) (realizer : E → T) {nu D : ℝ}
    (hnu : 0 ≤ nu) (hdegree : (tubes.card : ℝ) ≤ D)
    (hmaps : ∀ u ∈ Phi, realizer u ∈ tubes)
    (hfiber : ∀ t ∈ tubes, ((Phi.filter (fun u => realizer u=t)).card : ℝ) ≤ nu) :
    (Phi.card : ℝ) ≤ nu*D := by
  have hc := card_le_real_mul_of_fibers Phi tubes realizer nu hmaps hfiber
  have hd := mul_le_mul_of_nonneg_right hdegree hnu
  nlinarith

/-- Safe normalization by the UNCHANGED actual degree cap. The two bounded
original-label multiplicities remain visible in the slab loss mu*nu. -/
theorem tube_slab_with_original_degree {T : Type*} [DecidableEq T]
    (tubes : Finset T) (Phi : Finset E) (fine : T → E) (realizer : E → T)
    (f : E →L[ℝ] ℝ) (c : ℝ) {mu nu D F gamma delta R : ℝ}
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 0 ≤ F) (hR : 0 < R)
    (hdelta : delta ≤ R) (hRone : R ≤ 1) (hunit : ‖f‖=1)
    (hdegree : (tubes.card : ℝ) ≤ D)
    (hmaps : ∀ t ∈ tubes, fine t ∈ Phi)
    (hfiber : ∀ u ∈ Phi, ((tubes.filter (fun t => fine t=u)).card : ℝ) ≤ mu)
    (hrealizer : ∀ u ∈ Phi, realizer u ∈ tubes)
    (hrealizerFiber : ∀ t ∈ tubes, ((Phi.filter (fun u => realizer u=t)).card : ℝ) ≤ nu)
    (hslab : ∀ g : E →L[ℝ] ℝ, ‖g‖=1 → ∀ b r : ℝ, delta ≤ r → r ≤ 1 →
      ((Phi.filter (fun u => |g u-b| ≤ r)).card : ℝ) ≤ F*r^gamma*(Phi.card : ℝ)) :
    ((tubes.filter (fun t => |f (fine t)-c| ≤ R)).card : ℝ) ≤
      (mu*nu*F*R^gamma)*D := by
  have hpopulation := fine_population_of_realizing_tubes tubes Phi realizer
    hnu hdegree hrealizer hrealizerFiber
  have hc := fine_label_population_pullback tubes Phi fine (fun u => |f u-c| ≤ R)
    hmu hmaps hfiber (hslab f hunit c R hdelta hRone)
  have hp := mul_le_mul_of_nonneg_left hpopulation
    (show 0 ≤ mu*F*R^gamma by positivity)
  nlinarith

end
end FinePointSlabGeometry
