import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

/-!
An actual affine-slab pullback into a linear graph-direction plane.
The ambient space is ((E × G) × ℝ) with its stated product (maximum) norm.
The source E is a real inner-product space; F is a continuous linear map.
No bounds on the affine offsets ξ,c and no plane-containment certificate are
assumed. The witness and the plane are constructed from the displayed data.
-/
namespace SlabPlanePullback

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The codimension-one functional in graph parameter space. -/
noncomputable def slabFunctional (u : E) (c : ℝ) : (E × ℝ) →ₗ[ℝ] ℝ where
  toFun z := inner ℝ u z.1 - c * z.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, inner_add_right]; ring
  map_smul' a x := by
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The actual injective graph embedding; its last coordinate is height. -/
noncomputable def graphMap (F : E →L[ℝ] G) (ξ : G) : (E × ℝ) →ₗ[ℝ] ((E × G) × ℝ) where
  toFun z := ((z.1, F z.1 + z.2 • ξ), z.2)
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
        abel
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_smul,
          smul_eq_mul, RingHom.id_apply]
    · rfl

@[simp] theorem graphMap_apply (F : E →L[ℝ] G) (ξ : G) (w : E) (t : ℝ) :
    graphMap F ξ (w,t) = ((w, F w + t • ξ),t) := rfl

theorem graphMap_injective (F : E →L[ℝ] G) (ξ : G) :
    Function.Injective (graphMap F ξ) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : (E × G) × ℝ => z.1.1) h)
    (congrArg (fun z : (E × G) × ℝ => z.2) h)

/-- L consists exactly of graph vectors with inner(u,w)=c*t. -/
noncomputable def plane (F : E →L[ℝ] G) (ξ : G) (u : E) (c : ℝ) :
    Submodule ℝ ((E × G) × ℝ) :=
  LinearMap.range ((graphMap F ξ).comp (slabFunctional u c).ker.subtype)

theorem graph_mem_plane_iff (F : E →L[ℝ] G) (ξ : G) (u w : E) (c t : ℝ) :
    graphMap F ξ (w,t) ∈ plane F ξ u c ↔ inner ℝ u w = c * t := by
  constructor
  · rintro ⟨z, hz⟩
    have he : (z : E × ℝ) = (w,t) := graphMap_injective F ξ hz
    have hk := z.property
    rw [LinearMap.mem_ker] at hk
    change inner ℝ u (z : E × ℝ).1 - c * (z : E × ℝ).2 = 0 at hk
    rw [he] at hk
    exact sub_eq_zero.mp hk
  · intro h
    let z : (slabFunctional u c).ker := ⟨(w,t), by
      rw [LinearMap.mem_ker]
      change inner ℝ u w - c * t = 0
      exact sub_eq_zero.mpr h⟩
    exact ⟨z, rfl⟩

theorem mem_plane_iff (F : E →L[ℝ] G) (ξ : G) (u : E) (c : ℝ)
    (z : (E × G) × ℝ) :
    z ∈ plane F ξ u c ↔
      ∃ w : E, ∃ t : ℝ, inner ℝ u w = c * t ∧ z = ((w, F w + t • ξ),t) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v.val.1, v.val.2, ?_, hv.symm⟩
    have hk := v.property
    rw [LinearMap.mem_ker] at hk
    exact sub_eq_zero.mp hk
  · rintro ⟨w,t,h,rfl⟩
    exact (graph_mem_plane_iff F ξ u w c t).mpr h

lemma unit_inner_self (u : E) (hu : ‖u‖ = 1) : inner ℝ u u = 1 := by
  rw [real_inner_self_eq_norm_sq, hu]
  norm_num

theorem slabFunctional_ne_zero (u : E) (c : ℝ) (hu : ‖u‖ = 1) :
    slabFunctional u c ≠ 0 := by
  intro h
  have hv := LinearMap.congr_fun h (u,0)
  have huu := unit_inner_self u hu
  change inner ℝ u u - c * 0 = 0 at hv
  rw [mul_zero, sub_zero, huu] at hv
  norm_num at hv

/-- The constructed physical subspace has dimension dim E = ell-1. -/
theorem plane_finrank [FiniteDimensional ℝ E]
    (F : E →L[ℝ] G) (ξ : G) (u : E) (c : ℝ) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (plane F ξ u c) = Module.finrank ℝ E := by
  unfold plane
  have hinj : Function.Injective ((graphMap F ξ).comp (slabFunctional u c).ker.subtype) := by
    intro x y h
    apply Subtype.ext
    exact graphMap_injective F ξ h
  rw [LinearMap.finrank_range_of_inj hinj]
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero (slabFunctional_ne_zero u c hu)
  rw [Module.finrank_prod, Module.finrank_self] at hk
  omega

noncomputable def corrected (u : E) (c : ℝ) (φ : E) : E :=
  φ - (inner ℝ u φ - c) • u

theorem corrected_constraint (u φ : E) (c : ℝ) (hu : ‖u‖ = 1) :
    inner ℝ u (corrected u c φ) = c := by
  simp only [corrected, inner_sub_right, inner_smul_right, unit_inner_self u hu, mul_one]
  ring

theorem correction_dist_eq (u φ : E) (c : ℝ) (hu : ‖u‖ = 1) :
    dist φ (corrected u c φ) = |inner ℝ u φ - c| := by
  rw [dist_eq_norm]
  simp only [corrected, sub_sub_cancel, norm_smul, hu, mul_one, Real.norm_eq_abs]

/-- The affine offset cancels because the compared vectors have the SAME height. -/
theorem graph_same_height_dist_le (F : E →L[ℝ] G) (ξ : G) (v w : E) (t : ℝ) :
    dist (graphMap F ξ (v,t)) (graphMap F ξ (w,t)) ≤ (1 + ‖F‖) * dist v w := by
  have hF : dist (F v) (F w) ≤ ‖F‖ * dist v w := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact F.le_opNorm (v - w)
  simp only [graphMap_apply, Prod.dist_eq, dist_self, dist_add_right,
    max_eq_left (le_max_of_le_left dist_nonneg)]
  apply max_le
  · have hnorm : 0 ≤ ‖F‖ := norm_nonneg F
    have hd : 0 ≤ dist v w := dist_nonneg
    nlinarith
  · have hd : 0 ≤ dist v w := dist_nonneg
    nlinarith

/-- The explicit corrected graph vector belongs to the constructed subspace. -/
theorem corrected_witness_mem (F : E →L[ℝ] G) (ξ : G) (u φ : E) (c : ℝ)
    (hu : ‖u‖ = 1) : graphMap F ξ (corrected u c φ, 1) ∈ plane F ξ u c := by
  apply (graph_mem_plane_iff F ξ u (corrected u c φ) c 1).mpr
  simpa only [mul_one] using corrected_constraint u φ c hu

/-- Explicit distance estimate for the original physical direction (theta,1).
The norm in E×G and in the physical graph space is the product maximum norm. -/
theorem corrected_witness_distance (F : E →L[ℝ] G) (ξ : G)
    (u φ : E) (c r e : ℝ) (θ : E × G) (hu : ‖u‖ = 1)
    (hslab : |inner ℝ u φ - c| ≤ r)
    (hphysical : ‖θ - (φ, ξ + F φ)‖ ≤ e) :
    dist (θ, (1 : ℝ)) (graphMap F ξ (corrected u c φ,1)) ≤ (1 + ‖F‖) * r + e := by
  have hc : dist φ (corrected u c φ) ≤ r := by
    rw [correction_dist_eq u φ c hu]
    exact hslab
  have hi : dist (θ, (1 : ℝ)) (graphMap F ξ (φ,1)) ≤ e := by
    rw [graphMap_apply, one_smul]
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm]
    simpa only [add_comm (F φ) ξ] using hphysical
  have hg := graph_same_height_dist_le F ξ φ (corrected u c φ) 1
  have hm : (1 + ‖F‖) * dist φ (corrected u c φ) ≤ (1 + ‖F‖) * r :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have htriangle := dist_triangle (θ, (1 : ℝ)) (graphMap F ξ (φ,1))
    (graphMap F ξ (corrected u c φ,1))
  linarith

/-- A complete constructed-subspace/witness endpoint; no plane certificate is an input. -/
theorem slab_pullback [FiniteDimensional ℝ E]
    (F : E →L[ℝ] G) (ξ : G) (u φ : E) (c r e : ℝ) (θ : E × G)
    (hu : ‖u‖ = 1) (hslab : |inner ℝ u φ - c| ≤ r)
    (hphysical : ‖θ - (φ, ξ + F φ)‖ ≤ e) :
    Module.finrank ℝ (plane F ξ u c) = Module.finrank ℝ E ∧
      graphMap F ξ (corrected u c φ,1) ∈ plane F ξ u c ∧
      dist (θ, (1 : ℝ)) (graphMap F ξ (corrected u c φ,1)) ≤ (1 + ‖F‖) * r + e := by
  exact ⟨plane_finrank F ξ u c hu, corrected_witness_mem F ξ u φ c hu,
    corrected_witness_distance F ξ u φ c r e θ hu hslab hphysical⟩

/-- The witness bound also gives the literal metric distance to the plane. -/
theorem infDist_plane_le (F : E →L[ℝ] G) (ξ : G)
    (u φ : E) (c r e : ℝ) (θ : E × G) (hu : ‖u‖ = 1)
    (hslab : |inner ℝ u φ - c| ≤ r)
    (hphysical : ‖θ - (φ, ξ + F φ)‖ ≤ e) :
    Metric.infDist (θ, (1 : ℝ)) (plane F ξ u c : Set ((E × G) × ℝ)) ≤
      (1 + ‖F‖) * r + e := by
  exact (Metric.infDist_le_dist_of_mem (corrected_witness_mem F ξ u φ c hu)).trans
    (corrected_witness_distance F ξ u φ c r e θ hu hslab hphysical)

omit [InnerProductSpace ℝ E] [NormedSpace ℝ G] in
lemma graph_direction_norm_ge_one (θ : E × G) : (1 : ℝ) ≤ ‖(θ, (1 : ℝ))‖ := by
  rw [Prod.norm_def, norm_one]
  exact le_max_right _ _

noncomputable def unitDirection (θ : E × G) : (E × G) × ℝ :=
  ‖(θ, (1 : ℝ))‖⁻¹ • (θ, (1 : ℝ))

theorem unitDirection_norm (θ : E × G) : ‖unitDirection θ‖ = 1 := by
  have hn : 0 < ‖(θ, (1 : ℝ))‖ := lt_of_lt_of_le zero_lt_one (graph_direction_norm_ge_one θ)
  simp only [unitDirection, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

/-- Normalizing the physical direction does not enlarge the error: the graph
height forces norm at least one, and the constructed plane is linear. -/
theorem normalized_slab_pullback (F : E →L[ℝ] G) (ξ : G)
    (u φ : E) (c r e : ℝ) (θ : E × G) (hu : ‖u‖ = 1)
    (hslab : |inner ℝ u φ - c| ≤ r)
    (hphysical : ‖θ - (φ, ξ + F φ)‖ ≤ e) :
    ‖unitDirection θ‖ = 1 ∧
      ‖(θ, (1 : ℝ))‖⁻¹ • graphMap F ξ (corrected u c φ,1) ∈ plane F ξ u c ∧
      dist (unitDirection θ)
        (‖(θ, (1 : ℝ))‖⁻¹ • graphMap F ξ (corrected u c φ,1)) ≤
          (1 + ‖F‖) * r + e := by
  have hn1 := graph_direction_norm_ge_one θ
  have hn : 0 < ‖(θ, (1 : ℝ))‖ := lt_of_lt_of_le zero_lt_one hn1
  have ha0 : 0 ≤ ‖(θ, (1 : ℝ))‖⁻¹ := inv_nonneg.mpr hn.le
  have ha1 : ‖(θ, (1 : ℝ))‖⁻¹ ≤ 1 := (inv_le_one₀ hn).mpr hn1
  refine ⟨unitDirection_norm θ, (plane F ξ u c).smul_mem _
    (corrected_witness_mem F ξ u φ c hu), ?_⟩
  rw [unitDirection, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg ha0]
  calc
    ‖(θ, (1 : ℝ))‖⁻¹ * dist (θ, (1 : ℝ))
        (graphMap F ξ (corrected u c φ,1)) ≤
      1 * dist (θ, (1 : ℝ)) (graphMap F ξ (corrected u c φ,1)) :=
        mul_le_mul_of_nonneg_right ha1 dist_nonneg
    _ = dist (θ, (1 : ℝ)) (graphMap F ξ (corrected u c φ,1)) := one_mul _
    _ ≤ (1 + ‖F‖) * r + e := corrected_witness_distance F ξ u φ c r e θ hu hslab hphysical

/-- The d=4, ell=3 specialization gives a genuine two-dimensional subspace
of the four-dimensional product-coordinate direction space. -/
theorem native_four_dimensional_finrank
    (F : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (ξ : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) (c : ℝ) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (plane F ξ u c) = 2 := by
  rw [plane_finrank F ξ u c hu]
  simp

end SlabPlanePullback
