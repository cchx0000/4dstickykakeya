import Theorems.Thm_StickyKakeya4_positive_bush_frostman
import Theorems.Thm_StickyKakeya4_actual_residual_cycle_witness
import Theorems.Thm_StickyKakeya4_horizontal_determinant_null

/-!
# Exact collisions are null on a no-Frostman front

A positive exact-collision graph has genuine four-cycles. Lebesgue domination
removes horizontally degenerate fresh pairs; exact contact rigidity then puts
positive source mass in one physical bush. The existing positive-bush theorem
produces Frostman measures on the literal supported front.

Only qualitative nullity is proved. No quantitative determinant cutoff or
power decay of approximate collisions is asserted.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace StickyKakeya4.NoFrostmanExactCollision

/-- For arbitrary source measures, vanishing square integral is equivalent to
vanishing first integral. No probability normalization is needed. -/
theorem lintegral_sq_eq_zero_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ^ 2 ∂μ) = 0 ↔ (∫⁻ x, f x ∂μ) = 0 := by
  rw [lintegral_eq_zero_iff (hf.pow_const 2), lintegral_eq_zero_iff hf]
  constructor <;> intro h <;> filter_upwards [h] with x hx
  · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hx
  · simp [hx]

/-- A graph with zero rooted four-cycle density has zero edge mass, for
arbitrary s-finite source measures. This is the qualitative finite-source C4
principle and does not divide by source mass. -/
theorem edge_mass_eq_zero_of_rootedDensity_eq_zero
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (h : X × Y → ℝ≥0∞) (hh : Measurable h) (hbound : ∀ p, h p ≤ 1)
    (hzero : ∀ p, RootedFourCycle.rootedDensity μ ν h p = 0) :
    (∫⁻ p, h p ∂μ.prod ν) = 0 := by
  have hc : RootedFourCycle.cycleMass μ ν h = 0 := by
    rw [RootedFourCycle.cycleMass_eq_lintegral_rootedDensity μ ν h hh hbound]
    simp_rw [hzero]
    simp
  have hd : (∫⁻ p, RootedFourCycle.codegree ν h p ∂μ.prod μ) = 0 :=
    (lintegral_sq_eq_zero_iff _ _ (RootedFourCycle.measurable_codegree ν h hh)).mp hc
  rw [RootedFourCycle.lintegral_codegree_eq_degree_square μ ν h hh] at hd
  have hz := (lintegral_sq_eq_zero_iff ν _ hh.lintegral_prod_left').mp hd
  simpa only [← lintegral_prod_symm h hh.aemeasurable] using hz

/-- The exact physical graph excludes slope-diagonal pairs. -/
def exactEdges (b : E3 → E3) : Set (E3 × E3) :=
  {p | p.1 ≠ p.2 ∧ collisionResidual (p.1 - p.2) (b p.1 - b p.2) = 0}

theorem measurableSet_exactEdges (b : E3 → E3) (hb : Measurable b) :
    MeasurableSet (exactEdges b) := by
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
  · exact measurableSet_eq_fun
      (measurable_collisionResidual_comp _ _ (measurable_fst.sub measurable_snd)
        ((hb.comp measurable_fst).sub (hb.comp measurable_snd))) measurable_const

/-- Every exact edge has weight one and all other pairs have weight zero. -/
def exactWeight (b : E3 → E3) : E3 × E3 → ℝ≥0∞ :=
  (exactEdges b).indicator (fun _ => 1)

theorem measurable_exactWeight (b : E3 → E3) (hb : Measurable b) :
    Measurable (exactWeight b) := measurable_const.indicator (measurableSet_exactEdges b hb)

theorem exactWeight_le_one (b : E3 → E3) (p : E3 × E3) : exactWeight b p ≤ 1 := by
  classical
  by_cases hp : p ∈ exactEdges b <;> simp [exactWeight, hp]

theorem exactWeight_ne_zero_iff (b : E3 → E3) (p : E3 × E3) :
    exactWeight b p ≠ 0 ↔ p ∈ exactEdges b := by
  classical
  by_cases hp : p ∈ exactEdges b <;> simp [exactWeight, hp]

/-- Zero physical errors and an invertible actual horizontal frame force all
four original collision times to agree exactly. -/
theorem exact_cycle_times_eq (a c : Fin 4 → E3) (t : Fin 4 → ℝ)
    (hdet : (ContactCycleRigidity.edgeMatrix a).det ≠ 0)
    (hres : ∀ i, ContactCycleRigidity.residual a c t i = 0) (i j : Fin 4) :
    t i = t j := by
  have hsys := ContactCycleRigidity.time_difference_system a c t
  simp_rw [hres] at hsys
  have hv : (fun k : Fin 3 => t k.castSucc - t 3) = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    simpa using hsys
  have ht (k : Fin 4) : t k = t 3 := by
    fin_cases k
    · exact sub_eq_zero.mp (congrFun hv 0)
    · exact sub_eq_zero.mp (congrFun hv 1)
    · exact sub_eq_zero.mp (congrFun hv 2)
    · rfl
  exact (ht i).trans (ht j).symm

/-- The four-cycle's third vertex passes through the root edge's fixed
physical collision point. -/
theorem exact_cycle_third_mem_root_bush
    (b : E3 → E3) (x y z w : E3)
    (hxy : (x, y) ∈ exactEdges b) (hzy : (z, y) ∈ exactEdges b)
    (hzw : (z, w) ∈ exactEdges b) (hxw : (x, w) ∈ exactEdges b)
    (hdet : (ContactCycleRigidity.anchoredMatrix ![x, y, z, w]).det ≠ 0) :
    b z + ActualResidualCycleWitness.pairTime b (x, y) • z =
      b x + ActualResidualCycleWitness.pairTime b (x, y) • x := by
  let a : Fin 4 → E3 := ![x, y, z, w]
  let c : Fin 4 → E3 := fun i => b (a i)
  let t : Fin 4 → ℝ := ![ActualResidualCycleWitness.pairTime b (x, y),
    ActualResidualCycleWitness.pairTime b (z, y),
    ActualResidualCycleWitness.pairTime b (z, w),
    ActualResidualCycleWitness.pairTime b (x, w)]
  have hxy' := hxy.2
  have hzy' := hzy.2
  have hzw' := hzw.2
  have hxw' := hxw.2
  change (b x - b y) + t 0 • (x - y) = 0 at hxy'
  change (b z - b y) + t 1 • (z - y) = 0 at hzy'
  change (b z - b w) + t 2 • (z - w) = 0 at hzw'
  change (b x - b w) + t 3 • (x - w) = 0 at hxw'
  have hres : ∀ i, ContactCycleRigidity.residual a c t i = 0 := by
    intro i
    fin_cases i
    · change (b y - b x) + t 0 • (y - x) = 0
      rw [show (b y - b x) + t 0 • (y - x) = -((b x - b y) + t 0 • (x - y)) by module, hxy', neg_zero]
    · exact hzy'
    · change (b w - b z) + t 2 • (w - z) = 0
      rw [show (b w - b z) + t 2 • (w - z) = -((b z - b w) + t 2 • (z - w)) by module, hzw', neg_zero]
    · exact hxw'
  have hdet' : (ContactCycleRigidity.edgeMatrix a).det ≠ 0 := by
    rw [ContactCycleRigidity.edgeMatrix_det_eq_anchored]
    exact hdet
  have ht : t 1 = t 0 := exact_cycle_times_eq a c t hdet' hres 1 0
  rw [ht] at hzy'
  change b z + t 0 • z = b x + t 0 • x
  have hx : b x + t 0 • x = b y + t 0 • y := by
    apply sub_eq_zero.mp
    calc
      _ = (b x - b y) + t 0 • (x - y) := by module
      _ = 0 := hxy'
  have hz : b z + t 0 • z = b y + t 0 • y := by
    apply sub_eq_zero.mp
    calc
      _ = (b z - b y) + t 0 • (z - y) := by module
      _ = 0 := hzy'
  exact hz.trans hx.symm

/-- Null exact bushes annihilate every non-diagonal rooted C4 completion
once horizontally degenerate fresh pairs have been removed. -/
theorem rootSuccess_eq_zero_of_bush_null
    (σ : Measure E3) [SFinite σ] (b : E3 → E3) (hb : Measurable b)
    (p : E3 × E3) (hp : p ∈ exactEdges b)
    (hdet : ∀ᵐ q ∂σ.prod σ,
      (ContactCycleRigidity.anchoredMatrix ![p.1, p.2, q.1, q.2]).det ≠ 0)
    (hbush : σ {a | b a + ActualResidualCycleWitness.pairTime b p • a =
      b p.1 + ActualResidualCycleWitness.pairTime b p • p.1} = 0) :
    RootedFourCycle.rootSuccess σ σ (exactWeight b) p = 0 := by
  let G : Set E3 := {a | b a + ActualResidualCycleWitness.pairTime b p • a =
    b p.1 + ActualResidualCycleWitness.pairTime b p • p.1}
  have hz : ∀ᵐ z ∂σ, z ∉ G := by
    rw [ae_iff]
    simpa only [not_not, G, mem_ofPred_eq] using hbush
  have hzpair : ∀ᵐ q ∂σ.prod σ, q.1 ∉ G :=
    Measure.quasiMeasurePreserving_fst.ae hz
  unfold RootedFourCycle.rootSuccess
  have hw := measurable_exactWeight b hb
  apply (lintegral_eq_zero_iff (by fun_prop)).2
  filter_upwards [hdet, hzpair] with q hqdet hq
  by_contra hn
  have hzy : exactWeight b (q.1, p.2) ≠ 0 := by
    intro h
    simp [h] at hn
  have hzw : exactWeight b q ≠ 0 := by
    intro h
    simp [h] at hn
  have hxw : exactWeight b (p.1, q.2) ≠ 0 := by
    intro h
    simp [h] at hn
  exact hq (exact_cycle_third_mem_root_bush b p.1 p.2 q.1 q.2 hp
    ((exactWeight_ne_zero_iff b _).mp hzy) ((exactWeight_ne_zero_iff b _).mp hzw)
    ((exactWeight_ne_zero_iff b _).mp hxw) hqdet)

/-- A source with no positive exact bush has no positive exact-collision
graph, provided horizontal degeneracy is null at every distinct root. -/
theorem exactEdges_null_of_bush_null
    (σ : Measure E3) [SFinite σ] (b : E3 → E3) (hb : Measurable b)
    (hdet : ∀ x y : E3, x ≠ y → ∀ᵐ q ∂σ.prod σ,
      (ContactCycleRigidity.anchoredMatrix ![x, y, q.1, q.2]).det ≠ 0)
    (hbush : ∀ s : ℝ, ∀ c : E3, σ {a | b a + s • a = c} = 0) :
    (σ.prod σ) (exactEdges b) = 0 := by
  have hz : ∀ p, RootedFourCycle.rootedDensity σ σ (exactWeight b) p = 0 := by
    intro p
    by_cases hp : p ∈ exactEdges b
    · have hr := rootSuccess_eq_zero_of_bush_null σ b hb p hp
        (hdet p.1 p.2 hp.1) (hbush _ _)
      simp [RootedFourCycle.rootedDensity, hr]
    · have hw : exactWeight b p = 0 := by simp [exactWeight, hp]
      simp [RootedFourCycle.rootedDensity, hw]
  have he := edge_mass_eq_zero_of_rootedDensity_eq_zero σ σ (exactWeight b)
    (measurable_exactWeight b hb) (exactWeight_le_one b) hz
  simpa only [exactWeight, lintegral_indicator (measurableSet_exactEdges b hb),
    lintegral_const, one_mul, Measure.restrict_apply_univ] using he

/-- Continuity from above turns exact collision nullity into qualitative
vanishing of every fixed-angle residual sublevel graph. -/
theorem tendsto_fixed_angle_residual_mass_zero
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (hexact : (σ.prod σ) (exactEdges b) = 0) (sep : ℝ) (hsep : 0 < sep) :
    Tendsto (fun r : ℝ => (σ.prod σ) {p : E3 × E3 |
      sep ≤ ‖p.1 - p.2‖ ∧ ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r})
      (𝓝[>] 0) (𝓝 0) := by
  let E : ℝ → Set (E3 × E3) := fun r => {p |
    sep ≤ ‖p.1 - p.2‖ ∧ ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r}
  have hE (r : ℝ) : MeasurableSet (E r) := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const (measurable_fst.sub measurable_snd).norm
    · exact measurableSet_le (measurable_collisionResidual_comp _ _
        (measurable_fst.sub measurable_snd)
        ((hb.comp measurable_fst).sub (hb.comp measurable_snd))).norm measurable_const
  have hinter : (⋂ r > (0 : ℝ), E r) ⊆ exactEdges b := by
    intro p hp
    have he := mem_iInter.mp (mem_iInter.mp hp 1) (by norm_num : (0 : ℝ) < 1)
    refine ⟨?_, ?_⟩
    · intro h
      have hz : ‖p.1 - p.2‖ = 0 := by simp [h]
      exact (not_le_of_gt hsep) (hz ▸ he.1)
    · apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      apply le_of_forall_gt_imp_ge_of_dense
      intro r hr
      exact (mem_iInter.mp (mem_iInter.mp hp r) hr).2
  have hi : (σ.prod σ) (⋂ r > (0 : ℝ), E r) = 0 :=
    measure_mono_null hinter hexact
  have hlim := tendsto_measure_biInter_gt (μ := σ.prod σ) (a := (0 : ℝ))
    (s := E) (fun r _ => (hE r).nullMeasurableSet)
    (fun i j _ hij p hp => ⟨hp.1, hp.2.trans hij⟩)
    ⟨1, by norm_num, measure_ne_top _ _⟩
  simpa only [hi, Function.comp_def, E] using hlim

/-- Failure of the supported Frostman conclusion forces every exact
physical bush to have zero actual slope-source mass. -/
theorem exact_bush_null_of_no_front_frostman
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (s : ℝ) (c : E3) :
    σ {a | b a + s • a = c} = 0 := by
  by_contra hne
  exact hno (PositiveBush.front_frostman_of_positive_exact_bush_piece ambient hcompact
    σ hσ b hb hslopes u v s huv c hsupport (pos_iff_ne_zero.mpr hne))

/-- A no-Frostman front has zero product-source mass of off-diagonal exact
collisions. Lebesgue domination supplies horizontal nondegeneracy, and the
rooted C4 argument supplies the positive exact bush needed for contradiction. -/
theorem no_front_frostman_exact_collision_null
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) :
    (σ.prod σ) {p : E3 × E3 | p.1 ≠ p.2 ∧
      collisionResidual (p.1 - p.2) (b p.1 - b p.2) = 0} = 0 := by
  apply exactEdges_null_of_bush_null σ b hb
  · exact fun x y hxy => ae_contact_anchoredMatrix_det_ne_zero_of_le_volume σ hσ x y hxy
  · exact exact_bush_null_of_no_front_frostman ambient hcompact σ hσ b hb hslopes
      u v huv hsupport hno

/-- The actual fixed-angle residual graph tends to zero in mass on every
no-Frostman front as the collision radius tends to zero. This conclusion is
qualitative, with no uniform rate across sources. -/
theorem no_front_frostman_tendsto_fixed_angle_residual_mass_zero
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (sep : ℝ) (hsep : 0 < sep) :
    Tendsto (fun r : ℝ => (σ.prod σ) {p : E3 × E3 |
      sep ≤ ‖p.1 - p.2‖ ∧ ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r})
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_fixed_angle_residual_mass_zero σ b hb
    (no_front_frostman_exact_collision_null ambient hcompact σ hσ b hb hslopes
      u v huv hsupport hno) sep hsep

/-- The actual normalized residual graph is bounded by the fixed-angle
sublevel graph, with no assumption on the collision-time window. -/
theorem oldGraph_mass_le_fixed_angle_residual_mass
    (σ : Measure E3) (b : E3 → E3) (hb : Measurable b)
    (J : Set ℝ) (sep r : ℝ) (hsep : 0 < sep) :
    (σ.prod σ).withDensity (ActualResidualCycleWitness.oldGraphWeight b J sep r) univ ≤
      (σ.prod σ) {p : E3 × E3 | sep ≤ ‖p.1 - p.2‖ ∧
        ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r} := by
  classical
  let E : Set (E3 × E3) := {p | sep ≤ ‖p.1 - p.2‖ ∧
    ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r}
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const (measurable_fst.sub measurable_snd).norm
    · exact measurableSet_le (measurable_collisionResidual_comp _ _
        (measurable_fst.sub measurable_snd)
        ((hb.comp measurable_fst).sub (hb.comp measurable_snd))).norm measurable_const
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ p, E.indicator (fun _ => (1 : ℝ≥0∞)) p ∂σ.prod σ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ E
      · simpa only [indicator_of_mem hp] using
          ActualResidualCycleWitness.oldGraphWeight_le_one b J sep r hsep p
      · have hz : ActualResidualCycleWitness.oldGraphWeight b J sep r p = 0 := by
          by_contra hne
          have h := ActualResidualCycleWitness.oldGraphWeight_pos_support b J sep r p
            (pos_iff_ne_zero.mpr hne)
          exact hp ⟨h.1, h.2.1⟩
        simp [hz, hp]
    _ = _ := by rw [lintegral_indicator hE, lintegral_const, one_mul,
        Measure.restrict_apply_univ]

/-- The existing original fixed-angle residual weight has vanishing mass at
fine radius whenever the exact physical graph is null. -/
theorem tendsto_oldGraph_mass_zero
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (hexact : (σ.prod σ) (exactEdges b) = 0)
    (J : Set ℝ) (sep : ℝ) (hsep : 0 < sep) :
    Tendsto (fun r : ℝ => (σ.prod σ).withDensity
      (ActualResidualCycleWitness.oldGraphWeight b J sep r) univ)
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_fixed_angle_residual_mass_zero σ b hb hexact sep hsep)
    (fun _ => bot_le) (fun r => oldGraph_mass_le_fixed_angle_residual_mass σ b hb J sep r hsep)

/-- The normalized old residual graph itself has qualitative mass decay on
the no-Frostman branch, with the original source and any fixed time window. -/
theorem no_front_frostman_tendsto_oldGraph_mass_zero
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (b : E3 → E3) (hb : Measurable b) (hslopes : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (u v : ℝ) (huv : u < v)
    (hsupport : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      ActualSlopeSource.heightPoint (b a + s • a) s ∈ unitFront ambient)
    (hno : ¬ HasFrontFrostmanMeasures ambient) (J : Set ℝ) (sep : ℝ) (hsep : 0 < sep) :
    Tendsto (fun r : ℝ => (σ.prod σ).withDensity
      (ActualResidualCycleWitness.oldGraphWeight b J sep r) univ)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_oldGraph_mass_zero σ b hb
    (no_front_frostman_exact_collision_null ambient hcompact σ hσ b hb hslopes
      u v huv hsupport hno) J sep hsep

/-- A uniformly product-dominated lift supported on progressively finer
fixed-angle residual edges must lose all its mass when exact collisions are
null. In particular it cannot retain a fixed positive old mass. -/
theorem tendsto_dominated_fine_residual_lift_mass_zero
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3) (hb : Measurable b)
    (hexact : (σ.prod σ) (exactEdges b) = 0) (sep : ℝ) (hsep : 0 < sep)
    (η : ℝ → Measure (E3 × E3)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hdom : ∀ r, η r ≤ C • (σ.prod σ))
    (hsupport : ∀ r, ∀ᵐ p ∂η r, sep ≤ ‖p.1 - p.2‖ ∧
      ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r) :
    Tendsto (fun r => η r univ) (𝓝[>] 0) (𝓝 0) := by
  have hmass (r : ℝ) : η r univ ≤ C * (σ.prod σ) {p : E3 × E3 |
      sep ≤ ‖p.1 - p.2‖ ∧ ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r} := by
    calc
      _ ≤ η r {p : E3 × E3 | sep ≤ ‖p.1 - p.2‖ ∧
          ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r} :=
        measure_mono_ae ((hsupport r).mono (fun _ hp _ => hp))
      _ ≤ _ := by simpa only [Measure.smul_apply, smul_eq_mul] using (hdom r) _
  have hlim := ENNReal.Tendsto.const_mul
    (tendsto_fixed_angle_residual_mass_zero σ b hb hexact sep hsep) (Or.inr hC)
  simp only [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hmass

end StickyKakeya4.NoFrostmanExactCollision
