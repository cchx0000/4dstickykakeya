import Theorems.Thm_StickyKakeya4_rooted_cycle_witness_kernel
import Theorems.Thm_StickyKakeya4_residual_collision_bridge
import Theorems.Thm_StickyKakeya4_contact_cycle_rigidity
import Theorems.Thm_StickyKakeya4_actual_slope_source

/-!
# Rooted witnesses for the actual fixed-angle residual graph

The graph weight is the fixed-angle normalization of the existing physical
`residualContentWeight`, using the actual slope secant and intercept secant.
Positive graph edges therefore have actual closest collision times in `J` and
physical contact error at most the ORIGINAL `r₀`.

Rooted cycle witnesses retain the whole original occurrence, including its
old collision time and flags. The three NEW edge times are measurably appended
using the actual `collisionTime` formula. The inherited edge keeps its given
old time exactly, rather than replacing it by a minimizer. All four contact
errors required by `ContactCycleRigidity` are proved at the same `r₀`.

A determinant cutoff is an explicit measurable restriction. No positive mass
or quantitative lower bound for that cutoff is asserted; it is a separate
geometric obligation. Nothing here gives product-density domination after
conditioning or a paid estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace StickyKakeya4.ActualResidualCycleWitness

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]

/-- The original fixed-angle graph density, normalized by the angle cutoff. -/
def oldGraphWeight (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ) (p : E3 × E3) : ℝ≥0∞ := by
  classical
  exact if sep ≤ ‖p.1 - p.2‖ then
    ENNReal.ofReal sep * residualContentWeight J (p.1 - p.2) (b p.1 - b p.2) r₀ else 0

theorem measurable_oldGraphWeight (b : E3 → E3) (hb : Measurable b)
    (J : Set ℝ) (hJ : MeasurableSet J) (sep r₀ : ℝ) :
    Measurable (oldGraphWeight b J sep r₀) := by
  unfold oldGraphWeight
  apply Measurable.ite
    (measurableSet_le measurable_const (measurable_fst.sub measurable_snd).norm)
  · exact measurable_const.mul (measurable_residualContentWeight
      (fun p : E3 × E3 => p.1 - p.2) (fun p => b p.1 - b p.2)
      (measurable_fst.sub measurable_snd) ((hb.comp measurable_fst).sub (hb.comp measurable_snd))
      J hJ r₀)
  · exact measurable_const

/-- The normalization is proved from actual angular separation. -/
theorem oldGraphWeight_le_one (b : E3 → E3) (J : Set ℝ)
    (sep r₀ : ℝ) (hsep : 0 < sep) (p : E3 × E3) :
    oldGraphWeight b J sep r₀ p ≤ 1 := by
  unfold oldGraphWeight
  split_ifs with hs
  · unfold residualContentWeight
    split_ifs with hc
    · have hn : 0 < ‖p.1 - p.2‖ := hsep.trans_le hs
      calc
        _ ≤ ENNReal.ofReal ‖p.1 - p.2‖ * (ENNReal.ofReal ‖p.1 - p.2‖)⁻¹ :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hs) le_rfl
        _ = 1 := ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hn))
          ENNReal.ofReal_ne_top
    · simp
  · exact zero_le

/-- Positivity supplies real physical residual and closest-time information. -/
theorem oldGraphWeight_pos_support (b : E3 → E3) (J : Set ℝ)
    (sep r₀ : ℝ) (p : E3 × E3) (hp : 0 < oldGraphWeight b J sep r₀ p) :
    sep ≤ ‖p.1 - p.2‖ ∧
      ‖collisionResidual (p.1 - p.2) (b p.1 - b p.2)‖ ≤ r₀ ∧
      collisionTime (p.1 - p.2) (b p.1 - b p.2) ∈ J := by
  unfold oldGraphWeight at hp
  split_ifs at hp with hs
  · unfold residualContentWeight at hp
    split_ifs at hp with hc
    · exact ⟨hs, hc.2⟩
    · simp at hp
  · simp at hp

/-- Self-edges have zero weight in this actual graph. -/
theorem oldGraphWeight_diagonal (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ) (a : E3) :
    oldGraphWeight b J sep r₀ (a, a) = 0 := by
  simp [oldGraphWeight, residualContentWeight]

/-- Exact connection to the existing fixed-angle residual-content integral. -/
theorem oldGraph_mass_eq_fixed_angle_residual_content
    (σ : Measure E3) (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ) :
    (σ.prod σ).withDensity (oldGraphWeight b J sep r₀) univ =
      ENNReal.ofReal sep * weightedResidualContent
        ((σ.prod σ).restrict {p : E3 × E3 | sep ≤ ‖p.1 - p.2‖})
        (fun p => p.1 - p.2) (fun p => b p.1 - b p.2) J r₀ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ p, {p : E3 × E3 | sep ≤ ‖p.1 - p.2‖}.indicator
    (fun p => ENNReal.ofReal sep * residualContentWeight J
      (p.1 - p.2) (b p.1 - b p.2) r₀) p ∂σ.prod σ) = _
  have hA : MeasurableSet {p : E3 × E3 | sep ≤ ‖p.1 - p.2‖} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [lintegral_indicator hA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- The actual closest-time formula on an ordered physical slope edge. -/
def pairTime (b : E3 → E3) (p : E3 × E3) : ℝ :=
  collisionTime (p.1 - p.2) (b p.1 - b p.2)

theorem measurable_pairTime (b : E3 → E3) (hb : Measurable b) : Measurable (pairTime b) :=
  measurable_collisionTime_comp _ _ (measurable_fst.sub measurable_snd)
    ((hb.comp measurable_fst).sub (hb.comp measurable_snd))

/-- At initialization, the graph's canonical closest-time labels satisfy
the physical old-error and time-window bounds directly. This does not replace
the given time of any already marked old occurrence. -/
theorem canonical_old_time_bounds (σ : Measure E3) (b : E3 → E3) (hb : Measurable b)
    (J : Set ℝ) (hJ : MeasurableSet J) (sep r₀ : ℝ) :
    ∀ᵐ p ∂(σ.prod σ).withDensity (oldGraphWeight b J sep r₀),
      ‖(b p.1 - b p.2) + pairTime b p • (p.1 - p.2)‖ ≤ r₀ ∧ pairTime b p ∈ J := by
  rw [ae_withDensity_iff (measurable_oldGraphWeight b hb J hJ sep r₀)]
  apply Filter.Eventually.of_forall
  intro p hp
  exact (oldGraphWeight_pos_support b J sep r₀ p (pos_iff_ne_zero.mpr hp)).2

/-- Simultaneously reversing a secant preserves its actual closest time. -/
theorem pairTime_swap (b : E3 → E3) (p : E3 × E3) : pairTime b p.swap = pairTime b p := by
  unfold pairTime collisionTime
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [show p.2 - p.1 = -(p.1 - p.2) by abel,
    show b p.2 - b p.1 = -(b p.1 - b p.2) by abel]
  simp only [inner_neg_left, inner_neg_right, neg_neg, norm_neg]

/-- The rooted cycle order is x,y,z,w. -/
def cycleVertices (endpoint : Ω → E3 × E3) (p : Ω × (E3 × E3)) : Fin 4 → E3 :=
  ![(endpoint p.1).1, (endpoint p.1).2, p.2.1, p.2.2]

def cycleIntercepts (b : E3 → E3) (endpoint : Ω → E3 × E3)
    (p : Ω × (E3 × E3)) : Fin 4 → E3 := fun i => b (cycleVertices endpoint p i)

/-- Slot zero is the ORIGINAL inherited time. Only the three new edge times
are computed from the physical closest-time formula. -/
def cycleTimes (b : E3 → E3) (endpoint : Ω → E3 × E3) (oldTime : Ω → ℝ)
    (p : Ω × (E3 × E3)) : Fin 4 → ℝ :=
  ![oldTime p.1, pairTime b (p.2.1, (endpoint p.1).2),
    pairTime b p.2, pairTime b ((endpoint p.1).1, p.2.2)]

omit [MeasurableSpace Ω] in
@[simp] theorem cycleTimes_zero (b : E3 → E3) (endpoint : Ω → E3 × E3)
    (oldTime : Ω → ℝ) (p : Ω × (E3 × E3)) :
    cycleTimes b endpoint oldTime p 0 = oldTime p.1 := rfl

theorem measurable_cycleVertices (endpoint : Ω → E3 × E3) (he : Measurable endpoint) :
    Measurable (cycleVertices endpoint) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp only [cycleVertices] <;> fun_prop

theorem measurable_cycleIntercepts (b : E3 → E3) (hb : Measurable b)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint) :
    Measurable (cycleIntercepts b endpoint) := by
  apply measurable_pi_lambda
  intro i
  exact hb.comp ((measurable_pi_apply i).comp (measurable_cycleVertices endpoint he))

theorem measurable_cycleTimes (b : E3 → E3) (hb : Measurable b)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    Measurable (cycleTimes b endpoint oldTime) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact ht.comp measurable_fst
  all_goals
    simp only [cycleTimes]
    exact (measurable_pairTime b hb).comp (by fun_prop)

/-- Contact error is unchanged when an ordered physical edge is reversed. -/
theorem contact_norm_reverse (b : E3 → E3) (x y : E3) (t : ℝ) :
    ‖(b y - b x) + t • (y - x)‖ = ‖(b x - b y) + t • (x - y)‖ := by
  rw [show (b y - b x) + t • (y - x) = -((b x - b y) + t • (x - y)) by module,
    norm_neg]

omit [MeasurableSpace Ω] in
/-- Direct physical adapter: all four contact errors are bounded by the
original r₀, and the inherited old time is not changed to a closest time. -/
theorem cycle_contact_errors (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (oldTime : Ω → ℝ) (p : Ω × (E3 × E3))
    (hroot : ‖(b (endpoint p.1).1 - b (endpoint p.1).2) +
      oldTime p.1 • ((endpoint p.1).1 - (endpoint p.1).2)‖ ≤ r₀)
    (hsuccess : p ∈ RootedCycleWitnessKernel.witnessEvent endpoint (oldGraphWeight b J sep r₀)) :
    ∀ i, ‖ContactCycleRigidity.residual (cycleVertices endpoint p)
      (cycleIntercepts b endpoint p) (cycleTimes b endpoint oldTime p) i‖ ≤ r₀ := by
  obtain ⟨hzy, hzw, hxw⟩ := hsuccess
  have h₁ := (oldGraphWeight_pos_support b J sep r₀ _ hzy).2.1
  have h₂ := (oldGraphWeight_pos_support b J sep r₀ _ hzw).2.1
  have h₃ := (oldGraphWeight_pos_support b J sep r₀ _ hxw).2.1
  have h₀ : ‖(b (endpoint p.1).2 - b (endpoint p.1).1) +
      oldTime p.1 • ((endpoint p.1).2 - (endpoint p.1).1)‖ ≤ r₀ := by
    rw [contact_norm_reverse]
    exact hroot
  have h₂' : ‖(b p.2.2 - b p.2.1) + pairTime b p.2 • (p.2.2 - p.2.1)‖ ≤ r₀ := by
    rw [contact_norm_reverse]
    exact h₂
  intro i
  fin_cases i
  · simpa [ContactCycleRigidity.residual, ContactCycleRigidity.edge, cycleVertices,
      cycleIntercepts, cycleTimes, fourCycleNext] using h₀
  · simpa [ContactCycleRigidity.residual, ContactCycleRigidity.edge, cycleVertices,
      cycleIntercepts, cycleTimes, fourCycleNext, pairTime, collisionResidual] using h₁
  · simpa [ContactCycleRigidity.residual, ContactCycleRigidity.edge, cycleVertices,
      cycleIntercepts, cycleTimes, fourCycleNext] using h₂'
  · simpa [ContactCycleRigidity.residual, ContactCycleRigidity.edge, cycleVertices,
      cycleIntercepts, cycleTimes, fourCycleNext, pairTime, collisionResidual] using h₃

omit [MeasurableSpace Ω] in
/-- All three freshly appended physical times lie in the actual original window. -/
theorem cycle_fresh_times_mem (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (oldTime : Ω → ℝ) (p : Ω × (E3 × E3))
    (hsuccess : p ∈ RootedCycleWitnessKernel.witnessEvent endpoint (oldGraphWeight b J sep r₀)) :
    ∀ j : Fin 3, cycleTimes b endpoint oldTime p j.succ ∈ J := by
  obtain ⟨hzy, hzw, hxw⟩ := hsuccess
  intro j
  fin_cases j
  · exact (oldGraphWeight_pos_support b J sep r₀ _ hzy).2.2
  · exact (oldGraphWeight_pos_support b J sep r₀ _ hzw).2.2
  · exact (oldGraphWeight_pos_support b J sep r₀ _ hxw).2.2

/-- A measurable deterministic label appends the actual four time readout. -/
def timeLabelKernel (b : E3 → E3) (hb : Measurable b)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) : Kernel (Ω × (E3 × E3)) (Fin 4 → ℝ) :=
  Kernel.deterministic (cycleTimes b endpoint oldTime) (measurable_cycleTimes b hb endpoint he oldTime ht)

instance timeLabelKernel_isMarkov (b : E3 → E3) (hb : Measurable b)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    IsMarkovKernel (timeLabelKernel b hb endpoint he oldTime ht) := by
  unfold timeLabelKernel
  infer_instance

/-- Full inherited occurrence, two fresh vertices, and three fresh physical
times together with a copied readout of the untouched old time. -/
def timedWitnessMeasure (σ : Measure E3) [IsProbabilityMeasure σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    Measure ((Ω × (E3 × E3)) × (Fin 4 → ℝ)) :=
  (RootedCycleWitnessKernel.rootedWitnessExtension σ σ Γ endpoint (oldGraphWeight b J sep r₀)).compProd
    (timeLabelKernel b hb endpoint he oldTime ht)

theorem timed_witness_original (σ : Measure E3) [IsProbabilityMeasure σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    (timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht).map (fun p => p.1.1) = Γ := by
  rw [timedWitnessMeasure, MarkovEndpointPreservation.extension_endpoint _ _ Prod.fst measurable_fst]
  exact RootedCycleWitnessKernel.rooted_extension_original σ σ Γ endpoint _

theorem timed_witness_times (σ : Measure E3) [IsProbabilityMeasure σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht,
      p.2 = cycleTimes b endpoint oldTime p.1 := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun measurable_snd ((measurable_cycleTimes b hb endpoint he oldTime ht).comp measurable_fst))
  apply Filter.Eventually.of_forall
  intro p
  simp [timeLabelKernel, Kernel.deterministic_apply]

/-- The inherited old time is copied exactly, with no closest-time substitution. -/
theorem timed_witness_old_time (σ : Measure E3) [IsProbabilityMeasure σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht,
      p.2 0 = oldTime p.1.1 := by
  filter_upwards [timed_witness_times σ Γ b hb J sep r₀ endpoint he oldTime ht] with p hp
  rw [hp, cycleTimes_zero]

/-- The contact-error input to rigidity is obtained from the actual graph
weight, not postulated as a certificate of a new cycle. -/
theorem vertex_witness_contact_errors
    (σ : Measure E3) [IsProbabilityMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (sep r₀ : ℝ) (hsep : 0 < sep)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint) (oldTime : Ω → ℝ)
    (hΓ : Γ.map endpoint ≤ (σ.prod σ).withDensity (oldGraphWeight b J sep r₀))
    (hOld : ∀ᵐ ω ∂Γ, ‖(b (endpoint ω).1 - b (endpoint ω).2) +
      oldTime ω • ((endpoint ω).1 - (endpoint ω).2)‖ ≤ r₀) :
    ∀ᵐ p ∂(RootedCycleWitnessKernel.rootedWitnessExtension σ σ Γ endpoint (oldGraphWeight b J sep r₀)),
      ∀ i, ‖ContactCycleRigidity.residual (cycleVertices endpoint p)
        (cycleIntercepts b endpoint p) (cycleTimes b endpoint oldTime p) i‖ ≤ r₀ := by
  have hsuccess := RootedCycleWitnessKernel.rooted_extension_success σ σ Γ endpoint he
    (oldGraphWeight b J sep r₀) (measurable_oldGraphWeight b hb J hJ sep r₀)
    (oldGraphWeight_le_one b J sep r₀ hsep) hΓ
  have hroot := RootedCycleWitnessKernel.rooted_extension_inherited σ σ Γ endpoint
    (oldGraphWeight b J sep r₀) _ hOld
  filter_upwards [hsuccess, hroot] with p hp hr
  exact cycle_contact_errors b J sep r₀ endpoint oldTime p hr hp

/-- The four contact inequalities hold with the explicitly APPENDED actual
time labels and at the original r₀, for the full unchanged inherited law Γ. -/
theorem timed_witness_contact_errors
    (σ : Measure E3) [IsProbabilityMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (sep r₀ : ℝ) (hsep : 0 < sep)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime)
    (hΓ : Γ.map endpoint ≤ (σ.prod σ).withDensity (oldGraphWeight b J sep r₀))
    (hOld : ∀ᵐ ω ∂Γ, ‖(b (endpoint ω).1 - b (endpoint ω).2) +
      oldTime ω • ((endpoint ω).1 - (endpoint ω).2)‖ ≤ r₀) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht,
      ∀ i, ‖ContactCycleRigidity.residual (cycleVertices endpoint p.1)
        (cycleIntercepts b endpoint p.1) p.2 i‖ ≤ r₀ := by
  have hbase := vertex_witness_contact_errors σ Γ b hb J hJ sep r₀ hsep endpoint he oldTime hΓ hOld
  have hm : ∀ᵐ p ∂(timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht).map Prod.fst,
      ∀ i, ‖ContactCycleRigidity.residual (cycleVertices endpoint p)
        (cycleIntercepts b endpoint p) (cycleTimes b endpoint oldTime p) i‖ ≤ r₀ := by
    rw [timedWitnessMeasure, MarkovEndpointPreservation.extension_fst]
    exact hbase
  have hlift := ae_of_ae_map measurable_fst.aemeasurable hm
  filter_upwards [hlift, timed_witness_times σ Γ b hb J sep r₀ endpoint he oldTime ht] with p hp htime
  rw [htime]
  exact hp

/-- Arbitrary original time, flag, source, and ordered-endpoint observables
retain exactly their old laws after both actual witness extensions. -/
theorem timed_witness_observable
    (σ : Measure E3) [IsProbabilityMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (sep r₀ : ℝ)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime) (f : Ω → T) (hf : Measurable f) :
    (timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht).map (fun p => f p.1.1) =
      Γ.map f := by
  calc
    _ = ((timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht).map
        (fun p => p.1.1)).map f := (Measure.map_map hf (by fun_prop)).symm
    _ = _ := by rw [timed_witness_original]

/-- An actual horizontal-determinant cut. Its positive mass is NOT a conclusion. -/
def determinantCut (endpoint : Ω → E3 × E3) (Δ : ℝ) : Set (Ω × (E3 × E3)) :=
  {p | Δ ≤ |(ContactCycleRigidity.edgeMatrix (cycleVertices endpoint p)).det|}

theorem measurableSet_determinantCut (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (Δ : ℝ) : MeasurableSet (determinantCut endpoint Δ) := by
  apply measurableSet_le measurable_const
  unfold ContactCycleRigidity.edgeMatrix ContactCycleRigidity.edge
  unfold cycleVertices
  fun_prop

omit [MeasurableSpace Ω] in
/-- The actual old time synchronizes all four cycle times on the explicit
nondegenerate cut. This uses one inverse-frame estimate, not two. -/
theorem cycle_times_near_old_time
    (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ) (hr : 0 ≤ r₀)
    (endpoint : Ω → E3 × E3) (oldTime : Ω → ℝ) (p : Ω × (E3 × E3))
    (hroot : ‖(b (endpoint p.1).1 - b (endpoint p.1).2) +
      oldTime p.1 • ((endpoint p.1).1 - (endpoint p.1).2)‖ ≤ r₀)
    (hsuccess : p ∈ RootedCycleWitnessKernel.witnessEvent endpoint (oldGraphWeight b J sep r₀))
    (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hA : ∀ i j, |ContactCycleRigidity.edgeMatrix (cycleVertices endpoint p) i j| ≤ M)
    (hdet : p ∈ determinantCut endpoint Δ) (i : Fin 4) :
    |cycleTimes b endpoint oldTime p i - oldTime p.1| ≤ 48 * M ^ 2 * r₀ / Δ := by
  simpa only [cycleTimes_zero] using ContactCycleRigidity.old_times_pairwise_cluster
    (cycleVertices endpoint p) (cycleIntercepts b endpoint p) (cycleTimes b endpoint oldTime p)
    M Δ r₀ hM hΔ hr hA hdet (cycle_contact_errors b J sep r₀ endpoint oldTime p hroot hsuccess) i 0

omit [MeasurableSpace Ω] in
/-- A cell for the ORIGINAL root time synchronizes the actual physical edges,
with the root error retained in the exact radius. No determinant availability
or mass assertion is hidden in this literal cutoff-dependent conclusion. -/
theorem old_time_cell_contact_bound
    (b : E3 → E3) (J : Set ℝ) (sep r₀ : ℝ) (hr : 0 ≤ r₀)
    (endpoint : Ω → E3 × E3) (oldTime : Ω → ℝ) (p : Ω × (E3 × E3))
    (hroot : ‖(b (endpoint p.1).1 - b (endpoint p.1).2) +
      oldTime p.1 • ((endpoint p.1).1 - (endpoint p.1).2)‖ ≤ r₀)
    (hsuccess : p ∈ RootedCycleWitnessKernel.witnessEvent endpoint (oldGraphWeight b J sep r₀))
    (M Δ c θ L : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hA : ∀ i j, |ContactCycleRigidity.edgeMatrix (cycleVertices endpoint p) i j| ≤ M)
    (hdet : p ∈ determinantCut endpoint Δ) (hcell : |oldTime p.1 - c| ≤ θ)
    (hangle : ∀ i, ‖ContactCycleRigidity.edge (cycleVertices endpoint p) i‖ ≤ L) (i : Fin 4) :
    ‖ContactCycleRigidity.edge (cycleIntercepts b endpoint p) i +
        c • ContactCycleRigidity.edge (cycleVertices endpoint p) i‖ ≤
      r₀ + (θ + 48 * M ^ 2 * r₀ / Δ) * L := by
  have htime := cycle_times_near_old_time b J sep r₀ hr endpoint oldTime p hroot hsuccess
    M Δ hM hΔ hA hdet i
  have hpacket : |cycleTimes b endpoint oldTime p i - c| ≤ θ + 48 * M ^ 2 * r₀ / Δ := by
    calc
      _ ≤ |cycleTimes b endpoint oldTime p i - oldTime p.1| + |oldTime p.1 - c| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  exact SeparatedBushFiber.collision_at_packet_center
    (cycleVertices endpoint p (fourCycleNext i)) (cycleIntercepts b endpoint p (fourCycleNext i))
    (cycleVertices endpoint p i) (cycleIntercepts b endpoint p i)
    (cycleTimes b endpoint oldTime p i) c r₀ (θ + 48 * M ^ 2 * r₀ / Δ) L
    (cycle_contact_errors b J sep r₀ endpoint oldTime p hroot hsuccess i) hpacket (hangle i)

/-- The four vertices correspond to actual original selected marked lines. -/
def cycleMarkedLines (selector : Set MarkedLine) (hselMeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line) (hselector : IsDirectionSelector selector)
    (endpoint : Ω → E3 × E3) (p : Ω × (E3 × E3)) : Fin 4 → MarkedLine :=
  fun i => ActualSlopeSource.slopeLine selector hselMeas hvalid hselector (cycleVertices endpoint p i)

omit [MeasurableSpace Ω] in
theorem cycleMarkedLines_mem (selector : Set MarkedLine) (hselMeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line) (hselector : IsDirectionSelector selector)
    (endpoint : Ω → E3 × E3) (p : Ω × (E3 × E3)) (i : Fin 4) :
    cycleMarkedLines selector hselMeas hvalid hselector endpoint p i ∈ selector :=
  ActualSlopeSource.slopeLine_mem selector hselMeas hvalid hselector _

omit [MeasurableSpace Ω] in
/-- Exact contact-coordinate identification with the repository's selected
marked lines, not a replacement abstract phase-space frame. -/
theorem cycleMarkedLines_secant (selector : Set MarkedLine) (hselMeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line) (hselector : IsDirectionSelector selector)
    (endpoint : Ω → E3 × E3) (p : Ω × (E3 × E3)) (i : Fin 4) :
    fourCycleEdgeSecant (cycleMarkedLines selector hselMeas hvalid hselector endpoint p) i =
      (ContactCycleRigidity.edge (cycleVertices endpoint p) i,
        ContactCycleRigidity.edge (cycleIntercepts
          (ActualSlopeSource.intercept selector hselMeas hvalid hselector) endpoint p) i) := by
  simp [fourCycleEdgeSecant, cycleMarkedLines, ContactCycleRigidity.edge, cycleIntercepts,
    ActualSlopeSource.slope_slopeLine, ActualSlopeSource.intercept]

/-- The concrete selector-intercept specialization produces actual marked
line contact inequalities with the appended physical times. -/
theorem timed_selector_contact_errors
    (selector : Set MarkedLine) (hselMeas : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line) (hselector : IsDirectionSelector selector)
    (σ : Measure E3) [IsProbabilityMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (J : Set ℝ) (hJ : MeasurableSet J) (sep r₀ : ℝ) (hsep : 0 < sep)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime)
    (hΓ : Γ.map endpoint ≤ (σ.prod σ).withDensity
      (oldGraphWeight (ActualSlopeSource.intercept selector hselMeas hvalid hselector) J sep r₀))
    (hOld : ∀ᵐ ω ∂Γ,
      ‖(ActualSlopeSource.intercept selector hselMeas hvalid hselector (endpoint ω).1 -
        ActualSlopeSource.intercept selector hselMeas hvalid hselector (endpoint ω).2) +
        oldTime ω • ((endpoint ω).1 - (endpoint ω).2)‖ ≤ r₀) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ
      (ActualSlopeSource.intercept selector hselMeas hvalid hselector)
      (ActualSlopeSource.measurable_intercept selector hselMeas hvalid hselector)
      J sep r₀ endpoint he oldTime ht,
      ∀ i, ‖(fourCycleEdgeSecant
        (cycleMarkedLines selector hselMeas hvalid hselector endpoint p.1) i).2 +
        p.2 i • (fourCycleEdgeSecant
          (cycleMarkedLines selector hselMeas hvalid hselector endpoint p.1) i).1‖ ≤ r₀ := by
  filter_upwards [timed_witness_contact_errors σ Γ
    (ActualSlopeSource.intercept selector hselMeas hvalid hselector)
    (ActualSlopeSource.measurable_intercept selector hselMeas hvalid hselector)
    J hJ sep r₀ hsep endpoint he oldTime ht hΓ hOld] with p hp
  intro i
  rw [cycleMarkedLines_secant]
  exact hp i

/-- The three newly appended times stay inside the specified physical window. -/
theorem timed_witness_fresh_times_mem
    (σ : Measure E3) [IsProbabilityMeasure σ] (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (sep r₀ : ℝ) (hsep : 0 < sep)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime)
    (hΓ : Γ.map endpoint ≤ (σ.prod σ).withDensity (oldGraphWeight b J sep r₀)) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht,
      ∀ j : Fin 3, p.2 j.succ ∈ J := by
  have hs := RootedCycleWitnessKernel.rooted_extension_success σ σ Γ endpoint he
    (oldGraphWeight b J sep r₀) (measurable_oldGraphWeight b hb J hJ sep r₀)
    (oldGraphWeight_le_one b J sep r₀ hsep) hΓ
  have hm : ∀ᵐ p ∂(timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht).map Prod.fst,
      p ∈ RootedCycleWitnessKernel.witnessEvent endpoint (oldGraphWeight b J sep r₀) := by
    rw [timedWitnessMeasure, MarkovEndpointPreservation.extension_fst]
    exact hs
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hm,
    timed_witness_times σ Γ b hb J sep r₀ endpoint he oldTime ht] with p hp htime
  rw [htime]
  exact cycle_fresh_times_mem b J sep r₀ endpoint oldTime p.1 hp

/-- A diffuse original slope law gives four distinct physical cycle vertices
for this actual loop-free residual graph, before any determinant restriction. -/
theorem timed_witness_four_distinct
    (σ : Measure E3) [IsProbabilityMeasure σ] [NullSingletonClass σ]
    (Γ : Measure Ω) [IsFiniteMeasure Γ]
    (b : E3 → E3) (hb : Measurable b) (J : Set ℝ) (hJ : MeasurableSet J)
    (sep r₀ : ℝ) (hsep : 0 < sep)
    (endpoint : Ω → E3 × E3) (he : Measurable endpoint)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime)
    (hΓ : Γ.map endpoint ≤ (σ.prod σ).withDensity (oldGraphWeight b J sep r₀)) :
    ∀ᵐ p ∂timedWitnessMeasure σ Γ b hb J sep r₀ endpoint he oldTime ht,
      FourDistinctSources.FourDistinct (endpoint p.1.1).1 (endpoint p.1.1).2 p.1.2.1 p.1.2.2 := by
  have hd := RootedCycleWitnessKernel.rooted_extension_four_distinct σ σ Γ endpoint he
    (oldGraphWeight b J sep r₀) (measurable_oldGraphWeight b hb J hJ sep r₀)
    (oldGraphWeight_le_one b J sep r₀ hsep) (oldGraphWeight_diagonal b J sep r₀) hΓ
  apply ae_of_ae_map (p := fun p : Ω × (E3 × E3) =>
    FourDistinctSources.FourDistinct (endpoint p.1).1 (endpoint p.1).2 p.2.1 p.2.2)
    measurable_fst.aemeasurable
  rw [timedWitnessMeasure, MarkovEndpointPreservation.extension_fst]
  exact hd

end StickyKakeya4.ActualResidualCycleWitness
