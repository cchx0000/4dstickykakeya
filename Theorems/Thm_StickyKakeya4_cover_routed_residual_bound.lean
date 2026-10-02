import Theorems.Thm_StickyKakeya4_packet_free_bush_bound
import Theorems.Thm_StickyKakeya4_hausdorff_bush_routing
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The actual Hausdorff-routed residual cover functional

The finite cover and the unchanged-occurrence branches are constructed from
the original compact front. Their physical bush support and separated old
times feed the packet-free tube bound. Exact conservation then bounds the
original mass by a concrete cover functional involving the inherited error.

The small Hausdorff q-cost is recorded separately: no inequality comparing
that cost with the residual cover functional is assumed or asserted here.
In particular this is not a residual-power or final sticky Kakeya theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace StickyKakeya4.CoverRoutedResidualBound

open ActualSlopeSource HausdorffBushRouting PacketFreeBushBound

/-- The Euclidean three-ball coefficient in the original direction density. -/
def directionBallConstant : ENNReal := ENNReal.ofReal (4 * Real.pi / 3)

/-- Genuine ordered endpoint domination transfers every original source
almost-everywhere property, including literal front support. -/
theorem ae_source_of_endpoint_dom
    {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure E3) (Γ : Measure Ω) (endpoint : Ω → E3 × E3)
    (hendpoint : Measurable endpoint) (hdom : Γ.map endpoint ≤ σ.prod σ)
    {P : E3 → Prop} (hP : ∀ᵐ a ∂σ, P a) :
    ∀ᵐ ω ∂Γ, P (endpoint ω).1 := by
  have hp : ∀ᵐ p ∂σ.prod σ, P p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hP
  exact ae_of_ae_map hendpoint.aemeasurable (ae_mono hdom hp)

/-- The cubic ball density is derived from domination by actual Euclidean
volume, rather than supplied as an output geometric certificate. -/
theorem direction_ball_density_of_le_volume
    (σ : Measure E3) (hσ : σ ≤ volume) (x : E3) (T : ℝ) :
    σ (Metric.closedBall x T) ≤ directionBallConstant * ENNReal.ofReal T ^ 3 := by
  apply (hσ _).trans_eq
  rw [EuclideanSpace.volume_closedBall_fin_three, directionBallConstant]
  rw [show Real.pi * 4 / 3 = 4 * Real.pi / 3 by ring]
  exact mul_comm _ _

/-- A scaled product-dominated law on the entire old occurrence space pays
one physical bush. Its actual old time is used before pushing to endpoints,
so no measurable existential-time support set is required. -/
theorem occurrence_le_scaled_packet_free_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure E3) [SFinite σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (μ : Measure Ω) (endpoint : Ω → E3 × E3) (hendpoint : Measurable endpoint)
    (b : E3 → E3) (hb : Measurable b) (oldTime : Ω → ℝ)
    (c : E3) (s₀ R r g : ℝ) (w : ENNReal)
    (hscale : 0 < R + r) (hg : 0 < g)
    (hdom : μ.map endpoint ≤ w • σ.prod σ)
    (hphysical : ∀ᵐ ω ∂μ,
      ‖b (endpoint ω).1 + s₀ • (endpoint ω).1 - c‖ ≤ R ∧
      ‖(b (endpoint ω).1 - b (endpoint ω).2) +
        oldTime ω • ((endpoint ω).1 - (endpoint ω).2)‖ ≤ r ∧
      g ≤ |oldTime ω - s₀|) :
    μ univ ≤ w * (81 * directionBallConstant * ENNReal.ofReal ((R + r) / g) ^ 2) *
      σ univ := by
  let v : E3 → E3 := fun a => b a + s₀ • a - c
  have hv : Measurable v := by dsimp [v]; fun_prop
  let δ : ℝ := (R + r) / g
  have hδ : 0 < δ := div_pos hscale hg
  let tube : Set (E3 × E3) := lineTubeSet id id v δ
  have hmeas : MeasurableSet tube :=
    measurableSet_lineTubeSet id id v measurable_id measurable_id hv δ
  have hsupport : (μ.map endpoint) tubeᶜ = 0 := by
    apply ae_iff.mp
    apply (ae_map_iff hendpoint.aemeasurable hmeas).mpr
    filter_upwards [hphysical] with ω hω
    exact norm_lineResidual_le (endpoint ω).1 (endpoint ω).2 (v (endpoint ω).2) δ
      (SeparatedBushFiber.source_near_target_line (endpoint ω).1 (b (endpoint ω).1)
        (endpoint ω).2 (b (endpoint ω).2) c s₀ (oldTime ω) R r g
        hω.1 hω.2.1 hg hω.2.2)
  have hmass : (μ.map endpoint) univ = (μ.map endpoint) tube := by
    simpa only [hsupport, add_zero] using
      (measure_add_measure_compl (μ := μ.map endpoint) hmeas).symm
  have htube : (σ.prod σ) tube ≤
      (81 * directionBallConstant * ENNReal.ofReal δ ^ 2) * σ univ := by
    apply product_lineTubeSet_le_quadratic σ id id v measurable_id measurable_id hv
      hunit directionBallConstant _ δ hδ
    intro x T _hT
    exact direction_ball_density_of_le_volume σ hσ x T
  calc
    μ univ = (μ.map endpoint) univ := by
      rw [Measure.map_apply hendpoint MeasurableSet.univ, preimage_univ]
    _ = (μ.map endpoint) tube := hmass
    _ ≤ (w • σ.prod σ) tube := hdom tube
    _ = w * (σ.prod σ) tube := by simp
    _ ≤ w * ((81 * directionBallConstant * ENNReal.ofReal δ ^ 2) * σ univ) :=
      mul_le_mul_right htube w
    _ = _ := by dsimp [δ]; ring

/-- Hausdorff dimension constructs the actual finite cover and canonical
unchanged-occurrence routing, and these branches satisfy the explicit global
residual cover functional. The original error remains in every summand.
The independently small q-cost is not used as a bound on this functional. -/
theorem exists_original_front_cover_residual_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (Γ : Measure Ω) (endpoint : Ω → E3 × E3) (hendpoint : Measurable endpoint)
    (hdom : Γ.map endpoint ≤ σ.prod σ)
    (b : E3 → E3) (hb : Measurable b)
    (oldTime : Ω → ℝ) (ht : Measurable oldTime)
    {u v : ℝ} (huv : u < v)
    (ambient : Set MarkedLine) (hcompact : IsCompact ambient)
    (hfront : ∀ᵐ a ∂σ, ∀ s ∈ Icc u v,
      heightPoint (b a + s • a) s ∈ unitFront ambient)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcontact : ∀ᵐ ω ∂Γ,
      ‖(b (endpoint ω).1 - b (endpoint ω).2) +
        oldTime ω • ((endpoint ω).1 - (endpoint ω).2)‖ ≤ r₀)
    {q : NNReal} (hdim : dimH (unitFront ambient) < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ center : Fin n → E4, ∃ radius : Fin n → ℝ,
      unitFront ambient ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
      (∀ i, 0 < radius i ∧ radius i < rho ∧ radius i < (v - u) / 8) ∧
      (∑ i, radius i ^ (q : ℝ)) < epsilon ∧
      Measure.sum (ballBranch Γ (fun ω => (endpoint ω).1)
        (fun ω => b (endpoint ω).1) oldTime u v center radius) = Γ ∧
      (∀ i, ballBranch Γ (fun ω => (endpoint ω).1)
          (fun ω => b (endpoint ω).1) oldTime u v center radius i ≤ Γ ∧
        ballBranch Γ (fun ω => (endpoint ω).1)
          (fun ω => b (endpoint ω).1) oldTime u v center radius i ≤
            ENNReal.ofReal (8 * radius i / (v - u)) • Γ ∧
        ∀ᵐ ω ∂ballBranch Γ (fun ω => (endpoint ω).1)
            (fun ω => b (endpoint ω).1) oldTime u v center radius i,
          ‖b (endpoint ω).1 + center i (Fin.last 3) • (endpoint ω).1 -
            horizontalProjection (center i)‖ < 2 * radius i ∧
          (v - u) / 8 ≤ |center i (Fin.last 3) - oldTime ω|) ∧
      Γ univ ≤ ∑ i, ENNReal.ofReal (8 * radius i / (v - u)) *
        (81 * directionBallConstant *
          ENNReal.ofReal ((2 * radius i + r₀) / ((v - u) / 8)) ^ 2) * σ univ := by
  let a : Ω → E3 := fun ω => (endpoint ω).1
  let bsrc : Ω → E3 := fun ω => b (endpoint ω).1
  have ha : Measurable a := measurable_fst.comp hendpoint
  have hbsrc : Measurable bsrc := hb.comp ha
  have ha1 : ∀ᵐ ω ∂Γ, ‖a ω‖ ≤ 1 :=
    ae_source_of_endpoint_dom σ Γ endpoint hendpoint hdom hunit
  have hfrontΓ : ∀ᵐ ω ∂Γ, ∀ s ∈ Icc u v,
      heightPoint (bsrc ω + s • a ω) s ∈ unitFront ambient :=
    ae_source_of_endpoint_dom σ Γ endpoint hendpoint hdom hfront
  obtain ⟨n, center, radius, hcover, hrad, hcost, hsum, hbranches⟩ :=
    exists_original_front_low_cost_separated_bush_routing Γ ha hbsrc ht ha1 huv
      ambient hcompact hfrontΓ hdim hrho hepsilon
  refine ⟨n, center, radius, hcover, hrad, hcost, hsum, hbranches, ?_⟩
  have hbound (i : Fin n) :
      ballBranch Γ a bsrc oldTime u v center radius i univ ≤
        ENNReal.ofReal (8 * radius i / (v - u)) *
          (81 * directionBallConstant *
            ENNReal.ofReal ((2 * radius i + r₀) / ((v - u) / 8)) ^ 2) * σ univ := by
    let μ := ballBranch Γ a bsrc oldTime u v center radius i
    let w := ENNReal.ofReal (8 * radius i / (v - u))
    have hmap : μ.map endpoint ≤ w • σ.prod σ := by
      calc
        _ ≤ (w • Γ).map endpoint := Measure.map_mono (hbranches i).2.1 hendpoint
        _ = w • Γ.map endpoint := Measure.map_smul w Γ endpoint
        _ ≤ w • σ.prod σ := smul_le_smul_left w hdom
    apply occurrence_le_scaled_packet_free_bound σ hσ hunit μ endpoint hendpoint b hb
      oldTime (horizontalProjection (center i)) (center i (Fin.last 3))
      (2 * radius i) r₀ ((v - u) / 8) w (by linarith [(hrad i).1])
      (by linarith) hmap
    filter_upwards [(hbranches i).2.2, ae_mono (hbranches i).1 hcontact]
      with ω hphys hcollision
    exact ⟨hphys.1.le, hcollision, by simpa only [abs_sub_comm] using hphys.2⟩
  calc
    Γ univ = (Measure.sum (ballBranch Γ a bsrc oldTime u v center radius)) univ := by
      rw [hsum]
    _ = ∑ i, ballBranch Γ a bsrc oldTime u v center radius i univ := by
      rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
    _ ≤ _ := Finset.sum_le_sum (fun i _hi => hbound i)

end StickyKakeya4.CoverRoutedResidualBound
