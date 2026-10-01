import Theorems.Thm_StickyKakeya4_quantitative_north_return_firewall

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace StickyKakeya4

/-- Every positive finite mass admits a positive real scale at which an
arbitrary finite fourth-power cost is affordable.  The elementary fourth
power is the exact `3 + 1` cost of a direction cap together with the affine
fibre interval. -/
theorem exists_scale_fourth_power_le
    (mass cost : ENNReal) (hmass : 0 < mass) (hmassTop : mass ≠ ⊤)
    (hcostTop : cost ≠ ⊤) (radius : ℝ) (hradius : 0 < radius) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ radius ∧ rho ≤ 1 ∧
      cost * (ENNReal.ofReal rho) ^ 4 ≤ mass := by
  let rho : ℝ :=
    min radius (min 1 (mass.toReal / (cost.toReal + 1)))
  have hmassReal : 0 < mass.toReal :=
    ENNReal.toReal_pos hmass.ne' hmassTop
  have hcostReal : 0 ≤ cost.toReal := ENNReal.toReal_nonneg
  have hratio : 0 < mass.toReal / (cost.toReal + 1) := by positivity
  have hrho : 0 < rho := by
    simp only [rho, lt_min_iff]
    exact ⟨hradius, by simpa only [lt_min_iff] using
      (show 0 < (1 : ℝ) ∧ 0 < mass.toReal / (cost.toReal + 1) from
        ⟨by norm_num, hratio⟩)⟩
  have hrhoRadius : rho ≤ radius := min_le_left _ _
  have hrhoOne : rho ≤ 1 :=
    (min_le_right radius _).trans (min_le_left _ _)
  have hrhoRatio : rho ≤ mass.toReal / (cost.toReal + 1) :=
    (min_le_right radius _).trans (min_le_right _ _)
  have hscaled : rho * (cost.toReal + 1) ≤ mass.toReal :=
    (le_div_iff₀ (by positivity : 0 < cost.toReal + 1)).mp hrhoRatio
  have hrhoFourth : rho ^ 4 ≤ rho := by
    nlinarith [sq_nonneg rho, sq_nonneg (rho ^ 2 - rho)]
  have hreal : cost.toReal * rho ^ 4 ≤ mass.toReal := by
    calc
      cost.toReal * rho ^ 4 ≤ cost.toReal * rho := by
        exact mul_le_mul_of_nonneg_left hrhoFourth hcostReal
      _ ≤ rho * (cost.toReal + 1) := by nlinarith
      _ ≤ mass.toReal := hscaled
  have hleftTop : cost * (ENNReal.ofReal rho) ^ 4 ≠ ⊤ :=
    ENNReal.mul_ne_top hcostTop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine ⟨rho, hrho, hrhoRadius, hrhoOne, ?_⟩
  apply (ENNReal.toReal_le_toReal hleftTop hmassTop).1
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hrho.le]
  exact hreal

/-- A fourth-power budget at the comparison scale dominates the relative
`(4 - epsilon)` failed-Frostman lower ledger at every smaller positive scale.
This is the exponent cancellation that makes the collision estimate uniform
in the retained source mass. -/
theorem fourth_power_le_relative_frostman_budget
    (mass cost : ENNReal) (epsilon r rho : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (hr : 0 < r) (hrho : 0 < rho) (hrSmall : r ≤ rho)
    (hbudget : cost * (ENNReal.ofReal rho) ^ 4 ≤ mass) :
    cost * (ENNReal.ofReal r) ^ 4 ≤
      mass *
        (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
          (ENNReal.ofReal r).rpow (4 - epsilon)) := by
  let q : ENNReal := ENNReal.ofReal (r / rho)
  have hqOne : q ≤ 1 := by
    have hratio : r / rho ≤ 1 := (div_le_one hrho).2 hrSmall
    simpa [q] using ENNReal.ofReal_le_ofReal hratio
  have hqPow : q ^ 4 ≤ q.rpow (4 - epsilon) := by
    have h := ENNReal.rpow_le_rpow_of_exponent_ge (x := q) hqOne
      (show 4 - epsilon ≤ (4 : ℝ) by linarith)
    calc
      q ^ 4 = q.rpow (4 : ℝ) := (ENNReal.rpow_natCast q 4).symm
      _ ≤ q.rpow (4 - epsilon) := h
  have hrFactor :
      ENNReal.ofReal r = ENNReal.ofReal rho * q := by
    dsimp [q]
    rw [← ENNReal.ofReal_mul hrho.le]
    congr 1
    field_simp [hrho.ne']
  have hrelative :
      ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
          (ENNReal.ofReal r).rpow (4 - epsilon) =
        q.rpow (4 - epsilon) := by
    rw [hrFactor]
    rw [show
      (ENNReal.ofReal rho * q).rpow (4 - epsilon) =
        (ENNReal.ofReal rho).rpow (4 - epsilon) *
          q.rpow (4 - epsilon) from
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
    have hbase :
        (ENNReal.ofReal rho).rpow (4 - epsilon) ≠ 0 := by
      intro hzero
      have hrhoZero : ENNReal.ofReal rho = 0 :=
        (ENNReal.rpow_eq_zero_iff_of_pos (by linarith)).mp hzero
      exact (ENNReal.ofReal_pos.mpr hrho).ne' hrhoZero
    have hbaseTop :
        (ENNReal.ofReal rho).rpow (4 - epsilon) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    calc
      ((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
          ((ENNReal.ofReal rho).rpow (4 - epsilon) *
            q.rpow (4 - epsilon)) =
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal rho).rpow (4 - epsilon)) *
              q.rpow (4 - epsilon) := by ring
      _ = q.rpow (4 - epsilon) := by
        rw [ENNReal.inv_mul_cancel hbase hbaseTop, one_mul]
  calc
    cost * (ENNReal.ofReal r) ^ 4 =
        (cost * (ENNReal.ofReal rho) ^ 4) * q ^ 4 := by
      rw [hrFactor, mul_pow]
      ring
    _ ≤ mass * q ^ 4 := by gcongr
    _ ≤ mass * q.rpow (4 - epsilon) := by gcongr
    _ = mass *
        (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
          (ENNReal.ofReal r).rpow (4 - epsilon)) := by rw [hrelative]

/-- State-level collision terminal at an explicit comparison scale.  It is
the chain-free form needed after the budget scale has been chosen first and
the retained child has then been obtained from the uniform failure oracle. -/
theorem no_separated_return_of_relative_mass
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    (parent child : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector)
    (hchildNorth : child.source ⊆ contactNorthParameterCap)
    (epsilon rho t g E eta : ℝ) (outerCenter : E3)
    (hmassLower :
      (frontParameterProbability : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (frontParameterProbability : Measure FrontParameterSpace) child.source)
    (hreturn : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        outerCenter‖ ≤ E)
    (hE : 0 ≤ E) (hg : 0 < g)
    (hsep : g ≤ |t - child.center (3 : Fin 4)|)
    (heta : 0 < eta)
    (hradiusOne :
      2 * ((6 * child.radius + 2 * E) / g) + eta ≤ 1)
    (hbudget :
      ENNReal.ofReal (2 * child.radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + eta)) ^ 3) ≤
        (frontParameterProbability : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon))) :
    False := by
  let referenceParameter := child.witness
  let reference : MarkedLine :=
    selectorLine selector hmeasurable hvalid hselector referenceParameter.1
  have hrefParameter : referenceParameter ∈ child.source :=
    child.witness_mem_source
  have href : reference ∈ selector :=
    (selectorLine selector hmeasurable hvalid hselector
      referenceParameter.1).property
  have hsourcePos : ∀ z ∈ child.source,
      0 < direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
    intro z hz
    have hhalf : (1 / 2 : ℝ) ≤ direction
        (selectorLine selector hmeasurable hvalid hselector z.1)
          (3 : Fin 4) := by
      rw [direction_selectorLine selector hmeasurable hvalid hselector z.1]
      exact contactNorthParameterCap_direction_ge_half z (hchildNorth hz)
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hrefPos : 0 < direction reference (3 : Fin 4) :=
    hsourcePos referenceParameter hrefParameter
  have hfirst : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1)
            (child.center (3 : Fin 4)) -
        northGraphEvaluation reference (child.center (3 : Fin 4))‖ ≤
          6 * child.radius := by
    intro z hz
    exact le_of_lt
      (child.source_pair_common_probe_of_north hchildNorth
        z referenceParameter hz hrefParameter)
  have hsecond : ∀ z ∈ child.source,
      ‖northGraphEvaluation
          (selectorLine selector hmeasurable hvalid hselector z.1) t -
        northGraphEvaluation reference t‖ ≤ 2 * E := by
    intro z hz
    let u := northGraphEvaluation
      (selectorLine selector hmeasurable hvalid hselector z.1) t
    let v := northGraphEvaluation reference t
    have hu : ‖u - outerCenter‖ ≤ E := by simpa [u] using hreturn z hz
    have hv : ‖v - outerCenter‖ ≤ E := by
      simpa [v, reference, referenceParameter] using
        hreturn referenceParameter hrefParameter
    calc
      ‖u - v‖ = ‖(u - outerCenter) + (outerCenter - v)‖ := by
        congr 1 <;> abel
      _ ≤ ‖u - outerCenter‖ + ‖outerCenter - v‖ := norm_add_le _ _
      _ = ‖u - outerCenter‖ + ‖v - outerCenter‖ := by
        rw [norm_sub_rev outerCenter v]
      _ ≤ E + E := add_le_add hu hv
      _ = 2 * E := by ring
  have hmeasureUpper :
      (frontParameterProbability : Measure FrontParameterSpace) child.source ≤
        ENNReal.ofReal (2 * child.radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + eta)) ^ 3) := by
    apply frontParameterProbability_source_le_of_two_probe_and_ball
      selector hmeasurable hvalid hselector child.source reference href
      hsourcePos hrefPos (child.center (3 : Fin 4)) t
      (6 * child.radius) (2 * E) g eta hfirst hsecond
      child.center child.radius child.source_subset_ball
    · exact mul_nonneg (by norm_num) child.radius_pos.le
    · exact mul_nonneg (by norm_num) hE
    · exact hg
    · simpa [abs_sub_comm] using hsep
    · exact heta
    · exact hradiusOne
    · exact child.radius_pos.le
  have hmeasureLeLower := hmeasureUpper.trans hbudget
  exact (not_lt_of_ge hmeasureLeLower) hmassLower

/-- The failed-Frostman oracle can choose a retained north child at a scale
whose entire `3 + 1` two-probe cost is already paid by the parent mass.  Hence
no common second probe with fixed positive height gap and error linear in the
child radius can occur.  The numerical budget is produced internally rather
than supplied as a hypothesis. -/
theorem ConditionedBoundaryPacketState.exists_budget_adapted_north_child
    {selector : Set MarkedLine}
    {hmeasurable : MeasurableSet selector}
    {hvalid : ∀ line ∈ selector, IsValidLine line}
    {hselector : IsDirectionSelector selector}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonFour : epsilon < 4)
    (horacle : ∀ (source : Set FrontParameterSpace),
      MeasurableSet source →
      0 < (frontParameterProbability : Measure FrontParameterSpace) source →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (x : E4) (r : ℝ),
          0 < r ∧ r < rho ∧
          (frontParameterProbability : Measure FrontParameterSpace) source *
              (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
                (ENNReal.ofReal r).rpow (4 - epsilon)) <
            (frontParameterProbability : Measure FrontParameterSpace)
              (source ∩
                (frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                  Metric.ball x r))
    (parent : ConditionedBoundaryPacketState selector hmeasurable
      hvalid hselector)
    (hparentNorth : parent.source ⊆ contactNorthParameterCap)
    (g K : ℝ) (hg : 0 < g) (hK : 0 ≤ K) :
    ∃ (rho : ℝ) (child : ConditionedBoundaryPacketState selector hmeasurable
        hvalid hselector),
      0 < rho ∧ rho ≤ parent.radius / 4 ∧ rho ≤ 1 ∧
      IsConditionedBoundaryPacketChild parent child ∧
      child.radius < rho ∧
      (frontParameterProbability : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) <
        (frontParameterProbability : Measure FrontParameterSpace) child.source ∧
      child.source ⊆ contactNorthParameterCap ∧
      ∀ (t E : ℝ) (outerCenter : E3),
        0 ≤ E → E ≤ K * child.radius →
        g ≤ |t - child.center (3 : Fin 4)| →
        ¬ (∀ z ∈ child.source,
          ‖northGraphEvaluation
              (selectorLine selector hmeasurable hvalid hselector z.1) t -
            outerCenter‖ ≤ E) := by
  let L : ℝ := 2 * ((6 + 2 * K) / g) + 1
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  let cost : ENNReal :=
    ENNReal.ofReal 2 * metricSphereCapConstant * (ENNReal.ofReal L) ^ 3
  have hcostTop : cost ≠ ⊤ := by
    dsimp [cost]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top metricSphereCapConstant_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hmassTop :
      (frontParameterProbability : Measure FrontParameterSpace) parent.source ≠
        ⊤ := measure_ne_top _ _
  have hchoiceRadius : 0 < min (parent.radius / 4) (1 / L) := by
    rw [lt_min_iff]
    exact ⟨by linarith [parent.radius_pos], one_div_pos.mpr hLpos⟩
  obtain ⟨rho, hrho, hrhoChoice, hrhoOne, hscaleBudget⟩ :=
    exists_scale_fourth_power_le
      ((frontParameterProbability : Measure FrontParameterSpace) parent.source)
      cost parent.source_pos hmassTop hcostTop
      (min (parent.radius / 4) (1 / L)) hchoiceRadius
  have hrhoQuarter : rho ≤ parent.radius / 4 :=
    hrhoChoice.trans (min_le_left _ _)
  have hrhoInvL : rho ≤ 1 / L :=
    hrhoChoice.trans (min_le_right _ _)
  obtain ⟨child, hchild, hchildRho, hmassLower⟩ :=
    parent.exists_quantitative_child_below hepsilon hepsilonFour horacle
      rho hrho hrhoQuarter hrhoOne
  have hchildNorth : child.source ⊆ contactNorthParameterCap := by
    intro z hz
    rw [hchild.1] at hz
    exact hparentNorth hz.1
  refine ⟨rho, child, hrho, hrhoQuarter, hrhoOne, hchild, hchildRho,
    hmassLower, hchildNorth, ?_⟩
  intro t E outerCenter hE hEK hsep hreturn
  have hnumerator :
      6 * child.radius + 2 * E ≤ (6 + 2 * K) * child.radius := by
    nlinarith [child.radius_pos]
  have hquotient :
      (6 * child.radius + 2 * E) / g ≤
        ((6 + 2 * K) * child.radius) / g :=
    (div_le_div_iff_of_pos_right hg).2 hnumerator
  have hcapLe :
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤
        L * child.radius := by
    calc
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤
          2 * (((6 + 2 * K) * child.radius) / g) + child.radius := by
        gcongr
      _ = L * child.radius := by
        dsimp [L]
        field_simp [hg.ne']
  have hchildInvL : child.radius < 1 / L :=
    hchildRho.trans_le hrhoInvL
  have hLchild : L * child.radius < 1 := by
    have hmul := mul_lt_mul_of_pos_left hchildInvL hLpos
    simpa [hLpos.ne'] using hmul
  have hradiusOne :
      2 * ((6 * child.radius + 2 * E) / g) + child.radius ≤ 1 :=
    hcapLe.trans hLchild.le
  have hOfRealCap :
      ENNReal.ofReal
          (2 * ((6 * child.radius + 2 * E) / g) + child.radius) ≤
        ENNReal.ofReal L * ENNReal.ofReal child.radius := by
    calc
      ENNReal.ofReal
          (2 * ((6 * child.radius + 2 * E) / g) + child.radius) ≤
          ENNReal.ofReal (L * child.radius) :=
        ENNReal.ofReal_le_ofReal hcapLe
      _ = ENNReal.ofReal L * ENNReal.ofReal child.radius := by
        rw [ENNReal.ofReal_mul hLpos.le]
  have hgeometricCost :
      ENNReal.ofReal (2 * child.radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) ≤
        cost * (ENNReal.ofReal child.radius) ^ 4 := by
    calc
      ENNReal.ofReal (2 * child.radius) *
          (metricSphereCapConstant *
            (ENNReal.ofReal
              (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) =
          (ENNReal.ofReal 2 * ENNReal.ofReal child.radius) *
            (metricSphereCapConstant *
              (ENNReal.ofReal
                (2 * ((6 * child.radius + 2 * E) / g) + child.radius)) ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (ENNReal.ofReal 2 * ENNReal.ofReal child.radius) *
            (metricSphereCapConstant *
              (ENNReal.ofReal L * ENNReal.ofReal child.radius) ^ 3) := by
        gcongr
      _ = cost * (ENNReal.ofReal child.radius) ^ 4 := by
        dsimp [cost]
        ring
  have hrelativeBudget :
      cost * (ENNReal.ofReal child.radius) ^ 4 ≤
        (frontParameterProbability : Measure FrontParameterSpace) parent.source *
          (((ENNReal.ofReal rho).rpow (4 - epsilon))⁻¹ *
            (ENNReal.ofReal child.radius).rpow (4 - epsilon)) :=
    fourth_power_le_relative_frostman_budget
      ((frontParameterProbability : Measure FrontParameterSpace) parent.source)
      cost epsilon child.radius rho hepsilon hepsilonFour child.radius_pos
      hrho hchildRho.le hscaleBudget
  exact no_separated_return_of_relative_mass parent child hchildNorth
    epsilon rho t g E child.radius outerCenter hmassLower hreturn hE hg hsep
    child.radius_pos hradiusOne (hgeometricCost.trans hrelativeBudget)

end StickyKakeya4
