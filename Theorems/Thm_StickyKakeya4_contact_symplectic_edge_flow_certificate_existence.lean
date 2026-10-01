import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_exact_collision_identity
import Theorems.Thm_StickyKakeya4_maslov_incidence_equivalence
import Theorems.Thm_StickyKakeya4_lossless_edge_flow_carleson
import Theorems.Thm_StickyKakeya4_finite_scale_source_mass
import Theorems.Thm_StickyKakeya4_front_parametrization
import Theorems.Thm_StickyKakeya4_front_parameter_probability
import Theorems.Thm_StickyKakeya4_compact_front
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.MatrixPolynomialAlgebra

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace StickyKakeya4

/-- Algebraic heart of the four-time Maslov firewall: a polynomial of degree
at most three that vanishes at four distinct Reeb times is identically zero. -/
theorem cubic_polynomial_eq_zero_of_four_distinct_roots
    (p : Polynomial ℝ) (time : Fin 4 → ℝ)
    (hdegree : p.natDegree ≤ 3)
    (htime : Function.Injective time)
    (hroot : ∀ i, p.eval (time i) = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p htime hroot
  simpa using (Nat.lt_succ_iff.mpr hdegree)

/-- Every nontrivial `2 × 2` minor of the full-secant Reeb-front matrix
`B + s A` is quadratic, so its real critical-time multiset has cardinality at
most two.  This is the scalar part of the full-secant good-time/window split. -/
theorem quadratic_minor_has_at_most_two_roots
    (p : Polynomial ℝ) (hdegree : p.natDegree ≤ 2) :
    p.roots.card ≤ 2 := by
  exact (Polynomial.card_roots' p).trans hdegree

/-- Scalar bookkeeping for the full-secant normal/tangential factorization:
one normal Reeb-window power and two conditional tangential powers give the
cubic collision-width gain.  This checks only the multiplication of the two
geometric estimates; it does not assert either estimate. -/
theorem normal_tangential_collision_product
    (normalMass fullMass sourceMass K W normalLoss tangentialLoss : ℝ)
    (hsource : 0 ≤ sourceMass) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hnormalLoss : 0 ≤ normalLoss) (htangentialLoss : 0 ≤ tangentialLoss)
    (hnormal : normalMass ≤ K * W * normalLoss * sourceMass)
    (htangential : fullMass ≤ W ^ 2 * tangentialLoss * normalMass) :
    fullMass ≤ W ^ 2 * tangentialLoss *
      (K * W * normalLoss * sourceMass) := by
  have hcoefficient : 0 ≤ W ^ 2 * tangentialLoss :=
    mul_nonneg (sq_nonneg W) htangentialLoss
  calc
    fullMass ≤ W ^ 2 * tangentialLoss * normalMass := htangential
    _ ≤ W ^ 2 * tangentialLoss *
        (K * W * normalLoss * sourceMass) := by
      exact mul_le_mul_of_nonneg_left hnormal hcoefficient

/-- Scalar readback for the terminal atomic-cap reserve.  Once an old-neighbor
row has been normalized by a positive degree `D`, replacing the actual weight
of the assigned old-neighbor cap by its packing upper bound preserves the desired
source-relative estimate.  The geometric input is the cap-weight bound; this
theorem checks only the division and monotonicity step. -/
theorem terminal_atomic_cap_reserve
    (internalMass sourceMass capWeight capBound D : ℝ)
    (hD : 0 < D) (hsource : 0 ≤ sourceMass)
    (hrow : internalMass ≤ (capWeight / D) * sourceMass)
    (hcap : capWeight ≤ capBound) :
    internalMass ≤ (capBound / D) * sourceMass := by
  have hquotient : capWeight / D ≤ capBound / D := by
    exact div_le_div_of_nonneg_right hcap (le_of_lt hD)
  exact hrow.trans (mul_le_mul_of_nonneg_right hquotient hsource)

/-- Scalar readback for the terminal source-cap reversal.  If the original
directed edge mass is at most twice its reversed mass, and the reversed row
sees the original source cap as its old-neighbor cap, then the whole original
high--high terminal mass is bounded by twice the atomic-cap reserve. -/
theorem terminal_source_cap_reversal_reserve
    (originalMass reversedMass sourceMass capWeight capBound D : ℝ)
    (hD : 0 < D) (hsource : 0 ≤ sourceMass)
    (hreverse : originalMass ≤ 2 * reversedMass)
    (hrow : reversedMass ≤ (capWeight / D) * sourceMass)
    (hcap : capWeight ≤ capBound) :
    originalMass ≤ 2 * (capBound / D) * sourceMass := by
  have hreversed : reversedMass ≤ (capBound / D) * sourceMass :=
    terminal_atomic_cap_reserve reversedMass sourceMass capWeight capBound D
      hD hsource hrow hcap
  calc
    originalMass ≤ 2 * reversedMass := hreverse
    _ ≤ 2 * ((capBound / D) * sourceMass) := by
      exact mul_le_mul_of_nonneg_left hreversed (by norm_num)
    _ = 2 * (capBound / D) * sourceMass := by ring

/-- The endpoint-degree boundary strip created by reversal is paid by twice
the original low-degree union charge. -/
theorem terminal_reversal_boundary_union_charge
    (boundaryMass lowMass unionVolume D : ℝ)
    (hboundary : boundaryMass ≤ 2 * lowMass)
    (hlow : lowMass ≤ (D + 1) * unionVolume) :
    boundaryMass ≤ 2 * (D + 1) * unionVolume := by
  calc
    boundaryMass ≤ 2 * lowMass := hboundary
    _ ≤ 2 * ((D + 1) * unionVolume) := by
      exact mul_le_mul_of_nonneg_left hlow (by norm_num)
    _ = 2 * (D + 1) * unionVolume := by ring

/-- Exact scalar ledger for the normalized two-copy lift used on an oriented
cross-cap occurrence.  The symmetric lift assigns one half of the original
mass to each orientation, and restoring the distinguished copy-zero half
recovers the original mass without a hidden comparison constant. -/
theorem normalized_symmetric_lift_and_copy_zero_restore (mass : ℝ) :
    mass / 2 + mass / 2 = mass ∧ 2 * (mass / 2) = mass := by
  constructor <;> ring

/-- Pointwise replacement for a symmetry pigeonhole in the four-source
polarization cycle.  If two sampled planes are `θ`-separated, then the
unchanged distinguished source plane is `θ / 2`-separated from at least one
endpoint.  Hence the entire separated event can be routed sourcewise. -/
theorem separated_pair_has_distinguished_far_endpoint
    {X : Type*} [PseudoMetricSpace X] (v₀ vᵢ vⱼ : X) (θ : ℝ)
    (hsep : θ ≤ dist vᵢ vⱼ) :
    θ / 2 ≤ dist v₀ vᵢ ∨ θ / 2 ≤ dist v₀ vⱼ := by
  by_contra hfar
  push_neg at hfar
  have htri := dist_triangle vᵢ v₀ vⱼ
  rw [dist_comm vᵢ v₀] at htri
  linarith

/-- Positivity of the additional transverse gain created by the prescribed
four-time-firewall polarization partition. -/
theorem firewall_transverse_exponent_positive
    (d₀ : ℝ) (hd₀ : d₀ < 1 / 3) :
    0 < 2 * (1 - d₀) - 1 / 2 := by
  linarith

/-- Legacy exponent bookkeeping for the earlier alternating-return route.
The current terminal proof uses `terminal_source_cap_reversal_reserve` instead,
but this proved scalar lemma is retained for compatibility with the submitted
milestone. -/
theorem terminal_return_exponent_gain
    (d κ : ℝ) (hgain : 3 * d < κ) :
    0 < κ - 3 * d := by
  exact sub_pos.mpr hgain

/-- At one physical point all active off-diagonal row degrees differ only by
the two self weights.  Since source weights lie in `[0,1]`, the endpoint
degrees of every physical collision edge differ by at most one. -/
theorem physical_edge_endpoint_degree_difference
    (F wV wW : ℝ)
    (hwV0 : 0 ≤ wV) (hwV1 : wV ≤ 1)
    (hwW0 : 0 ≤ wW) (hwW1 : wW ≤ 1) :
    |(F - wV) - (F - wW)| ≤ 1 := by
  rw [show (F - wV) - (F - wW) = wW - wV by ring]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A collision edge leaving a row of degree at least `D ≥ 2` enters a row
of degree at least `D/2`.  This is the scalar input which permits reversal of
the terminal old-edge occurrence before applying the atomic cap reserve. -/
theorem reversed_endpoint_retains_high_degree
    (dV dW D : ℝ)
    (hD : 2 ≤ D) (hV : D ≤ dV)
    (hcompare : |dV - dW| ≤ 1) :
    D / 2 ≤ dW := by
  have hright : dV - dW ≤ 1 := (abs_le.mp hcompare).2
  linarith

/-- The determinant polynomial of the Reeb/Maslov pencil `B + s A`. -/
noncomputable def maslovPencilPolynomial (A B : Mat3) : Polynomial ℝ :=
  Matrix.det
    ((Polynomial.X : Polynomial ℝ) • A.map Polynomial.C +
      B.map Polynomial.C)

theorem maslovPencilPolynomial_natDegree_le (A B : Mat3) :
    (maslovPencilPolynomial A B).natDegree ≤ 3 := by
  simpa [maslovPencilPolynomial] using
    (Polynomial.natDegree_det_X_add_C_le A B)

theorem maslovPencilPolynomial_eval (A B : Mat3) (s : ℝ) :
    (maslovPencilPolynomial A B).eval s = Matrix.det (pencil A B s) := by
  rw [maslovPencilPolynomial, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [pencil]
  ring

/-- Four distinct exact Maslov incidences force the whole pencil determinant
to vanish, hence every Reeb time is front-null for the coherent plane. -/
theorem four_time_maslov_pencil_firewall
    (A B : Mat3) (time : Fin 4 → ℝ)
    (htime : Function.Injective time)
    (hincidence : ∀ i, Matrix.det (pencil A B (time i)) = 0) :
    maslovPencilPolynomial A B = 0 := by
  apply cubic_polynomial_eq_zero_of_four_distinct_roots
    (maslovPencilPolynomial A B) time
      (maslovPencilPolynomial_natDegree_le A B) htime
  intro i
  rw [maslovPencilPolynomial_eval]
  exact hincidence i

theorem four_time_maslov_pencil_det_zero_at_every_time
    (A B : Mat3) (time : Fin 4 → ℝ)
    (htime : Function.Injective time)
    (hincidence : ∀ i, Matrix.det (pencil A B (time i)) = 0) :
    ∀ s : ℝ, Matrix.det (pencil A B s) = 0 := by
  have hzero := four_time_maslov_pencil_firewall A B time htime hincidence
  intro s
  rw [← maslovPencilPolynomial_eval, hzero]
  simp

/-- Final scalar step in the quantitative origin-plane separation.  A
determinant lower bound and a Lipschitz comparison with the front-null locus
force a Grassmannian distance lower bound. -/
theorem origin_plane_distance_from_front_null
    (Δ detHorizontal grassmannDistance lipschitzConstant : ℝ)
    (hL : 0 < lipschitzConstant)
    (hdet : Δ ≤ |detHorizontal|)
    (hlipschitz : |detHorizontal| ≤
      lipschitzConstant * grassmannDistance) :
    Δ / lipschitzConstant ≤ grassmannDistance := by
  apply (div_le_iff₀ hL).2
  simpa [mul_comm] using hdet.trans hlipschitz

/-- Row-normalizing a positive collision graph produces a probability kernel.
When the distinguished source weight is placed before that kernel, its full
row mass is exactly the original source weight. -/
theorem normalized_collision_kernel_row_mass
    {n : ℕ} (edge : Fin n → Fin n → ℝ) (degree sourceWeight : Fin n → ℝ)
    (hdegree : ∀ i, degree i = ∑ j, edge i j)
    (hdegreePos : ∀ i, 0 < degree i) (i : Fin n) :
    (∑ j, sourceWeight i * (edge i j / degree i)) = sourceWeight i := by
  calc
    (∑ j, sourceWeight i * (edge i j / degree i)) =
        sourceWeight i * ∑ j, edge i j / degree i := by
      rw [Finset.mul_sum]
    _ = sourceWeight i * ((∑ j, edge i j) / degree i) := by
      rw [Finset.sum_div]
    _ = sourceWeight i := by
      rw [← hdegree i, div_self (ne_of_gt (hdegreePos i)), mul_one]

/-- Summing the normalized rows preserves the complete absolute source mass;
no bush, target cell, or time packet is selected. -/
theorem normalized_collision_kernel_total_mass
    {n : ℕ} (edge : Fin n → Fin n → ℝ) (degree sourceWeight : Fin n → ℝ)
    (hdegree : ∀ i, degree i = ∑ j, edge i j)
    (hdegreePos : ∀ i, 0 < degree i) :
    (∑ i, ∑ j, sourceWeight i * (edge i j / degree i)) =
      ∑ i, sourceWeight i := by
  exact Finset.sum_congr rfl fun i _ =>
    normalized_collision_kernel_row_mass edge degree sourceWeight
      hdegree hdegreePos i

/-- For fractional source weights, the self-collision diagonal is bounded by
the first moment.  This remains true after arbitrary shading restriction. -/
theorem fractional_weight_diagonal_le_source_mass
    {n : ℕ} (weight shadingVolume : Fin n → ℝ)
    (hweightNonneg : ∀ i, 0 ≤ weight i)
    (hweightOne : ∀ i, weight i ≤ 1)
    (hvolume : ∀ i, 0 ≤ shadingVolume i) :
    (∑ i, (weight i) ^ 2 * shadingVolume i) ≤
      ∑ i, weight i * shadingVolume i := by
  apply Finset.sum_le_sum
  intro i _
  have hsquare : (weight i) ^ 2 ≤ weight i := by
    nlinarith [hweightNonneg i, hweightOne i]
  exact mul_le_mul_of_nonneg_right hsquare (hvolume i)

/-- Exact numerical form of the initial incidence reduction.  If source mass
is more than `B` times its physical union, Cauchy--Schwarz forces energy at
least `B` times the source mass.  For `B ≥ 2`, removing a diagonal of size at
most the source mass leaves enough off-diagonal collision mass to normalize a
full source-mass Markov flow. -/
theorem union_failure_forces_linear_offdiagonal
    (sourceMass unionVolume energy diagonal offDiagonal B : ℝ)
    (hsource : 0 < sourceMass) (henergy : 0 ≤ energy)
    (hcauchy : sourceMass ^ 2 ≤ unionVolume * energy)
    (hfailure : B * unionVolume ≤ sourceMass) (hB : 2 ≤ B)
    (hdiagonal : diagonal ≤ sourceMass)
    (hoffDiagonal : offDiagonal = energy - diagonal) :
    sourceMass ≤ offDiagonal := by
  have hunionPos : 0 < unionVolume := by
    by_contra hnot
    have hunionNonpos : unionVolume ≤ 0 := le_of_not_gt hnot
    have hproduct : unionVolume * energy ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hunionNonpos henergy
    have hsquare : 0 < sourceMass ^ 2 := sq_pos_of_pos hsource
    linarith
  have hscaled : B * unionVolume * sourceMass ≤ sourceMass * sourceMass :=
    mul_le_mul_of_nonneg_right hfailure hsource.le
  have hsquare : sourceMass * sourceMass ≤ unionVolume * energy := by
    simpa [pow_two] using hcauchy
  have hcancel : unionVolume * (B * sourceMass) ≤ unionVolume * energy := by
    calc
      unionVolume * (B * sourceMass) = B * unionVolume * sourceMass := by ring
      _ ≤ sourceMass * sourceMass := hscaled
      _ ≤ unionVolume * energy := hsquare
  have henergyLower : B * sourceMass ≤ energy :=
    le_of_mul_le_mul_left hcancel hunionPos
  have htwo : 2 * sourceMass ≤ B * sourceMass :=
    mul_le_mul_of_nonneg_right hB hsource.le
  rw [hoffDiagonal]
  linarith

/-- Rows of zero off-diagonal degree are paid directly by the physical
union.  Therefore, under a factor-two union failure, the positive-degree rows
still carry at least half of the original source mass.  This is the missing
step between row normalization and the root-flow identity. -/
theorem positive_degree_rows_retain_half_source
    (sourceMass positiveDegreeMass zeroDegreeMass unionVolume : ℝ)
    (hdecomp : sourceMass = positiveDegreeMass + zeroDegreeMass)
    (hzero : zeroDegreeMass ≤ unionVolume)
    (hfailure : 2 * unionVolume ≤ sourceMass) :
    sourceMass / 2 ≤ positiveDegreeMass := by
  linarith

/-- A union estimate for the row-normalized positive-degree source recovers
the whole source with only the fixed factor two; no zero-degree row is put
into the Markov kernel by fiat. -/
theorem positive_degree_bound_recovers_full_source
    (sourceMass positiveDegreeMass zeroDegreeMass unionVolume K : ℝ)
    (hdecomp : sourceMass = positiveDegreeMass + zeroDegreeMass)
    (hzero : zeroDegreeMass ≤ unionVolume)
    (hfailure : 2 * unionVolume ≤ sourceMass)
    (hpositive : positiveDegreeMass ≤ K * unionVolume) :
    sourceMass ≤ 2 * K * unionVolume := by
  have hhalf := positive_degree_rows_retain_half_source
    sourceMass positiveDegreeMass zeroDegreeMass unionVolume
      hdecomp hzero hfailure
  linarith

/-- A row of off-diagonal degree below `D` can occur only at a physical point
whose complete fractional multiplicity is below `D + 1`.  This is the
pointwise low-degree payment used before row normalization. -/
theorem low_degree_row_forces_total_multiplicity_lt
    (totalMultiplicity rowWeight degree D : ℝ)
    (hrow : rowWeight ≤ 1)
    (hdegree : degree = totalMultiplicity - rowWeight)
    (hlow : degree < D) :
    totalMultiplicity < D + 1 := by
  linarith

/-- On a dyadic degree layer, a raw collision charge with its natural factor
`D` yields the desired charge for the row-normalized Markov source after that
factor is cancelled once. -/
theorem degree_layer_raw_charge_to_normalized_charge
    (normalizedMass rawEdgeMass D capacity unionVolume : ℝ)
    (hD : 0 < D)
    (hlayerLower : D * normalizedMass ≤ rawEdgeMass)
    (hrawCharge : rawEdgeMass ≤ D * (capacity * unionVolume)) :
    normalizedMass ≤ capacity * unionVolume := by
  have hscaled : D * normalizedMass ≤ D * (capacity * unionVolume) :=
    hlayerLower.trans hrawCharge
  nlinarith

/-- The full two-sided comparison between a normalized row destination and
its raw edge mass on `D ≤ degree < 2D`. -/
theorem degree_layer_raw_markov_comparison
    (normalizedMass rawEdgeMass D : ℝ)
    (hlower : D * normalizedMass ≤ rawEdgeMass)
    (hupper : rawEdgeMass ≤ (2 * D) * normalizedMass) :
    D * normalizedMass ≤ rawEdgeMass ∧
      rawEdgeMass ≤ (2 * D) * normalizedMass :=
  ⟨hlower, hupper⟩

/-- Absolute-occurrence summation turns a per-node normalized-small
coefficient into one root-relative error bound. -/
theorem normalized_small_destinations_root_bound
    (smallMass depthFactor coefficient rootMass : ℝ)
    (hsmall : smallMass ≤ depthFactor * coefficient * rootMass)
    (hroot : 0 ≤ rootMass)
    (hreserve : 4 * depthFactor * coefficient ≤ 1) :
    4 * smallMass ≤ rootMass := by
  have hscaled := mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 4 by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hreserve hroot]

/-- A quarter-root geometric reserve and a quarter-root deterministic tail
combine into the half-root error hypothesis required by the finite
certificate; neither is charged to the physical union. -/
theorem geometric_and_deterministic_errors_fit_half_root
    (geometricError deterministicError rootMass : ℝ)
    (hgeometric : 4 * geometricError ≤ rootMass)
    (hdeterministic : 4 * deterministicError ≤ rootMass) :
    2 * (geometricError + deterministicError) ≤ rootMass := by
  linarith

/-- A nonzero destination which is stable under hereditary restriction cannot
be discarded with a uniform relative coefficient strictly below one: restrict
the source to that destination and its relative mass becomes one. -/
theorem hereditary_normalized_small_destination_impossible
    (destinationMass κ : ℝ)
    (hmass : 0 < destinationMass)
    (hκ : κ < 1)
    (hhereditary : destinationMass ≤ κ * destinationMass) :
    False := by
  nlinarith

/-- Once an oriented flat-packet output is disintegrated on the edge-flow
source coordinate, exact decomposition and source domination make it a
coefficient-one continuing child flow.  The geometric input is recorded by
the uniform strict contraction of every child cap. -/
theorem source_rooted_flat_packet_localization
    {ι : Type*} [Fintype ι]
    (incoming flatMass parentRadius contraction : ENNReal)
    (childMass childRadius : ι → ENNReal)
    (hdecomp : flatMass = ∑ i, childMass i)
    (hsource : (∑ i, childMass i) ≤ incoming)
    (hcap : ∀ i, childRadius i ≤ contraction * parentRadius) :
    flatMass ≤ incoming ∧
      ∀ i, childRadius i ≤ contraction * parentRadius := by
  constructor
  · rw [hdecomp]
    exact hsource
  · exact hcap

/-- After Minkowski and Cauchy--Schwarz have converted all accepted residual
leaves into one lower bound on the union, the root-mass bound pays their
complete absolute mass with one global union coefficient. -/
theorem accepted_residual_global_union_charge
    (residualMass rootMass K unionVolume : ℝ)
    (hroot : 0 ≤ rootMass)
    (hmass : residualMass ≤ rootMass)
    (hunion : 1 ≤ K * unionVolume) :
    residualMass ≤ rootMass * K * unionVolume := by
  calc
    residualMass ≤ rootMass := hmass
    _ = rootMass * 1 := by ring
    _ ≤ rootMass * (K * unionVolume) :=
      mul_le_mul_of_nonneg_left hunion hroot
    _ = rootMass * K * unionVolume := by ring

/-- Pointwise combinatorial form of the zero-degree payment.  If two retained
zero-degree rows cannot both have positive weight, their total fractional
weight is at most one, hence is bounded by the indicator of the physical
union after restricting to points where the set is nonempty. -/
theorem pairwise_exclusive_fractional_weights_le_one
    {n : ℕ} (weight : Fin n → ENNReal) (zeroRows : Finset (Fin n))
    (hweight : ∀ i, weight i ≤ 1)
    (hexclusive : ∀ {i j}, i ∈ zeroRows → j ∈ zeroRows →
      0 < weight i → 0 < weight j → i = j) :
    ∑ i ∈ zeroRows, weight i ≤ 1 := by
  by_cases hpos : ∃ i ∈ zeroRows, 0 < weight i
  · obtain ⟨i, hi, hwi⟩ := hpos
    have hsum : ∑ j ∈ zeroRows, weight j = weight i := by
      rw [Finset.sum_eq_single i]
      · intro j hj hji
        have hjzero : weight j = 0 := by
          apply bot_unique
          exact le_of_not_gt fun hwj =>
            hji (hexclusive hj hi hwj hwi)
        exact hjzero
      · intro hnot
        exact False.elim (hnot hi)
    rw [hsum]
    exact hweight i
  · have hzero : ∀ i ∈ zeroRows, weight i = 0 := by
      intro i hi
      apply bot_unique
      exact le_of_not_gt fun hwi => hpos ⟨i, hi, hwi⟩
    calc
      (∑ i ∈ zeroRows, weight i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hzero i hi
      _ ≤ 1 := bot_le

/-- A same-window Maslov edge returns its target endpoint to the current
physical bush.  This is the metric part of the same-window amplification
branch: no new Reeb probe is introduced. -/
theorem same_window_target_rejoins_bush
    (a b a' b' c : E3) (s t R r δ U : ℝ)
    (hsource : ‖b + s • a - c‖ ≤ R)
    (hcollision : ‖(b + t • a) - (b' + t • a')‖ ≤ r)
    (htime : |t - s| ≤ δ)
    (ha : ‖a‖ ≤ U) (ha' : ‖a'‖ ≤ U) :
    ‖b' + s • a' - c‖ ≤ R + r + 2 * δ * U := by
  have hδ : 0 ≤ δ := (abs_nonneg (t - s)).trans htime
  have hU : 0 ≤ U := (norm_nonneg a).trans ha
  have hdir : ‖a' - a‖ ≤ 2 * U := by
    calc
      ‖a' - a‖ ≤ ‖a'‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ U + U := add_le_add ha' ha
      _ = 2 * U := by ring
  have hshift : ‖(s - t) • (a' - a)‖ ≤ 2 * δ * U := by
    rw [norm_smul, Real.norm_eq_abs]
    have hst : |s - t| ≤ δ := by simpa [abs_sub_comm] using htime
    calc
      |s - t| * ‖a' - a‖ ≤ δ * (2 * U) :=
        mul_le_mul hst hdir (norm_nonneg _) hδ
      _ = 2 * δ * U := by ring
  have hid :
      b' + s • a' - c =
        (b + s • a - c) - ((b + t • a) - (b' + t • a')) +
          (s - t) • (a' - a) := by
    module
  rw [hid]
  calc
    ‖(b + s • a - c) - ((b + t • a) - (b' + t • a')) +
        (s - t) • (a' - a)‖
        ≤ ‖(b + s • a - c) - ((b + t • a) - (b' + t • a'))‖ +
            ‖(s - t) • (a' - a)‖ := norm_add_le _ _
    _ ≤ (‖b + s • a - c‖ + ‖(b + t • a) - (b' + t • a')‖) +
          ‖(s - t) • (a' - a)‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ R + r + 2 * δ * U := by linarith

/-- The numerical core of the same-window branch.  A degree layer is either
quadratic in the bush mass or its retained old-neighbour flow forces an
amplified target bush. -/
theorem same_window_quadratic_or_amplified
    (q θ B c₀ edgeMass E targetMass : ℝ)
    (hq : 0 < q) (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hc₀ : 0 ≤ c₀)
    (hdegreeLower : θ * q ≤ edgeMass)
    (hdegreeUpper : edgeMass ≤ 2 * θ * q)
    (hretained : c₀ * edgeMass ≤ E)
    (hincidence : E ≤ q * targetMass) :
    (θ ≤ B * q → edgeMass ≤ 2 * B * q ^ 2) ∧
      (B * q < θ → c₀ * B * q ≤ targetMass) := by
  constructor <;> intro hbranch
  · nlinarith
  · have hBθ := mul_le_mul_of_nonneg_left (le_of_lt hbranch) hc₀
    have hBθq := mul_le_mul_of_nonneg_right hBθ (le_of_lt hq)
    have hdegreeScaled := mul_le_mul_of_nonneg_left hdegreeLower hc₀
    have hproduct : q * (c₀ * B * q) ≤ q * targetMass := by
      calc
        q * (c₀ * B * q) = (c₀ * (B * q)) * q := by ring
        _ ≤ (c₀ * θ) * q := hBθq
        _ = c₀ * (θ * q) := by ring
        _ ≤ c₀ * edgeMass := hdegreeScaled
        _ ≤ E := hretained
        _ ≤ q * targetMass := hincidence
    nlinarith [hproduct]

/-- Nonnegative disjoint layer masses have square sum at most the square of
their total mass.  This is the lossless summation used after the same-window
quadratic alternative has been selected on every layer. -/
theorem sum_sq_le_sq_sum_of_nonnegative
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) :
    (∑ i ∈ s, (q i) ^ 2) ≤ (∑ i ∈ s, q i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hqa : 0 ≤ q a := hq a (Finset.mem_insert_self a s)
      have hqs : ∀ i ∈ s, 0 ≤ q i := by
        intro i hi
        exact hq i (Finset.mem_insert_of_mem hi)
      have hs : 0 ≤ ∑ i ∈ s, q i := Finset.sum_nonneg hqs
      have hih := ih hqs
      nlinarith

/-- Summing the quadratic alternatives over a finite disjoint bush family
does not introduce a layer-count loss. -/
theorem same_window_family_square_sum
    {n : ℕ} (q edgeMass : Fin n → ℝ) (B : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hB : 0 ≤ B)
    (hquadratic : ∀ i, edgeMass i ≤ B * (q i) ^ 2) :
    (∑ i, edgeMass i) ≤ B * (∑ i, q i) ^ 2 := by
  calc
    (∑ i, edgeMass i) ≤ ∑ i, B * (q i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hquadratic i
    _ = B * ∑ i, (q i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B * (∑ i, q i) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_sq_le_sq_sum_of_nonnegative Finset.univ q
          (fun i _ => hq i)) hB

/-- A uniform cap-mass bound linearizes the same-window quadratic payments.
Thus summing all cap pieces costs their total source mass, not their number. -/
theorem same_window_cap_square_payment
    {n : ℕ} (q edgeMass : Fin n → ℝ) (B capMass : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hB : 0 ≤ B)
    (hcap : ∀ i, q i ≤ capMass)
    (hquadratic : ∀ i, edgeMass i ≤ B * (q i) ^ 2) :
    (∑ i, edgeMass i) ≤ B * capMass * ∑ i, q i := by
  calc
    (∑ i, edgeMass i) ≤ ∑ i, B * (q i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hquadratic i
    _ ≤ ∑ i, B * capMass * q i := by
      apply Finset.sum_le_sum
      intro i _
      have hsquare : (q i) ^ 2 ≤ capMass * q i := by
        nlinarith [hq i, hcap i]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsquare hB
    _ = B * capMass * ∑ i, q i := by
      rw [Finset.mul_sum]

/-- The deterministic cap threshold converts the linearized cap-square
payment into the desired quadratic root-mass target. -/
theorem same_window_cap_square_reaches_quadratic
    {n : ℕ} (q edgeMass : Fin n → ℝ)
    (B capMass rootMass gain : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hB : 0 ≤ B) (hcapMass : 0 ≤ capMass)
    (hroot : 0 ≤ rootMass)
    (hcap : ∀ i, q i ≤ capMass)
    (hquadratic : ∀ i, edgeMass i ≤ B * (q i) ^ 2)
    (htotal : ∑ i, q i ≤ rootMass)
    (hsaturation : B * capMass ≤ rootMass * gain) :
    (∑ i, edgeMass i) ≤ rootMass ^ 2 * gain := by
  calc
    (∑ i, edgeMass i) ≤ B * capMass * ∑ i, q i :=
      same_window_cap_square_payment q edgeMass B capMass hq hB hcap hquadratic
    _ ≤ B * capMass * rootMass :=
      mul_le_mul_of_nonneg_left htotal (mul_nonneg hB hcapMass)
    _ ≤ (rootMass * gain) * rootMass :=
      mul_le_mul_of_nonneg_right hsaturation hroot
    _ = rootMass ^ 2 * gain := by ring

/-- Iterating only the amplified same-window branch gives genuine geometric
growth of the physical bush mass. -/
theorem same_window_amplification_iterate
    (mass : ℕ → ℝ) (initial growth : ℝ)
    (hgrowth : 0 ≤ growth)
    (hzero : initial ≤ mass 0)
    (hstep : ∀ k, growth * mass k ≤ mass (k + 1)) :
    ∀ L, growth ^ L * initial ≤ mass L := by
  intro L
  induction L with
  | zero => simpa using hzero
  | succ L ih =>
      calc
        growth ^ (L + 1) * initial = growth * (growth ^ L * initial) := by
          rw [pow_succ]
          ring
        _ ≤ growth * mass L := mul_le_mul_of_nonneg_left ih hgrowth
        _ ≤ mass (L + 1) := hstep L

/-- Since selector-direction mass is at most one, an amplification chain of
length `L` forces `growth ^ L * initial ≤ 1`. -/
theorem same_window_amplification_bounded
    (mass : ℕ → ℝ) (initial growth : ℝ)
    (hgrowth : 0 ≤ growth)
    (hzero : initial ≤ mass 0)
    (hstep : ∀ k, growth * mass k ≤ mass (k + 1))
    (hupper : ∀ k, mass k ≤ 1) :
    ∀ L, growth ^ L * initial ≤ 1 := by
  intro L
  exact (same_window_amplification_iterate mass initial growth
    hgrowth hzero hstep L).trans (hupper L)

/-- Numerical heart of the common-target Markovization.  If the available
target support does not grow, the part below multiplicity `S = sqrt B` carries
at most half of the incoming normalized edge mass. -/
theorem common_target_high_multiplicity_retention
    (c₀ B Q W targetSupport lowMass S : ℝ)
    (hS : 0 ≤ S) (hSsq : S * S = B)
    (hSupport : targetSupport ≤ (c₀ / 2) * S * Q)
    (hLow : lowMass ≤ S * targetSupport)
    (hTotal : c₀ * B * Q ≤ W) :
    lowMass ≤ W / 2 := by
  calc
    lowMass ≤ S * targetSupport := hLow
    _ ≤ S * ((c₀ / 2) * S * Q) :=
      mul_le_mul_of_nonneg_left hSupport hS
    _ = (c₀ * B * Q) / 2 := by rw [← hSsq]; ring
    _ ≤ W / 2 := by linarith

/-- Cauchy--Schwarz converts failure of amplified target-union growth into a
linear weighted common-target star.  `secondMoment - diagonal` is the
off-diagonal overlap content, and the square-root threshold is encoded by
`S * S = B`. -/
theorem amplified_target_overlap_star
    (c₀ B Q W targetSupport secondMoment diagonal offDiagonal S : ℝ)
    (hc₀ : 0 ≤ c₀) (hQ : 0 ≤ Q) (hW : 0 ≤ W)
    (hS : 1 ≤ S) (hSsq : S * S = B)
    (hSupportPos : 0 < targetSupport)
    (hSupport : targetSupport ≤ (c₀ / 2) * S * Q)
    (hTotal : c₀ * B * Q ≤ W)
    (hSecond : W * W ≤ targetSupport * secondMoment)
    (hDiagonal : diagonal ≤ W)
    (hOffDiagonal : offDiagonal = secondMoment - diagonal) :
    S * W ≤ offDiagonal := by
  have hSnonneg : 0 ≤ S := le_trans (by norm_num) hS
  have htwosNonneg : 0 ≤ 2 * S := mul_nonneg (by norm_num) hSnonneg
  have hsupportScaled :
      (2 * S) * targetSupport ≤ (2 * S) * ((c₀ / 2) * S * Q) :=
    mul_le_mul_of_nonneg_left hSupport htwosNonneg
  have hrootFlow : (2 * S) * targetSupport ≤ W := by
    calc
      (2 * S) * targetSupport
          ≤ (2 * S) * ((c₀ / 2) * S * Q) := hsupportScaled
      _ = c₀ * B * Q := by rw [← hSsq]; ring
      _ ≤ W := hTotal
  have hscaled : ((2 * S) * targetSupport) * W ≤ W * W :=
    mul_le_mul_of_nonneg_right hrootFlow hW
  have hmomentCross :
      targetSupport * (2 * S * W) ≤ targetSupport * secondMoment := by
    calc
      targetSupport * (2 * S * W) = ((2 * S) * targetSupport) * W := by ring
      _ ≤ W * W := hscaled
      _ ≤ targetSupport * secondMoment := hSecond
  have hmoment : 2 * S * W ≤ secondMoment :=
    by nlinarith [hmomentCross]
  have hWleSW : W ≤ S * W := by
    nlinarith
  rw [hOffDiagonal]
  linarith

/-- On one dyadic source-mass layer, retaining at least half of the normalized
mass above the common-target threshold retains at least one quarter of the
original edge occurrence mass. -/
theorem common_target_high_edge_fraction
    (q W lowMass totalEdge highEdge : ℝ)
    (hq : 0 ≤ q)
    (hLow : lowMass ≤ W / 2)
    (hTotalEdge : totalEdge ≤ 2 * q * W)
    (hHighEdge : q * (W - lowMass) ≤ highEdge) :
    totalEdge / 4 ≤ highEdge := by
  have hremaining : W / 2 ≤ W - lowMass := by linarith
  have hscaled : q * (W / 2) ≤ q * (W - lowMass) :=
    mul_le_mul_of_nonneg_left hremaining hq
  calc
    totalEdge / 4 ≤ q * (W / 2) := by linarith
    _ ≤ q * (W - lowMass) := hscaled
    _ ≤ highEdge := hHighEdge

/-- At a target of normalized multiplicity at least `S`, no source atom in a
dyadic mass layer has conditional probability greater than `2 / S`.  This is
the estimate that permits repeated sampling of distinct source flags without
raising the incoming edge mass to a power. -/
theorem common_target_different_source_probability
    (q sourceMass n totalDensity sourceDensity S : ℝ)
    (hq : 0 < q) (hS : 0 < S)
    (hsource : sourceMass ≤ 2 * q)
    (hdensity : sourceDensity ≤ sourceMass)
    (hmultiplicity : S ≤ n)
    (htotal : q * n ≤ totalDensity) :
    sourceDensity / totalDensity ≤ 2 / S := by
  have hn : 0 < n := hS.trans_le hmultiplicity
  have htotalPos : 0 < totalDensity :=
    (mul_pos hq hn).trans_le htotal
  have h₁ : sourceDensity * S ≤ sourceMass * S :=
    mul_le_mul_of_nonneg_right hdensity hS.le
  have h₂ : sourceMass * S ≤ (2 * q) * S :=
    mul_le_mul_of_nonneg_right hsource hS.le
  have h₃ : (2 * q) * S ≤ 2 * (q * n) := by
    have := mul_le_mul_of_nonneg_left hmultiplicity (by positivity : 0 ≤ 2 * q)
    nlinarith
  have h₄ : 2 * (q * n) ≤ 2 * totalDensity := by linarith
  have hcross : sourceDensity * S ≤ 2 * totalDensity :=
    h₁.trans (h₂.trans (h₃.trans h₄))
  apply (div_le_iff₀ htotalPos).2
  rw [show 2 / S * totalDensity = (2 * totalDensity) / S by ring]
  exact (le_div_iff₀ hS).2 hcross

/-- There are six unordered pairs among four sampled source flags.  Thus the
per-pair common-target collision bound `2 / S` loses only `12 / S`; no power
of the incoming edge mass is introduced. -/
theorem four_flag_collision_union_bound
    (S : ℝ) (pairCollision : Fin 6 → ℝ)
    (hpair : ∀ i, pairCollision i ≤ 2 / S) :
    (∑ i, pairCollision i) ≤ 12 / S := by
  calc
    (∑ i, pairCollision i) ≤ ∑ _i : Fin 6, 2 / S :=
      Finset.sum_le_sum fun i _ => hpair i
    _ = 12 / S := by simp; ring

/-- Once the common-target multiplicity threshold is at least `24`, removing
all configurations with a repeated pair of source flags leaves at least half
of the four-flag mass. -/
theorem four_distinct_flag_retention
    (S totalMass repeatedMass : ℝ)
    (hS : 24 ≤ S) (htotal : 0 ≤ totalMass)
    (hrepeated : repeatedMass ≤ (12 / S) * totalMass) :
    totalMass / 2 ≤ totalMass - repeatedMass := by
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS
  have hfactor : 12 / S ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hSpos).2
    linarith
  have hbad : repeatedMass ≤ totalMass / 2 := by
    calc
      repeatedMass ≤ (12 / S) * totalMass := hrepeated
      _ ≤ ((1 : ℝ) / 2) * totalMass :=
        mul_le_mul_of_nonneg_right hfactor htotal
      _ = totalMass / 2 := by ring
  linarith

/-- The complete scalar retention in the common-target Markov branch.  The
high-multiplicity restriction keeps one quarter of the incoming edge flow and
removing repeated source flags keeps one half of that restriction.  Hence four
distinct source flags retain one eighth of the original edge flow, linearly. -/
theorem common_target_four_source_linear_retention
    (q W lowMass totalEdge highEdge repeatedMass distinctMass S : ℝ)
    (hq : 0 ≤ q) (htotalNonneg : 0 ≤ totalEdge)
    (hLow : lowMass ≤ W / 2)
    (hTotalEdge : totalEdge ≤ 2 * q * W)
    (hHighEdge : q * (W - lowMass) ≤ highEdge)
    (hS : 24 ≤ S)
    (hRepeated : repeatedMass ≤ (12 / S) * highEdge)
    (hDistinct : distinctMass = highEdge - repeatedMass) :
    totalEdge / 8 ≤ distinctMass := by
  have hquarter : totalEdge / 4 ≤ highEdge :=
    common_target_high_edge_fraction q W lowMass totalEdge highEdge
      hq hLow hTotalEdge hHighEdge
  have hhighNonneg : 0 ≤ highEdge := by linarith
  have hhalf : highEdge / 2 ≤ highEdge - repeatedMass :=
    four_distinct_flag_retention S highEdge repeatedMass
      hS hhighNonneg hRepeated
  rw [hDistinct]
  linarith

/-- Weighted transverse-cell summation.  A pointwise two-plane intersection
bound is divided by the reuse threshold `K`, so the global estimate is charged
to total reuse rather than to the number of graph cells. -/
theorem transverse_reuse_weighted_sum
    {n : ℕ} (cellMass reuse : Fin n → ℝ)
    (C w K θ : ℝ)
    (hC : 0 ≤ C) (hK : 0 < K) (hθ : 0 < θ)
    (hcell : ∀ i, cellMass i ≤ C * w ^ 2 / θ)
    (hreuse : ∀ i, K ≤ reuse i) :
    (∑ i, cellMass i) ≤
      (C * w ^ 2 / (K * θ)) * ∑ i, reuse i := by
  calc
    (∑ i, cellMass i) ≤
        ∑ i, (C * w ^ 2 / (K * θ)) * reuse i := by
      apply Finset.sum_le_sum
      intro i _
      have hbase : 0 ≤ C * w ^ 2 / θ :=
        div_nonneg (mul_nonneg hC (sq_nonneg w)) hθ.le
      have hratio : 1 ≤ reuse i / K := by
        apply (le_div_iff₀ hK).2
        simpa using hreuse i
      calc
        cellMass i ≤ C * w ^ 2 / θ := hcell i
        _ ≤ (C * w ^ 2 / θ) * (reuse i / K) := by
          simpa using mul_le_mul_of_nonneg_left hratio hbase
        _ = (C * w ^ 2 / (K * θ)) * reuse i := by
          field_simp [ne_of_gt hK, ne_of_gt hθ]
    _ = (C * w ^ 2 / (K * θ)) * ∑ i, reuse i := by
      rw [Finset.mul_sum]

/-- If the total reuse itself has a Carleson budget, the transverse cell
family inherits that budget with the reciprocal-reuse gain. -/
theorem transverse_reuse_carleson
    {n : ℕ} (cellMass reuse : Fin n → ℝ)
    (C w K θ totalReuse : ℝ)
    (hC : 0 ≤ C) (hK : 0 < K) (hθ : 0 < θ)
    (hcell : ∀ i, cellMass i ≤ C * w ^ 2 / θ)
    (hreuse : ∀ i, K ≤ reuse i)
    (hreuseTotal : ∑ i, reuse i ≤ totalReuse) :
    (∑ i, cellMass i) ≤
      (C * w ^ 2 / (K * θ)) * totalReuse := by
  calc
    (∑ i, cellMass i) ≤
        (C * w ^ 2 / (K * θ)) * ∑ i, reuse i :=
      transverse_reuse_weighted_sum cellMass reuse C w K θ
        hC hK hθ hcell hreuse
    _ ≤ (C * w ^ 2 / (K * θ)) * totalReuse := by
      apply mul_le_mul_of_nonneg_left hreuseTotal
      exact div_nonneg (mul_nonneg hC (sq_nonneg w))
        (mul_nonneg hK.le hθ.le)

/-- Exact weighted double count for anchored packet reuse.  Summing the cell
reuse multiplicities equals summing cell incidences inside packets and is at
most the total retained endpoint occurrence. -/
theorem anchor_reuse_le_endpoint_occurrence
    {p c : ℕ} (incidence : Fin p → Fin c → ENNReal)
    (endpointOccurrence : Fin p → ENNReal)
    (hpacket : ∀ q, ∑ χ, incidence q χ ≤ endpointOccurrence q) :
    (∑ χ, ∑ q, incidence q χ) ≤ ∑ q, endpointOccurrence q := by
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun q _ => hpacket q

/-- Absolute occurrence domination at every depth turns the nodewise reuse
double count into an `L * rootMass` all-generation budget. -/
theorem anchor_reuse_across_depths
    {L n : ℕ} (reuse : Fin L → Fin n → ENNReal) (rootMass : ENNReal)
    (hlevel : ∀ ℓ, ∑ i, reuse ℓ i ≤ rootMass) :
    (∑ ℓ, ∑ i, reuse ℓ i) ≤ (L : ENNReal) * rootMass := by
  calc
    (∑ ℓ, ∑ i, reuse ℓ i) ≤ ∑ _ℓ : Fin L, rootMass :=
      Finset.sum_le_sum fun ℓ _ => hlevel ℓ
    _ = (L : ENNReal) * rootMass := by simp

/-- Global Carleson synthesis directly from the distinguished endpoint
occurrence.  Every geometric destination is allowed its own local coefficient,
but cells, packets, and branches are all summed before the depth estimate.
Thus the only multiplicity cost is the number of depths, never the number of
descendants or graph cells. -/
theorem category_capacity_from_endpoint_occurrence
    {L k p c : ℕ}
    (incidence : Fin L → Fin p → Fin c → ENNReal)
    (endpointOccurrence : Fin L → Fin p → ENNReal)
    (capacity : Fin k → Fin L → Fin c → ENNReal)
    (factor : Fin k → ENNReal) (rootMass : ENNReal)
    (hlocal : ∀ q ℓ χ,
      capacity q ℓ χ ≤ factor q * ∑ a, incidence ℓ a χ)
    (hpacket : ∀ ℓ a,
      ∑ χ, incidence ℓ a χ ≤ endpointOccurrence ℓ a)
    (hlevel : ∀ ℓ, ∑ a, endpointOccurrence ℓ a ≤ rootMass) :
    (∑ ℓ, ∑ χ, ∑ q, capacity q ℓ χ) ≤
      (L : ENNReal) * (∑ q, factor q) * rootMass := by
  have hincidence : ∀ ℓ, ∑ χ, ∑ a, incidence ℓ a χ ≤ rootMass := by
    intro ℓ
    calc
      (∑ χ, ∑ a, incidence ℓ a χ) =
          ∑ a, ∑ χ, incidence ℓ a χ := Finset.sum_comm
      _ ≤ ∑ a, endpointOccurrence ℓ a :=
        Finset.sum_le_sum fun a _ => hpacket ℓ a
      _ ≤ rootMass := hlevel ℓ
  calc
    (∑ ℓ, ∑ χ, ∑ q, capacity q ℓ χ) ≤
        ∑ ℓ, ∑ χ, ∑ q, factor q * ∑ a, incidence ℓ a χ :=
      Finset.sum_le_sum fun ℓ _ =>
        Finset.sum_le_sum fun χ _ =>
          Finset.sum_le_sum fun q _ => hlocal q ℓ χ
    _ = ∑ ℓ, (∑ q, factor q) * (∑ χ, ∑ a, incidence ℓ a χ) := by
      apply Finset.sum_congr rfl
      intro ℓ _
      calc
        (∑ χ, ∑ q, factor q * ∑ a, incidence ℓ a χ) =
            ∑ q, ∑ χ, factor q * ∑ a, incidence ℓ a χ :=
          Finset.sum_comm
        _ = ∑ q, factor q * (∑ χ, ∑ a, incidence ℓ a χ) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
        _ = (∑ q, factor q) * (∑ χ, ∑ a, incidence ℓ a χ) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ _ℓ : Fin L, (∑ q, factor q) * rootMass :=
      Finset.sum_le_sum fun ℓ _ => by
        simpa [mul_comm] using
          (mul_le_mul_right (hincidence ℓ) (∑ q, factor q))
    _ = (L : ENNReal) * (∑ q, factor q) * rootMass := by
      simp
      ring

/-- A synchronized Reeb packet and a target carrier cell give an actual
physical point-probe bush.  This is the quantitative metric estimate behind
the target-cell partition in the same-window carrier branch. -/
theorem synchronized_target_cell_rejoins_bush
    (aSource bSource aTarget bTarget aCell bCell : E3)
    (u s t ρ ε δ η U : ℝ)
    (hcollision :
      ‖(bSource + u • aSource) - (bTarget + u • aTarget)‖ ≤ ρ)
    (hsync : |s - u| ≤ ε)
    (hpacket : |t - s| ≤ δ)
    (hcell :
      ‖(bTarget + t • aTarget) - (bCell + t • aCell)‖ ≤ η)
    (hSource : ‖aSource‖ ≤ U) (hTarget : ‖aTarget‖ ≤ U) :
    ‖(bSource + t • aSource) - (bCell + t • aCell)‖
      ≤ ρ + 2 * U * (ε + δ) + η := by
  have hε : 0 ≤ ε := (abs_nonneg (s - u)).trans hsync
  have hδ : 0 ≤ δ := (abs_nonneg (t - s)).trans hpacket
  have hU : 0 ≤ U := (norm_nonneg aSource).trans hSource
  have htime : |t - u| ≤ δ + ε := by
    rw [abs_le] at hsync hpacket ⊢
    constructor <;> linarith
  have hdir : ‖aSource - aTarget‖ ≤ 2 * U := by
    calc
      ‖aSource - aTarget‖ ≤ ‖aSource‖ + ‖aTarget‖ := norm_sub_le _ _
      _ ≤ U + U := add_le_add hSource hTarget
      _ = 2 * U := by ring
  have hshift : ‖(t - u) • (aSource - aTarget)‖ ≤ 2 * U * (ε + δ) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t - u| * ‖aSource - aTarget‖
          ≤ (δ + ε) * (2 * U) :=
        mul_le_mul htime hdir (norm_nonneg _) (add_nonneg hδ hε)
      _ = 2 * U * (ε + δ) := by ring
  have hid :
      (bSource + t • aSource) - (bCell + t • aCell) =
        ((bSource + u • aSource) - (bTarget + u • aTarget)) +
          (t - u) • (aSource - aTarget) +
          ((bTarget + t • aTarget) - (bCell + t • aCell)) := by
    module
  rw [hid]
  calc
    ‖((bSource + u • aSource) - (bTarget + u • aTarget)) +
        (t - u) • (aSource - aTarget) +
        ((bTarget + t • aTarget) - (bCell + t • aCell))‖
        ≤
          ‖((bSource + u • aSource) - (bTarget + u • aTarget)) +
            (t - u) • (aSource - aTarget)‖ +
          ‖(bTarget + t • aTarget) - (bCell + t • aCell)‖ :=
      norm_add_le _ _
    _ ≤
        (‖(bSource + u • aSource) - (bTarget + u • aTarget)‖ +
          ‖(t - u) • (aSource - aTarget)‖) +
          ‖bTarget + t • aTarget - (bCell + t • aCell)‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ρ + 2 * U * (ε + δ) + η := by linarith

/-- Four real Reeb labels are either pairwise `δ`-separated or are covered by
three closed packets of radius `δ`.  In the second branch a close pair shares
one packet and the other two labels supply the remaining packet centers. -/
theorem four_reeb_times_separated_or_three_packets
    (s₀ s₁ s₂ s₃ δ : ℝ) :
    (δ < |s₀ - s₁| ∧ δ < |s₀ - s₂| ∧ δ < |s₀ - s₃| ∧
      δ < |s₁ - s₂| ∧ δ < |s₁ - s₃| ∧ δ < |s₂ - s₃|) ∨
    ∃ t₀ t₁ t₂ : ℝ,
      (|s₀ - t₀| ≤ δ ∨ |s₀ - t₁| ≤ δ ∨ |s₀ - t₂| ≤ δ) ∧
      (|s₁ - t₀| ≤ δ ∨ |s₁ - t₁| ≤ δ ∨ |s₁ - t₂| ≤ δ) ∧
      (|s₂ - t₀| ≤ δ ∨ |s₂ - t₁| ≤ δ ∨ |s₂ - t₂| ≤ δ) ∧
      (|s₃ - t₀| ≤ δ ∨ |s₃ - t₁| ≤ δ ∨ |s₃ - t₂| ≤ δ) := by
  by_cases h₀₁ : δ < |s₀ - s₁|
  · by_cases h₀₂ : δ < |s₀ - s₂|
    · by_cases h₀₃ : δ < |s₀ - s₃|
      · by_cases h₁₂ : δ < |s₁ - s₂|
        · by_cases h₁₃ : δ < |s₁ - s₃|
          · by_cases h₂₃ : δ < |s₂ - s₃|
            · exact Or.inl ⟨h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃⟩
            · right
              have hclose : |s₂ - s₃| ≤ δ := le_of_not_gt h₂₃
              have hδ : 0 ≤ δ := (abs_nonneg (s₂ - s₃)).trans hclose
              refine ⟨s₂, s₀, s₁, ?_⟩
              simp [hδ, hclose, abs_sub_comm]
          · right
            have hclose : |s₁ - s₃| ≤ δ := le_of_not_gt h₁₃
            have hδ : 0 ≤ δ := (abs_nonneg (s₁ - s₃)).trans hclose
            refine ⟨s₁, s₀, s₂, ?_⟩
            simp [hδ, hclose, abs_sub_comm]
        · right
          have hclose : |s₁ - s₂| ≤ δ := le_of_not_gt h₁₂
          have hδ : 0 ≤ δ := (abs_nonneg (s₁ - s₂)).trans hclose
          refine ⟨s₁, s₀, s₃, ?_⟩
          simp [hδ, hclose, abs_sub_comm]
      · right
        have hclose : |s₀ - s₃| ≤ δ := le_of_not_gt h₀₃
        have hδ : 0 ≤ δ := (abs_nonneg (s₀ - s₃)).trans hclose
        refine ⟨s₀, s₁, s₂, ?_⟩
        simp [hδ, hclose, abs_sub_comm]
    · right
      have hclose : |s₀ - s₂| ≤ δ := le_of_not_gt h₀₂
      have hδ : 0 ≤ δ := (abs_nonneg (s₀ - s₂)).trans hclose
      refine ⟨s₀, s₁, s₃, ?_⟩
      simp [hδ, hclose, abs_sub_comm]
  · right
    have hclose : |s₀ - s₁| ≤ δ := le_of_not_gt h₀₁
    have hδ : 0 ≤ δ := (abs_nonneg (s₀ - s₁)).trans hclose
    refine ⟨s₀, s₂, s₃, ?_⟩
    simp [hδ, hclose, abs_sub_comm]

/-- The exact tail ledger for the three-packet stopping: removing at least
half of the current remainder at every round leaves a geometrically vanishing
tail.  This is the finite statement used before continuity from above. -/
theorem three_packet_stopping_geometric_tail
    (remaining : ℕ → ℝ) (initial : ℝ)
    (hzero : remaining 0 ≤ initial)
    (hstep : ∀ k, remaining (k + 1) ≤ remaining k / 2) :
    ∀ L, remaining L ≤ ((1 : ℝ) / 2) ^ L * initial := by
  intro L
  induction L with
  | zero => simpa using hzero
  | succ L ih =>
      calc
        remaining (L + 1) ≤ remaining L / 2 := hstep L
        _ ≤ ((((1 : ℝ) / 2) ^ L) * initial) / 2 := by linarith
        _ = ((1 : ℝ) / 2) ^ (L + 1) * initial := by
          rw [pow_succ]
          ring

/-- Iterating the predetermined cap contraction never selects a child: the
same bound holds simultaneously on every branch of the return tree. -/
theorem deterministic_cap_contraction_iterate
    (capRadius : ℕ → ℝ) (T₀ B : ℝ)
    (hB : 0 < B)
    (hzero : capRadius 0 ≤ T₀)
    (hstep : ∀ k, capRadius (k + 1) ≤ capRadius k / B) :
    ∀ L, capRadius L ≤ T₀ / B ^ L := by
  intro L
  induction L with
  | zero => simpa using hzero
  | succ L ih =>
      calc
        capRadius (L + 1) ≤ capRadius L / B := hstep L
        _ ≤ (T₀ / B ^ L) / B := (div_le_div_iff_of_pos_right hB).2 ih
        _ = T₀ / B ^ (L + 1) := by
          rw [pow_succ]
          field_simp

/-- Terminal fractional source marginals add before the cap-square weight is
applied.  Hence a common terminal cap-radius bound pays the whole family with
coefficient one, independently of the number of terminal nodes. -/
theorem terminal_cap_square_sum
    {n : ℕ} (terminalMass capRadius : Fin n → ENNReal)
    (rootMass maxRadius : ENNReal)
    (hmass : ∑ i, terminalMass i ≤ rootMass)
    (hradius : ∀ i, capRadius i ≤ maxRadius) :
    (∑ i, terminalMass i * (capRadius i) ^ 3) ≤
      rootMass * maxRadius ^ 3 := by
  calc
    (∑ i, terminalMass i * (capRadius i) ^ 3) ≤
        ∑ i, terminalMass i * maxRadius ^ 3 := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hradius i
    _ = (∑ i, terminalMass i) * maxRadius ^ 3 := by
      rw [Finset.sum_mul]
    _ ≤ rootMass * maxRadius ^ 3 := by
      gcongr

/-- Once deterministic saturation reaches
`maxRadius ^ 3 ≤ rootMass * gain`, the complete terminal cap-square family is
at the quadratic root-mass target. -/
theorem terminal_cap_square_quadratic
    {n : ℕ} (terminalMass capRadius : Fin n → ENNReal)
    (rootMass maxRadius gain : ENNReal)
    (hmass : ∑ i, terminalMass i ≤ rootMass)
    (hradius : ∀ i, capRadius i ≤ maxRadius)
    (hsaturation : maxRadius ^ 3 ≤ rootMass * gain) :
    (∑ i, terminalMass i * (capRadius i) ^ 3) ≤
      rootMass ^ 2 * gain := by
  calc
    (∑ i, terminalMass i * (capRadius i) ^ 3) ≤
        rootMass * maxRadius ^ 3 :=
      terminal_cap_square_sum terminalMass capRadius rootMass maxRadius
        hmass hradius
    _ ≤ rootMass * (rootMass * gain) := by
      gcongr
    _ = rootMass ^ 2 * gain := by ring

/-- In the deterministic saturation branch, conservation is used once at
each depth.  If every node error is at most `loss` times its incoming mass
and the incoming masses at each depth sum to at most the root mass, then the
whole finite-depth tail costs only `L * loss` times the root mass. -/
theorem deterministic_saturation_tail_accumulation
    {L n : ℕ} (nodeMass errorMass : Fin L → Fin n → ℝ)
    (rootMass loss : ℝ)
    (hloss : 0 ≤ loss)
    (hlevel : ∀ ℓ, ∑ i, nodeMass ℓ i ≤ rootMass)
    (herror : ∀ ℓ i, errorMass ℓ i ≤ loss * nodeMass ℓ i) :
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤
      (L : ℝ) * loss * rootMass := by
  calc
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤
        ∑ ℓ, ∑ i, loss * nodeMass ℓ i :=
      Finset.sum_le_sum fun ℓ _ =>
        Finset.sum_le_sum fun i _ => herror ℓ i
    _ = ∑ ℓ, loss * ∑ i, nodeMass ℓ i := by
      apply Finset.sum_congr rfl
      intro ℓ _
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ _ℓ : Fin L, loss * rootMass :=
      Finset.sum_le_sum fun ℓ _ =>
        mul_le_mul_of_nonneg_left (hlevel ℓ) hloss
    _ = (L : ℝ) * loss * rootMass := by simp; ring

/-- Extended-nonnegative version of the finite-depth tail ledger used by the
certificate capacities.  Absolute node errors accumulate linearly in depth,
not exponentially in the number of routing pieces. -/
theorem deterministic_saturation_tail_accumulation_ennreal
    {L n : ℕ} (nodeMass errorMass : Fin L → Fin n → ENNReal)
    (rootMass loss : ENNReal)
    (hlevel : ∀ ℓ, ∑ i, nodeMass ℓ i ≤ rootMass)
    (herror : ∀ ℓ i, errorMass ℓ i ≤ loss * nodeMass ℓ i) :
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤
      (L : ENNReal) * loss * rootMass := by
  calc
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤
        ∑ ℓ, ∑ i, loss * nodeMass ℓ i :=
      Finset.sum_le_sum fun ℓ _ =>
        Finset.sum_le_sum fun i _ => herror ℓ i
    _ = ∑ ℓ, loss * ∑ i, nodeMass ℓ i := by
      apply Finset.sum_congr rfl
      intro ℓ _
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ _ℓ : Fin L, loss * rootMass :=
      Finset.sum_le_sum fun ℓ _ => mul_le_mul_right (hlevel ℓ) loss
    _ = (L : ENNReal) * loss * rootMass := by simp; ring

theorem deterministic_saturation_tail_absorption_ennreal
    {L n : ℕ} (nodeMass errorMass : Fin L → Fin n → ENNReal)
    (rootMass loss budget : ENNReal)
    (hlevel : ∀ ℓ, ∑ i, nodeMass ℓ i ≤ rootMass)
    (herror : ∀ ℓ i, errorMass ℓ i ≤ loss * nodeMass ℓ i)
    (hbudget : (L : ENNReal) * loss ≤ budget) :
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤ budget * rootMass := by
  calc
    (∑ ℓ, ∑ i, errorMass ℓ i) ≤
        (L : ENNReal) * loss * rootMass :=
      deterministic_saturation_tail_accumulation_ennreal
        nodeMass errorMass rootMass loss hlevel herror
    _ ≤ budget * rootMass := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_right hbudget rootMass)

/-- Choosing the finite-depth reserve so that twice `L * loss` is at most one
produces exactly the `smallError` field of the approximate certificate. -/
theorem deterministic_saturation_tail_is_half_root
    {L n : ℕ} (nodeMass errorMass : Fin L → Fin n → ENNReal)
    (rootMass loss : ENNReal)
    (hlevel : ∀ ℓ, ∑ i, nodeMass ℓ i ≤ rootMass)
    (herror : ∀ ℓ i, errorMass ℓ i ≤ loss * nodeMass ℓ i)
    (hreserve :
      (L : ENNReal) * loss + (L : ENNReal) * loss ≤ 1) :
    (∑ ℓ, ∑ i, errorMass ℓ i) +
        (∑ ℓ, ∑ i, errorMass ℓ i) ≤ rootMass := by
  have htail :
      (∑ ℓ, ∑ i, errorMass ℓ i) ≤
        (L : ENNReal) * loss * rootMass :=
    deterministic_saturation_tail_accumulation_ennreal
      nodeMass errorMass rootMass loss hlevel herror
  calc
    (∑ ℓ, ∑ i, errorMass ℓ i) +
          (∑ ℓ, ∑ i, errorMass ℓ i) ≤
        ((L : ENNReal) * loss * rootMass) +
          ((L : ENNReal) * loss * rootMass) := add_le_add htail htail
    _ = ((L : ENNReal) * loss + (L : ENNReal) * loss) * rootMass := by
      rw [add_mul]
    _ ≤ 1 * rootMass := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_right hreserve rootMass)
    _ = rootMass := one_mul rootMass

/-- Substituting a lossless secondary routing of an aggregate cross-cap graph
into the node ledger preserves absolute occurrence with coefficient one.
Only the paid part is terminal; rerouted child flow continues and the new
tail is added to the root-relative error. -/
theorem aggregate_cross_rerouting_identity
    (incoming paid rawCross childFlow errorMass
      crossPaid crossChild crossError : ENNReal)
    (hnode :
      incoming = paid + rawCross + childFlow + errorMass)
    (hcross :
      rawCross = crossPaid + crossChild + crossError) :
    incoming =
      (paid + crossPaid) + (childFlow + crossChild) +
        (errorMass + crossError) := by
  rw [hnode, hcross]
  ac_rfl

/-- Assemble a finite contact--symplectic certificate from the nodewise
conservative routing and its local capacity ledger.  No separate exhaustion
axiom is needed: finiteness of the root source mass and the level-decreasing
carrier forest make conservation telescope exactly. -/
theorem contactSymplecticEdgeFlowCertificate_of_conservative_capacity
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming paid terminalMass capacity : Fin n → ENNReal)
    (hconservation : ∀ i,
      incoming i = paid i + terminalMass i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0))
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0))
    (hlocalCharge : ∀ i,
      paid i + terminalMass i ≤ capacity i * volume (sourceUnion R))
    (hcapacityCarleson : Finset.univ.sum capacity ≤
      A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  exact ⟨{
    incoming := incoming
    paid := paid
    terminalMass := terminalMass
    routingError := fun _ => 0
    capacity := capacity
    conservation := by
      intro i
      simpa [add_assoc] using hconservation i
    sourceAtRoots := hsourceAtRoots
    smallError := by simp
    localCharge := hlocalCharge
    capacityCarleson := hcapacityCarleson }⟩

/-- Record the degree/time-packet tail as a genuine routing error.  It is
small relative to the total root flow and is not charged locally to the
physical union. -/
theorem contactSymplecticEdgeFlowCertificate_of_conservative_capacity_with_error
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming paid terminalMass errorMass capacity : Fin n → ENNReal)
    (hconservation : ∀ i,
      incoming i = paid i + terminalMass i + errorMass i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0))
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0))
    (hsmallError :
      Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
        Finset.univ.sum (fun i : Fin n =>
          if R.tree.parent i = none then incoming i else 0))
    (hlocalCharge : ∀ i,
      paid i + terminalMass i ≤ capacity i * volume (sourceUnion R))
    (hcapacityCarleson : Finset.univ.sum capacity ≤
      A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  exact ⟨{
    incoming := incoming
    paid := paid
    terminalMass := terminalMass
    routingError := errorMass
    capacity := capacity
    conservation := hconservation
    sourceAtRoots := hsourceAtRoots
    smallError := hsmallError
    localCharge := hlocalCharge
    capacityCarleson := hcapacityCarleson }⟩

/-- Direct formal readback of the absolute-occurrence identity.  Cross-cap
flow is terminal, genuine child occurrences continue down the carrier forest,
and the root-relative degree/time-packet tail is kept as routing error. -/
theorem contactSymplecticEdgeFlowCertificate_of_absolute_occurrence_routing
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming paid cross errorMass capacity : Fin n → ENNReal)
    (hoccurrence : ∀ i,
      incoming i = paid i + cross i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0) + errorMass i)
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0))
    (hsmallError :
      Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
        Finset.univ.sum (fun i : Fin n =>
          if R.tree.parent i = none then incoming i else 0))
    (hlocalCharge : ∀ i,
      paid i + cross i ≤ capacity i * volume (sourceUnion R))
    (hcapacityCarleson : Finset.univ.sum capacity ≤
      A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  apply contactSymplecticEdgeFlowCertificate_of_conservative_capacity_with_error
    D R ε A incoming paid cross errorMass capacity
  · intro i
    simpa [add_assoc, add_comm, add_left_comm] using hoccurrence i
  · exact hsourceAtRoots
  · exact hsmallError
  · exact hlocalCharge
  · exact hcapacityCarleson

/-- Assemble the local charge from finitely many geometric destination
ledgers.  Each contact/Maslov output is estimated separately; their capacities
are added only after the absolute occurrence partition, so no destination is
selected and no incoming mass is squared. -/
theorem contactSymplecticEdgeFlowCertificate_of_category_ledgers
    {n k : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming cross errorMass crossCapacity : Fin n → ENNReal)
    (paidPiece paidCapacity : Fin k → Fin n → ENNReal)
    (hoccurrence : ∀ i,
      incoming i = (∑ c, paidPiece c i) + cross i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0) + errorMass i)
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0))
    (hsmallError :
      Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
        Finset.univ.sum (fun i : Fin n =>
          if R.tree.parent i = none then incoming i else 0))
    (hpaidLocal : ∀ c i,
      paidPiece c i ≤ paidCapacity c i * volume (sourceUnion R))
    (hcrossLocal : ∀ i,
      cross i ≤ crossCapacity i * volume (sourceUnion R))
    (hcapacityCarleson :
      Finset.univ.sum (fun i : Fin n =>
        (∑ c, paidCapacity c i) + crossCapacity i) ≤
        A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  apply contactSymplecticEdgeFlowCertificate_of_absolute_occurrence_routing
    D R ε A incoming (fun i => ∑ c, paidPiece c i) cross errorMass
      (fun i => (∑ c, paidCapacity c i) + crossCapacity i)
  · exact hoccurrence
  · exact hsourceAtRoots
  · exact hsmallError
  · intro i
    have hpaid :
        (∑ c, paidPiece c i) ≤
          (∑ c, paidCapacity c i) * volume (sourceUnion R) := by
      calc
        (∑ c, paidPiece c i) ≤
            ∑ c, paidCapacity c i * volume (sourceUnion R) :=
          Finset.sum_le_sum fun c _ => hpaidLocal c i
        _ = (∑ c, paidCapacity c i) * volume (sourceUnion R) := by
          rw [Finset.sum_mul]
    calc
      (∑ c, paidPiece c i) + cross i ≤
          (∑ c, paidCapacity c i) * volume (sourceUnion R) +
            crossCapacity i * volume (sourceUnion R) :=
        add_le_add hpaid (hcrossLocal i)
      _ = ((∑ c, paidCapacity c i) + crossCapacity i) *
          volume (sourceUnion R) := by
        rw [add_mul]
  · exact hcapacityCarleson

/-- Finite Fubini for the category capacities.  Separate global budgets for
the contact/Maslov destinations and cross-cap flow add with coefficient one. -/
theorem category_capacity_carleson_of_separate_budgets
    {n k : ℕ} (paidCapacity : Fin k → Fin n → ENNReal)
    (crossCapacity : Fin n → ENNReal)
    (paidBudget : Fin k → ENNReal) (crossBudget : ENNReal)
    (hpaidBudget : ∀ c, ∑ i, paidCapacity c i ≤ paidBudget c)
    (hcrossBudget : ∑ i, crossCapacity i ≤ crossBudget) :
    Finset.univ.sum (fun i : Fin n =>
      (∑ c, paidCapacity c i) + crossCapacity i) ≤
      (∑ c, paidBudget c) + crossBudget := by
  calc
    Finset.univ.sum (fun i : Fin n =>
        (∑ c, paidCapacity c i) + crossCapacity i) =
        (∑ c, ∑ i, paidCapacity c i) + (∑ i, crossCapacity i) := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    _ ≤ (∑ c, paidBudget c) + crossBudget :=
      add_le_add (Finset.sum_le_sum fun c _ => hpaidBudget c) hcrossBudget

/-- Certificate assembly with one explicit Carleson budget per geometric
destination.  This is the interface used by the separate polarized ledgers. -/
theorem contactSymplecticEdgeFlowCertificate_of_separate_category_budgets
    {n k : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming cross errorMass crossCapacity : Fin n → ENNReal)
    (paidPiece paidCapacity : Fin k → Fin n → ENNReal)
    (paidBudget : Fin k → ENNReal) (crossBudget : ENNReal)
    (hoccurrence : ∀ i,
      incoming i = (∑ c, paidPiece c i) + cross i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0) + errorMass i)
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0))
    (hsmallError :
      Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
        Finset.univ.sum (fun i : Fin n =>
          if R.tree.parent i = none then incoming i else 0))
    (hpaidLocal : ∀ c i,
      paidPiece c i ≤ paidCapacity c i * volume (sourceUnion R))
    (hcrossLocal : ∀ i,
      cross i ≤ crossCapacity i * volume (sourceUnion R))
    (hpaidBudget : ∀ c, ∑ i, paidCapacity c i ≤ paidBudget c)
    (hcrossBudget : ∑ i, crossCapacity i ≤ crossBudget)
    (htotalBudget : (∑ c, paidBudget c) + crossBudget ≤
      A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  apply contactSymplecticEdgeFlowCertificate_of_category_ledgers
    D R ε A incoming cross errorMass crossCapacity
      paidPiece paidCapacity hoccurrence hsourceAtRoots hsmallError
      hpaidLocal hcrossLocal
  exact (category_capacity_carleson_of_separate_budgets
    paidCapacity crossCapacity paidBudget crossBudget
      hpaidBudget hcrossBudget).trans htotalBudget

/-- A category ledger is collision-faithful when every paid, cross-cap, and
error occurrence is obtained by partitioning the actual row-normalized
weighted shading-intersection kernel.  Zero-collision rows are recorded
separately and may only enter the paid ledger through their direct physical
union payment.  These identities rule out manufacturing an unrelated flow
that merely happens to satisfy the abstract carrier recurrence. -/
def IsCollisionFaithfulCategoryLedger {n k : ℕ}
    (R : FiniteScaleSource n)
    (paidPiece : Fin k → Fin n → ENNReal)
    (cross errorMass : Fin n → ENNReal) : Prop :=
  ∃ zeroPiece : Fin k → Fin n → ENNReal,
  ∃ paidCollision : Fin k → Fin n → Fin n → ENNReal,
  ∃ crossCollision errorCollision : Fin n → Fin n → ENNReal,
    (∀ i j, sourceNormalizedCollisionFlow R i j =
      (∑ c, paidCollision c i j) + crossCollision i j + errorCollision i j) ∧
    (∀ i, sourceZeroCollisionRowPiece R i = ∑ c, zeroPiece c i) ∧
    (∀ c i, paidPiece c i = zeroPiece c i + ∑ j, paidCollision c i j) ∧
    (∀ i, cross i = ∑ j, crossCollision i j) ∧
    ∀ i, errorMass i = ∑ j, errorCollision i j

/-- Read back one collision-faithful ledger row.  Its complete terminal mass
is exactly the original weighted source row: the zero-degree part is paid
directly, while every positive-degree part is the genuine normalized
collision flow. -/
theorem collisionFaithfulCategoryLedger_terminal_eq_sourceRowMass
    {n k : ℕ} {D R : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    {paidPiece : Fin k → Fin n → ENNReal}
    {cross errorMass : Fin n → ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D)
    (hledger : IsCollisionFaithfulCategoryLedger R paidPiece cross errorMass)
    (i : Fin n) :
    (∑ c, paidPiece c i) + cross i + errorMass i = sourceRowMass R i := by
  rcases hledger with
    ⟨zeroPiece, paidCollision, crossCollision, errorCollision,
      hpartition, hzero, hpaid, hcross, herror⟩
  have hcombined :
      (∑ j, ((∑ c, paidCollision c i j) + crossCollision i j +
        errorCollision i j)) =
      (∑ j, ∑ c, paidCollision c i j) +
        (∑ j, crossCollision i j) + (∑ j, errorCollision i j) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc
    (∑ c, paidPiece c i) + cross i + errorMass i =
        (∑ c, (zeroPiece c i + ∑ j, paidCollision c i j)) +
          (∑ j, crossCollision i j) + (∑ j, errorCollision i j) := by
      simp_rw [hpaid, hcross, herror]
    _ = (∑ c, zeroPiece c i) +
        ((∑ c, ∑ j, paidCollision c i j) +
          (∑ j, crossCollision i j) + (∑ j, errorCollision i j)) := by
      rw [Finset.sum_add_distrib]
      ac_rfl
    _ = (∑ c, zeroPiece c i) +
        ((∑ j, ∑ c, paidCollision c i j) +
          (∑ j, crossCollision i j) + (∑ j, errorCollision i j)) := by
      rw [Finset.sum_comm]
    _ = (∑ c, zeroPiece c i) +
        ∑ j, ((∑ c, paidCollision c i j) + crossCollision i j +
          errorCollision i j) := by
      rw [hcombined]
    _ = sourceZeroCollisionRowPiece R i +
        ∑ j, sourceNormalizedCollisionFlow R i j := by
      rw [hzero i]
      apply congrArg (fun z => (∑ c, zeroPiece c i) + z)
      apply Finset.sum_congr rfl
      intro j hj
      exact (hpartition i j).symm
    _ = sourceRowMass R i :=
      (sourceRowMass_eq_zeroCollisionRowPiece_add_normalizedCollisionFlow_of_fractional_admissible
        hD hR i).symm

/-- Uniform absolute-occurrence routing data, before it is packaged as a
`ContactSymplecticEdgeFlowCertificate`.  The paid categories retain the
separate contact/Maslov destination ledgers from the manuscript; cross-cap
flow is terminal, and `errorMass` is the root-relative degree/time-packet
tail.  Crucially, the same `A` and `δ₀` work for every finite carrier tree and
every fractional source restriction. -/
def HasAbsoluteOccurrenceCategoryRouting
    (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ Cpack : ENNReal, Cpack ≠ 0 → Cpack ≠ ⊤ →
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (n : ℕ) (D R : FiniteScaleSource n),
      D.thickness ≤ δ₀ →
      ComesFromSelector D selector →
      IsAdmissibleStickySource D (ε / 10) Cpack →
      IsFractionalSourceRestriction R D →
      ∃ k : ℕ,
      ∃ incoming cross errorMass crossCapacity : Fin n → ENNReal,
      ∃ paidPiece paidCapacity : Fin k → Fin n → ENNReal,
      ∃ paidBudget : Fin k → ENNReal,
      ∃ crossBudget : ENNReal,
        (∀ i,
          incoming i = (∑ c, paidPiece c i) + cross i +
            Finset.univ.sum (fun j : Fin n =>
              if R.tree.parent j = some i then incoming j else 0) +
            errorMass i) ∧
        sourceMass R =
          Finset.univ.sum (fun i : Fin n =>
            if R.tree.parent i = none then incoming i else 0) ∧
        Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
          Finset.univ.sum (fun i : Fin n =>
            if R.tree.parent i = none then incoming i else 0) ∧
        (∀ c i,
          paidPiece c i ≤ paidCapacity c i * volume (sourceUnion R)) ∧
        (∀ i,
          cross i ≤ crossCapacity i * volume (sourceUnion R)) ∧
        (∀ c, ∑ i, paidCapacity c i ≤ paidBudget c) ∧
        (∑ i, crossCapacity i) ≤ crossBudget ∧
        (∑ c, paidBudget c) + crossBudget ≤
          A * (ENNReal.ofReal D.thickness).rpow (-ε)

/-- The honest geometric routing interface.  It contains the same uniform,
source-hereditary capacity statement as `HasAbsoluteOccurrenceCategoryRouting`,
but additionally requires the terminal category ledger to be a literal
partition of `sourceNormalizedCollisionFlow`, with the zero-degree rows paid
only through `sourceZeroCollisionRowPiece`. -/
def HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting
    (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ Cpack : ENNReal, Cpack ≠ 0 → Cpack ≠ ⊤ →
    ∃ A : ENNReal, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (n : ℕ) (D R : FiniteScaleSource n),
      D.thickness ≤ δ₀ →
      ComesFromSelector D selector →
      IsAdmissibleStickySource D (ε / 10) Cpack →
      IsFractionalSourceRestriction R D →
      ∃ k : ℕ,
      ∃ incoming cross errorMass crossCapacity : Fin n → ENNReal,
      ∃ paidPiece paidCapacity : Fin k → Fin n → ENNReal,
      ∃ paidBudget : Fin k → ENNReal,
      ∃ crossBudget : ENNReal,
        (∀ i,
          incoming i = (∑ c, paidPiece c i) + cross i +
            Finset.univ.sum (fun j : Fin n =>
              if R.tree.parent j = some i then incoming j else 0) +
            errorMass i) ∧
        (∀ i, incoming i ≠ ⊤) ∧
        Finset.univ.sum errorMass + Finset.univ.sum errorMass ≤
          Finset.univ.sum (fun i : Fin n =>
            if R.tree.parent i = none then incoming i else 0) ∧
        (∀ c i,
          paidPiece c i ≤ paidCapacity c i * volume (sourceUnion R)) ∧
        (∀ i,
          cross i ≤ crossCapacity i * volume (sourceUnion R)) ∧
        (∀ c, ∑ i, paidCapacity c i ≤ paidBudget c) ∧
        (∑ i, crossCapacity i) ≤ crossBudget ∧
        (∑ c, paidBudget c) + crossBudget ≤
          A * (ENNReal.ofReal D.thickness).rpow (-ε) ∧
        IsCollisionFaithfulCategoryLedger R paidPiece cross errorMass

/-- Forgetting only the pair-level collision partition recovers the previous
abstract routing interface. -/
theorem hasAbsoluteOccurrenceCategoryRouting_of_collisionFaithful
    (selector : Set MarkedLine)
    (hroute : HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector) :
    HasAbsoluteOccurrenceCategoryRouting selector := by
  intro ε hε Cpack hCpack0 hCpackTop
  obtain ⟨A, hA0, hATop, δ₀, hδ₀, hroute'⟩ :=
    hroute ε hε Cpack hCpack0 hCpackTop
  refine ⟨A, hA0, hATop, δ₀, hδ₀, ?_⟩
  intro n D R hthickness hfrom hadmissible hrestriction
  obtain ⟨k, incoming, cross, errorMass, crossCapacity,
      paidPiece, paidCapacity, paidBudget, crossBudget,
      hoccurrence, hincomingFinite, hsmallError, hpaidLocal,
      hcrossLocal, hpaidBudget, hcrossBudget, htotalBudget, hfaithful⟩ :=
    hroute' n D R hthickness hfrom hadmissible hrestriction
  let terminal : Fin n → ENNReal :=
    fun i => (∑ c, paidPiece c i) + cross i
  have hconservation : ∀ i,
      incoming i = terminal i + errorMass i +
        Finset.univ.sum (fun j : Fin n =>
          if R.tree.parent j = some i then incoming j else 0) := by
    intro i
    rw [hoccurrence i]
    dsimp [terminal]
    ac_rfl
  have hrootsFinite :
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hroot : R.tree.parent i = none
    · simp [hroot, hincomingFinite i]
    · simp [hroot]
  have hrootTelescope :=
    lossless_edge_flow_exact_of_roots_ne_top R.tree incoming terminal errorMass
      hconservation hrootsFinite
  have hterminal : ∀ i,
      terminal i + errorMass i = sourceRowMass R i := by
    intro i
    simpa [terminal, add_assoc] using
      (collisionFaithfulCategoryLedger_terminal_eq_sourceRowMass
        hadmissible hrestriction hfaithful i)
  have hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n =>
        if R.tree.parent i = none then incoming i else 0) := by
    calc
      sourceMass R = ∑ i, sourceRowMass R i := by
        simpa [sourceRowMass] using
          sourceMass_eq_sum_weight_mul_volume R hrestriction.2.2.2.2.1
      _ = ∑ i, (terminal i + errorMass i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hterminal i).symm
      _ = Finset.univ.sum (fun i : Fin n =>
          if R.tree.parent i = none then incoming i else 0) :=
        hrootTelescope.symm
  exact ⟨k, incoming, cross, errorMass, crossCapacity,
    paidPiece, paidCapacity, paidBudget, crossBudget,
    hoccurrence, hsourceAtRoots, hsmallError, hpaidLocal,
    hcrossLocal, hpaidBudget, hcrossBudget, htotalBudget⟩

/-- The absolute-occurrence routing interface already implies the complete
uniform certificate branch.  This is the formal coefficient-one passage from
the manuscript's separate paid/cross-cap ledgers to the source-hereditary
finite certificate; no geometric estimate is inserted here. -/
theorem hasContactSymplecticEdgeFlowCertificates_of_absoluteOccurrenceCategoryRouting
    (selector : Set MarkedLine)
    (hroute : HasAbsoluteOccurrenceCategoryRouting selector) :
    HasContactSymplecticEdgeFlowCertificates selector := by
  intro ε hε Cpack hCpack0 hCpackTop
  obtain ⟨A, hA0, hATop, δ₀, hδ₀, hroute'⟩ :=
    hroute ε hε Cpack hCpack0 hCpackTop
  refine ⟨A, hA0, hATop, δ₀, hδ₀, ?_⟩
  intro n D R hthickness hfrom hadmissible hrestriction
  obtain ⟨k, incoming, cross, errorMass, crossCapacity,
      paidPiece, paidCapacity, paidBudget, crossBudget,
      hoccurrence, hsourceAtRoots, hsmallError, hpaidLocal,
      hcrossLocal, hpaidBudget, hcrossBudget, htotalBudget⟩ :=
    hroute' n D R hthickness hfrom hadmissible hrestriction
  exact
    contactSymplecticEdgeFlowCertificate_of_separate_category_budgets
      D R ε A incoming cross errorMass crossCapacity paidPiece paidCapacity
      paidBudget crossBudget hoccurrence hsourceAtRoots hsmallError
      hpaidLocal hcrossLocal hpaidBudget hcrossBudget htotalBudget

/-- Collision-faithful routing therefore supplies the complete uniform
contact--symplectic certificate branch. -/
theorem hasContactSymplecticEdgeFlowCertificates_of_collisionFaithfulRouting
    (selector : Set MarkedLine)
    (hroute : HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector) :
    HasContactSymplecticEdgeFlowCertificates selector :=
  hasContactSymplecticEdgeFlowCertificates_of_absoluteOccurrenceCategoryRouting
    selector
    (hasAbsoluteOccurrenceCategoryRouting_of_collisionFaithful selector hroute)

/-- Direction--fibre parameter space used by the vector-Frostman stopping
alternative.  The affine fibre coordinate is retained, so this is a marked
front parameter space rather than an unmarked direction space. -/
abbrev FrontParameterSpace :=
  {theta : E4 // ‖theta‖ = 1} ×
    Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- Output of the mass-conserving vector-Frostman stopping procedure before
pushforward to physical space.  The estimate is required for preimages of
every physical ball, which is exactly what survives collisions under the
front parametrization. -/
def HasMassConservingVectorFrostmanEscape
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 4 →
    ∃ ν : Measure FrontParameterSpace,
      IsProbabilityMeasure ν ∧
      ∃ C : ENNReal, C ≠ ⊤ ∧
        ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
          ν ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r) ≤
            C * (ENNReal.ofReal r).rpow (4 - ε)

/-- Push a parameter-space vector-Frostman escape measure to physical space.
Support is asserted on a compact ambient front, not on the possibly
non-Borel image of the selector itself.  This is the precise place where
compactness removes the descriptive-set-theoretic gap: `unitFront ambient`
is measurable, so `Measure.map_apply` is available on its complement. -/
theorem hasFrontFrostmanMeasures_of_massConservingVectorFrostmanEscape
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hescape : HasMassConservingVectorFrostmanEscape selector
      hmeasurable hvalid hselector) :
    HasFrontFrostmanMeasures ambient := by
  intro ε hε hε4
  obtain ⟨ν, hνprob, C, hCtop, hball⟩ := hescape ε hε hε4
  let f : FrontParameterSpace → E4 :=
    frontParametrization selector hmeasurable hvalid hselector
  let μ : Measure E4 := Measure.map f ν
  have hf : Measurable f :=
    measurable_frontParametrization selector hmeasurable hvalid hselector
  have hμprob : IsProbabilityMeasure μ := by
    letI : IsProbabilityMeasure ν := hνprob
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  have hambientFront : MeasurableSet (unitFront ambient) :=
    (StickyKakeya4.IsCompact.unitFront hambientCompact).measurableSet
  have hpreimage : f ⁻¹' (unitFront ambient)ᶜ = ∅ := by
    ext z
    constructor
    · intro hz
      have hzSelector : f z ∈ unitFront selector := by
        rw [← range_frontParametrization selector hmeasurable hvalid hselector]
        exact ⟨z, rfl⟩
      rcases hzSelector with ⟨line, hline, t, ht, hpoint⟩
      exact (hz ⟨line, hselectorAmbient hline, t, ht, hpoint⟩).elim
    · simp
  refine ⟨μ, hμprob, ?_, C, hCtop, ?_⟩
  · rw [Measure.map_apply hf hambientFront.compl, hpreimage]
    exact measure_empty
  · intro x r hr hr1
    rw [Measure.map_apply hf Metric.isOpen_ball.measurableSet]
    exact hball x r hr hr1

/-- The honest third output of the contact--symplectic stopping tree.  This
is positive boundary data, rather than merely the conjunction of two
negations: besides failure of uniform absolute-occurrence routing, it records
one exponent below four at which every probability law on the marked
direction--fibre space and every finite Frostman coefficient has a violating
physical ball.  The affine fibre coordinate is retained in the preimage.

In the manuscript these witnesses are the coherent concentration packets
whose compatible infinite-depth limit is the fresh-failure boundary measure.
They must not be relabelled as a local capacity or as a Frostman measure. -/
def HasCoherentConcentrationBoundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) : Prop :=
  ¬ HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector ∧
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
    ∀ nu : Measure FrontParameterSpace,
      IsProbabilityMeasure nu →
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
              Metric.ball x r)

/-- Failure of both successful stopping outcomes produces the positive
coherent-concentration boundary certificate.  Classical logic is isolated
here; all consumers of the boundary receive the exponent and violating balls
as explicit data. -/
theorem coherentConcentrationBoundary_of_failures
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hroute : ¬ HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector)
    (hescape : ¬ HasMassConservingVectorFrostmanEscape selector
      hmeasurable hvalid hselector) :
    HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector := by
  refine ⟨hroute, ?_⟩
  rw [HasMassConservingVectorFrostmanEscape] at hescape
  push Not at hescape
  exact hescape

/-- The positive boundary packet rules out the global vector-Frostman escape.
Thus the new data-bearing formulation is logically as strong as the former
negative branch, while exposing the datum actually used by WZ pruning. -/
theorem coherentConcentrationBoundary_not_massConservingVectorFrostmanEscape
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ¬ HasMassConservingVectorFrostmanEscape selector
      hmeasurable hvalid hselector := by
  intro hescape
  obtain ⟨epsilon, hepsilon, hepsilonFour, hpacket⟩ := hboundary.2
  obtain ⟨nu, hnu, C, hCtop, hbound⟩ :=
    hescape epsilon hepsilon hepsilonFour
  obtain ⟨x, r, hr, hrOne, hviolate⟩ := hpacket nu hnu C hCtop
  exact (not_lt_of_ge (hbound x r hr hrOne)) hviolate

/-- The boundary branch contains a genuine concentration witness, not merely
a name for the complement of the two successful branches.  Negating the
mass-conserving vector-Frostman alternative selects one exponent below four;
for every probability law on the marked direction--fibre parameter space and
every finite candidate Frostman constant, some physical ball violates that
bound.  The affine fibre coordinate is retained in the preimage throughout.

This is the first data-bearing input to the cover-adapted WZ readback: later
pruning may specialize `nu` to the canonical marked law and use the returned
ball as the active concentration packet. -/
theorem coherentConcentrationBoundary_extracts_failed_frostman_scale
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ nu : Measure FrontParameterSpace,
        IsProbabilityMeasure nu →
        ∀ C : ENNReal, C ≠ ⊤ →
          ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
            C * (ENNReal.ofReal r).rpow (4 - epsilon) <
              nu ((frontParametrization selector hmeasurable hvalid hselector) ⁻¹'
                Metric.ball x r) := by
  exact hboundary.2

/-- Specialize the failed-Frostman boundary witness to the canonical marked
direction--fibre probability and read it in physical space.  This produces an
actual high-mass front ball, which is the positive concentration datum used by
the cover-adapted finite source construction. -/
theorem coherentConcentrationBoundary_extracts_selectorFrontProbability_ball
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hboundary : HasCoherentConcentrationBoundary selector
      hmeasurable hvalid hselector) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 4 ∧
      ∀ C : ENNReal, C ≠ ⊤ →
        ∃ (x : E4) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
          C * (ENNReal.ofReal r).rpow (4 - epsilon) <
            (selectorFrontProbability selector hmeasurable hvalid hselector :
              Measure E4) (Metric.ball x r) := by
  obtain ⟨epsilon, hepsilon, hepsilonFour, hfail⟩ :=
    coherentConcentrationBoundary_extracts_failed_frostman_scale
      selector hmeasurable hvalid hselector hboundary
  refine ⟨epsilon, hepsilon, hepsilonFour, ?_⟩
  intro C hCtop
  obtain ⟨x, r, hr, hrOne, hlarge⟩ :=
    hfail (frontParameterProbability : Measure FrontParameterSpace)
      (by infer_instance) C hCtop
  refine ⟨x, r, hr, hrOne, ?_⟩
  rw [selectorFrontProbability, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply
      (measurable_frontParametrization selector hmeasurable hvalid hselector)
      Metric.isOpen_ball.measurableSet]
  exact hlarge

/-- Logical terminal split after all finite contact/Maslov routing has been
packaged.  The non-routing branch is tested for the global vector-Frostman
escape; if that test also fails, the coherent-concentration boundary remains
explicit.  This is the trichotomy stated in the corrected manuscript. -/
theorem collisionFaithfulRouting_or_massConservingVectorFrostmanEscape_or_boundary
    (selector : Set MarkedLine)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector) :
    HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector ∨
      HasMassConservingVectorFrostmanEscape selector
        hmeasurable hvalid hselector ∨
      HasCoherentConcentrationBoundary selector
        hmeasurable hvalid hselector := by
  by_cases hroute : HasCollisionFaithfulAbsoluteOccurrenceCategoryRouting selector
  · exact Or.inl hroute
  · by_cases hescape : HasMassConservingVectorFrostmanEscape selector
        hmeasurable hvalid hselector
    · exact Or.inr (Or.inl hescape)
    · exact Or.inr (Or.inr
        (coherentConcentrationBoundary_of_failures selector hmeasurable
          hvalid hselector hroute hescape))

/--
The geometric core has two honest terminal outcomes.  Dense/tangential
stopping, the physical Lagrangian bush, two-copy Maslov routing, and strict
progress either construct lossless certificates for every admissible retained
source, or the mass-conserving vector-Frostman escape directly constructs
front Frostman measures.  The latter is not declared to be a local capacity.
-/
theorem contact_symplectic_edge_flow_certificate_or_front_frostman_or_boundary
    (ambient selector : Set MarkedLine)
    (hambientCompact : IsCompact ambient)
    (hselectorAmbient : selector ⊆ ambient)
    (hmeasurable : MeasurableSet selector)
    (hvalid : ∀ line ∈ selector, IsValidLine line)
    (hselector : IsDirectionSelector selector)
    (hpacking : packingDim (lineCarrier selector) = 3) :
    HasContactSymplecticEdgeFlowCertificates selector ∨
      HasFrontFrostmanMeasures ambient ∨
      HasCoherentConcentrationBoundary selector
        hmeasurable hvalid hselector := by
  rcases
      collisionFaithfulRouting_or_massConservingVectorFrostmanEscape_or_boundary
        selector hmeasurable hvalid hselector with hroute | hescape | hboundary
  · exact Or.inl
      (hasContactSymplecticEdgeFlowCertificates_of_collisionFaithfulRouting
        selector hroute)
  · exact Or.inr (Or.inl
      (hasFrontFrostmanMeasures_of_massConservingVectorFrostmanEscape
      ambient selector hambientCompact hselectorAmbient hmeasurable hvalid hselector
      hescape))
  · exact Or.inr (Or.inr hboundary)

end StickyKakeya4
