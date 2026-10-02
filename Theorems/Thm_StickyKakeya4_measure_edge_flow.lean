import Theorems.Thm_StickyKakeya4_lossless_edge_flow_carleson
import Theorems.Thm_StickyKakeya4_global_terminal_band

/-!
Measure-valued finite occurrence flow.

All node measures live on one fixed occurrence space. The only conservation
hypothesis is an equality of measures at every node. Evaluating that equality
and applying the scalar forest ledger yields measure domination, not merely a
bound on total masses. A single measurable endpoint map therefore preserves
the domination. Geometric construction of such a conservative occurrence tree,
and domination of its root endpoint measure by a product measure, remain
separate hypotheses to be established in applications.
-/

open MeasureTheory

namespace StickyKakeya4

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem measure_ite_zero_apply (p : Prop) [Decidable p]
    (μ : Measure Ω) (s : Set Ω) :
    (if p then μ else 0) s = if p then μ s else 0 := by
  split_ifs <;> rfl

/-- A nodewise equality of occurrence measures gives the scalar conservation
identity on every test set. -/
theorem measure_edge_flow_conservation_apply
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (s : Set Ω) :
    ∀ i, incoming i s = paid i s + terminal i s +
      Finset.univ.sum (fun j : Fin n =>
        if T.parent j = some i then incoming j s else 0) := by
  classical
  intro i
  have h := congrArg (fun μ : Measure Ω => μ s) (hconserve i)
  simpa only [Measure.add_apply, Measure.finsetSum_apply, measure_ite_zero_apply] using h

/-- Finite nodewise conservative occurrence flow pays no more than its root
measure, as a measure inequality on the original occurrence space. No finiteness
assumption on the root mass is needed. -/
theorem measure_lossless_edge_flow_carleson
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) :
    Finset.univ.sum (fun i : Fin n => paid i + terminal i) ≤
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  have h := lossless_edge_flow_carleson T
    (fun i => incoming i s) (fun i => paid i s) (fun i => terminal i s)
    (measure_edge_flow_conservation_apply T incoming paid terminal hconserve s)
  simpa only [Measure.finsetSum_apply, Measure.add_apply, measure_ite_zero_apply] using h

/-- Summed terminal occurrence measures are dominated by the summed root
occurrence measures. This is stronger than terminal total-mass accounting. -/
theorem measure_terminal_flow_le_root
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) :
    Finset.univ.sum terminal ≤
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) := by
  classical
  calc
    Finset.univ.sum terminal ≤
        Finset.univ.sum (fun i : Fin n => paid i + terminal i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Measure.le_add_left le_rfl
    _ ≤ _ := measure_lossless_edge_flow_carleson T incoming paid terminal hconserve

/-- Keeping one fixed measurable endpoint map preserves the terminal measure
bound. The map may retain the ordered endpoint pair and any inherited marks;
it must not be replaced by a node-dependent resampling operation. -/
theorem measure_terminal_flow_map_le_root
    {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint) :
    Finset.univ.sum (fun i : Fin n => (terminal i).map endpoint) ≤
      (Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0)).map endpoint := by
  classical
  rw [← Measure.map_finset_sum hendpoint.aemeasurable]
  exact Measure.map_mono
    (measure_terminal_flow_le_root T incoming paid terminal hconserve) hendpoint

/-- A separately proved bound for the root endpoint measure passes to the
summed terminal endpoint measures. In particular the bound can be a product
measure, without assuming any per-terminal marginal-product comparison. -/
theorem measure_terminal_flow_map_le_of_root_le
    {Y : Type*} [MeasurableSpace Y]
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (endpoint : Ω → Y) (hendpoint : Measurable endpoint)
    (rootBound : Measure Y)
    (hroot : (Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0)).map endpoint ≤ rootBound) :
    Finset.univ.sum (fun i : Fin n => (terminal i).map endpoint) ≤ rootBound :=
  (measure_terminal_flow_map_le_root T incoming paid terminal hconserve
    endpoint hendpoint).trans hroot

/-- The finite occurrence-forest ledger combined with the global band estimate.
The terminal measure budget is derived from nodewise conservation rather than
assumed. The root endpoint domination, terminal support, original selector
ball-density bound, and stopping scale are the remaining explicit geometric
inputs. In particular this does not assert that the routing construction
produces those inputs.

The left side is the mass of the original occurrence measures. A single
measurable endpoint map preserves each total mass. -/
theorem measure_forest_terminal_mass_le_quadratic
    {X D : Type*} [MeasurableSpace X]
    [PseudoMetricSpace D] [MeasurableSpace D] [BorelSpace D]
    [SecondCountableTopology D]
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming paid terminal : Fin n → Measure Ω)
    (hconserve : ∀ i,
      incoming i = paid i + terminal i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0))
    (endpoint : Ω → X × X) (hendpoint : Measurable endpoint)
    (σ : Measure X) [SFinite σ]
    {direction : X → D} (hdirection : Measurable direction)
    (C q : ENNReal) {capScale : ℝ} (hscale_nonneg : 0 ≤ capScale)
    (hroot : (Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0)).map endpoint ≤ σ.prod σ)
    (hsupport : ∀ i, (terminal i).map endpoint
      (GlobalTerminalBand.directionBand direction (2 * capScale))ᶜ = 0)
    (hdensity : ∀ a : D, ∀ R : ℝ, 0 ≤ R →
      σ (direction ⁻¹' Metric.closedBall a R) ≤ C * ENNReal.ofReal R ^ 3)
    (hscale : ENNReal.ofReal capScale ^ 3 ≤ σ Set.univ * q) :
    Finset.univ.sum (fun i : Fin n => terminal i Set.univ) ≤
      8 * C * (σ Set.univ) ^ 2 * q := by
  classical
  have hbudget : Measure.sum (fun i : Fin n => (terminal i).map endpoint) ≤
      (Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0)).map endpoint := by
    rw [Measure.sum_fintype]
    exact measure_terminal_flow_map_le_root T incoming paid terminal hconserve
      endpoint hendpoint
  have hbound := GlobalTerminalBand.terminal_mass_le_quadratic σ
    ((Finset.univ.sum (fun i : Fin n =>
      if T.parent i = none then incoming i else 0)).map endpoint)
    (fun i : Fin n => (terminal i).map endpoint)
    hdirection C q hscale_nonneg hbudget hroot hsupport hdensity hscale
  simpa only [tsum_fintype, Measure.map_apply hendpoint MeasurableSet.univ,
    Set.preimage_univ] using hbound

end StickyKakeya4
