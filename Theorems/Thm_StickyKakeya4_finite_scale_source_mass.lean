import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_compact_front
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory Set

namespace StickyKakeya4

/-- The canonical one-level carrier tree for a finite family of actual marked
lines.  Every node is a root and its carrier cell is the singleton containing
that line's unmarked carrier. -/
def oneLevelCarrierTree {n : ℕ} (line : Fin n → MarkedLine) :
    NestedCarrierTree n where
  parent := fun _ => none
  level := fun _ => 0
  parent_level := by simp
  carrierCell := fun i => {(direction (line i), offset (line i))}
  nested := by simp

noncomputable def normalizedPartitionWeight (C : ENNReal) (delta : ℝ) (q : ENNReal) :
    ENNReal :=
  q / (C * (ENNReal.ofReal delta) ^ 3)

theorem normalizedPartitionWeight_le_one
    {C q : ENNReal} {delta : ℝ}
    (hdenZero : C * (ENNReal.ofReal delta) ^ 3 ≠ 0)
    (hdenTop : C * (ENNReal.ofReal delta) ^ 3 ≠ ⊤)
    (hq : q ≤ C * (ENNReal.ofReal delta) ^ 3) :
    normalizedPartitionWeight C delta q ≤ 1 := by
  unfold normalizedPartitionWeight
  rw [ENNReal.div_le_iff hdenZero hdenTop]
  simpa using hq

theorem sum_normalizedPartitionWeight {n : ℕ}
    (C : ENNReal) (delta : ℝ) (q : Fin n → ENNReal)
    (hq : ∑ i, q i = 1) :
    ∑ i, normalizedPartitionWeight C delta (q i) =
      (C * (ENNReal.ofReal delta) ^ 3)⁻¹ := by
  unfold normalizedPartitionWeight
  simp only [div_eq_mul_inv]
  calc
    (∑ i, q i * (C * (ENNReal.ofReal delta) ^ 3)⁻¹) =
        (∑ i, q i) * (C * (ENNReal.ofReal delta) ^ 3)⁻¹ :=
      (Finset.sum_mul Finset.univ q
        (C * (ENNReal.ofReal delta) ^ 3)⁻¹).symm
    _ = (C * (ENNReal.ofReal delta) ^ 3)⁻¹ := by rw [hq, one_mul]

theorem sum_active_normalizedPartitionWeight {n : ℕ}
    (C : ENNReal) (delta : ℝ) (q : Fin n → ENNReal)
    (active : Set (Fin n)) [DecidablePred (fun i => i ∈ active)] :
    (∑ i, if i ∈ active then normalizedPartitionWeight C delta (q i) else 0) =
      (∑ i, if i ∈ active then q i else 0) /
        (C * (ENNReal.ofReal delta) ^ 3) := by
  classical
  unfold normalizedPartitionWeight
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hiactive : i ∈ active <;> simp [hiactive]

theorem inv_mul_scaled_cancel (C scale a : ENNReal)
    (hCZero : C ≠ 0) (hCTop : C ≠ ⊤)
    (hscaleZero : scale ≠ 0) (hscaleTop : scale ≠ ⊤) :
    (C * scale)⁻¹ * (a * scale) = C⁻¹ * a := by
  rw [ENNReal.mul_inv (Or.inl hCZero) (Or.inl hCTop)]
  calc
    (C⁻¹ * scale⁻¹) * (a * scale) =
        (C⁻¹ * a) * (scale⁻¹ * scale) := by ac_rfl
    _ = C⁻¹ * a := by
      rw [ENNReal.inv_mul_cancel hscaleZero hscaleTop, mul_one]

theorem sum_normalizedPartitionWeight_le_ratio {n : ℕ}
    (C : ENNReal) (delta : ℝ) (q : Fin n → ENNReal)
    (indices : Finset (Fin n)) (radiusMass : ENNReal)
    (hCZero : C ≠ 0) (hCTop : C ≠ ⊤) (hdelta : 0 < delta)
    (hmass : ∑ i ∈ indices, q i ≤ C * radiusMass) :
    ∑ i ∈ indices, normalizedPartitionWeight C delta (q i) ≤
      radiusMass / (ENNReal.ofReal delta) ^ 3 := by
  let scale : ENNReal := (ENNReal.ofReal delta) ^ 3
  have hscaleZero : scale ≠ 0 :=
    pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hscaleTop : scale ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hdenZero : C * scale ≠ 0 := mul_ne_zero hCZero hscaleZero
  have hdenTop : C * scale ≠ ⊤ := ENNReal.mul_ne_top hCTop hscaleTop
  have hsum :
      ∑ i ∈ indices, normalizedPartitionWeight C delta (q i) =
        (∑ i ∈ indices, q i) / (C * scale) := by
    unfold normalizedPartitionWeight
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul indices]
  rw [hsum, ENNReal.div_le_iff hdenZero hdenTop]
  calc
    ∑ i ∈ indices, q i ≤ C * radiusMass := hmass
    _ = (radiusMass / scale) * (C * scale) := by
      rw [div_eq_mul_inv]
      calc
        C * radiusMass = (radiusMass * C) * (scale⁻¹ * scale) := by
          rw [ENNReal.inv_mul_cancel hscaleZero hscaleTop, mul_one, mul_comm]
        _ = (radiusMass * scale⁻¹) * (C * scale) := by ac_rfl

/-- The full-tube finite source associated with a finite injective family of
marked lines and cell masses. -/
noncomputable def fullMarkedTubeSource {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) : FiniteScaleSource n where
  thickness := delta
  line := line
  line_injective := hline
  shading := fun i => markedUnitTube (line i) delta
  weight := fun i => normalizedPartitionWeight C delta (q i)
  fibreMark := fun i => mark (line i)
  tree := oneLevelCarrierTree line
  line_in_carrier := by simp [oneLevelCarrierTree]

/-- Keep the full source weight on selected cells but retain only the part of
each selected tube inside one physical closed ball.  This is the local
readback restriction used in the Frostman estimate. -/
noncomputable def activeBallRestriction {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (active : Set (Fin n)) (x : E4) (radius : ℝ) :
    FiniteScaleSource n := by
  classical
  exact
    { thickness := delta
      line := line
      line_injective := hline
      shading := fun i => if i ∈ active then
        markedUnitTube (line i) delta ∩ Metric.closedBall x radius else ∅
      weight := fun i => if i ∈ active then
        normalizedPartitionWeight C delta (q i) else 0
      fibreMark := fun i => mark (line i)
      tree := oneLevelCarrierTree line
      line_in_carrier := by simp [oneLevelCarrierTree] }

theorem activeBallRestriction_isFractionalSourceRestriction {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (active : Set (Fin n)) (x : E4) (radius : ℝ) :
    IsFractionalSourceRestriction
      (activeBallRestriction delta line hline q C active x radius)
      (fullMarkedTubeSource delta line hline q C) := by
  classical
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ active
    · simp only [activeBallRestriction, hi, if_true]
      exact (measurableSet_markedUnitTube (line i) delta).inter
        Metric.isClosed_closedBall.measurableSet
    · simp [activeBallRestriction, hi]
  · intro i
    by_cases hi : i ∈ active <;>
      simp [activeBallRestriction, fullMarkedTubeSource, hi]
  · intro i
    by_cases hi : i ∈ active <;>
      simp [activeBallRestriction, fullMarkedTubeSource, hi]

theorem sourceUnion_activeBallRestriction_subset {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (active : Set (Fin n)) (x : E4) (radius : ℝ) :
    sourceUnion (activeBallRestriction delta line hline q C active x radius) ⊆
      Metric.closedBall x radius := by
  classical
  intro y hy
  by_contra hyball
  have hzero :
      sourceFunction
        (activeBallRestriction delta line hline q C active x radius) y = 0 := by
    unfold sourceFunction
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hiactive : i ∈ active <;>
      simp [activeBallRestriction, hiactive, hyball]
  change 0 < sourceFunction
    (activeBallRestriction delta line hline q C active x radius) y at hy
  rw [hzero] at hy
  exact (lt_irrefl 0 hy)

@[simp] theorem fullMarkedTubeSource_thickness {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) :
    (fullMarkedTubeSource delta line hline q C).thickness = delta := rfl

@[simp] theorem fullMarkedTubeSource_line {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (i : Fin n) :
    (fullMarkedTubeSource delta line hline q C).line i = line i := rfl

@[simp] theorem fullMarkedTubeSource_shading {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (i : Fin n) :
    (fullMarkedTubeSource delta line hline q C).shading i =
      markedUnitTube (line i) delta := rfl

@[simp] theorem fullMarkedTubeSource_weight {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (i : Fin n) :
    (fullMarkedTubeSource delta line hline q C).weight i =
      normalizedPartitionWeight C delta (q i) := rfl

/-- Measurability of the finite weighted source function follows termwise
from measurability of its shadings. -/
theorem sourceFunction_measurable {n : ℕ} (D : FiniteScaleSource n)
    (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    Measurable (sourceFunction D) := by
  unfold sourceFunction
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (hmeas i) measurable_const measurable_const

/-- The positive support of a finite measurable source is measurable. -/
theorem sourceUnion_measurable {n : ℕ} (D : FiniteScaleSource n)
    (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    MeasurableSet (sourceUnion D) := by
  unfold sourceUnion
  exact measurableSet_lt measurable_const
    (sourceFunction_measurable D hmeas)

/-- Quadratic multiplicity energy of a finite weighted source.  This is the
quantity whose off-diagonal part is routed through the contact--symplectic
collision ledger. -/
noncomputable def sourceEnergy {n : ℕ} (D : FiniteScaleSource n) : ENNReal :=
  ∫⁻ x, sourceFunction D x * sourceFunction D x ∂volume

/-- Source-level Cauchy--Schwarz in its division-free extended-real form.  It
is the analytic bridge from failure of the physical-union estimate to large
quadratic collision energy. -/
theorem sourceMass_le_sqrt_energy_mul_sqrt_union {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    sourceMass D ≤
      (sourceEnergy D).rpow (1 / 2 : ℝ) *
        (volume (sourceUnion D)).rpow (1 / 2 : ℝ) := by
  let f : E4 → ENNReal := sourceFunction D
  let g : E4 → ENNReal :=
    (sourceUnion D).indicator (fun _ => (1 : ENNReal))
  have hf : Measurable f := sourceFunction_measurable D hmeas
  have hU : MeasurableSet (sourceUnion D) := sourceUnion_measurable D hmeas
  have hg : Measurable g := Measurable.indicator measurable_const hU
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    hf.aemeasurable hg.aemeasurable
  have hfg : (fun x => (f * g) x) = f := by
    funext x
    by_cases hx : x ∈ sourceUnion D
    · simp [g, hx]
    · have hzero : f x = 0 := by
        apply le_antisymm
        · exact not_lt.mp (by simpa [f, sourceUnion] using hx)
        · exact bot_le
      simp [g, hx, hzero]
  rw [hfg] at hholder
  have hg_sq : (∫⁻ x, g x * g x ∂volume) = volume (sourceUnion D) := by
    have hpoint : (fun x => g x * g x) =
        (sourceUnion D).indicator (fun _ => (1 : ENNReal)) := by
      funext x
      by_cases hx : x ∈ sourceUnion D <;> simp [g, hx]
    rw [hpoint]
    simpa only [one_mul] using
      (MeasureTheory.lintegral_indicator_const
        (μ := volume) hU (1 : ENNReal))
  simp_rw [ENNReal.rpow_two, pow_two] at hholder
  rw [hg_sq] at hholder
  simpa [sourceMass, sourceEnergy, f] using hholder

private theorem ennreal_sqrt_sq (x : ENNReal) :
    (x.rpow (1 / 2 : ℝ)) ^ 2 = x := by
  calc
    (x.rpow (1 / 2 : ℝ)) ^ 2 =
        (x.rpow (1 / 2 : ℝ)).rpow (2 : ℝ) :=
      (ENNReal.rpow_natCast (x.rpow (1 / 2 : ℝ)) 2).symm
    _ = x.rpow ((1 / 2 : ℝ) * 2) :=
      (ENNReal.rpow_mul x (1 / 2 : ℝ) 2).symm
    _ = x := by norm_num

/-- Squared Cauchy--Schwarz in the exact form consumed by the initial
incidence reduction. -/
theorem sourceMass_sq_le_union_mul_energy {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    (sourceMass D) ^ 2 ≤ volume (sourceUnion D) * sourceEnergy D := by
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union D hmeas
  calc
    (sourceMass D) ^ 2 ≤
        ((sourceEnergy D).rpow (1 / 2 : ℝ) *
          (volume (sourceUnion D)).rpow (1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left' hholder 2
    _ = sourceEnergy D * volume (sourceUnion D) := by
      rw [mul_pow, ennreal_sqrt_sq, ennreal_sqrt_sq]
    _ = volume (sourceUnion D) * sourceEnergy D := mul_comm _ _

/-- The contribution of the ordered pair `(i,j)` to the quadratic source
energy. -/
noncomputable def sourcePairMass {n : ℕ} (D : FiniteScaleSource n)
    (i j : Fin n) : ENNReal :=
  (D.weight i * D.weight j) * volume (D.shading i ∩ D.shading j)

/-- The diagonal part of the ordered-pair expansion of `sourceEnergy`. -/
noncomputable def sourceDiagonalMass {n : ℕ}
    (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, ∑ j, if i = j then sourcePairMass D i j else 0

/-- The off-diagonal collision part of the ordered-pair expansion of
`sourceEnergy`. -/
noncomputable def sourceOffDiagonalMass {n : ℕ}
    (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, ∑ j, if i = j then 0 else sourcePairMass D i j

/-- Linear mass carried by one source row before collision normalization. -/
noncomputable def sourceRowMass {n : ℕ} (D : FiniteScaleSource n)
    (i : Fin n) : ENNReal :=
  D.weight i * volume (D.shading i)

/-- Raw off-diagonal collision degree of one source row. -/
noncomputable def sourceOffDiagonalRowMass {n : ℕ}
    (D : FiniteScaleSource n) (i : Fin n) : ENNReal :=
  ∑ j, if i = j then 0 else sourcePairMass D i j

theorem sourceOffDiagonalMass_eq_sum_rowMass {n : ℕ}
    (D : FiniteScaleSource n) :
    sourceOffDiagonalMass D = ∑ i, sourceOffDiagonalRowMass D i := by
  rfl

/-- Row-normalized collision flow.  A zero collision row sends no flow; a
positive row distributes its complete linear row mass over all genuine
off-diagonal collision partners. -/
noncomputable def sourceNormalizedCollisionFlow {n : ℕ}
    (D : FiniteScaleSource n) (i j : Fin n) : ENNReal :=
  if sourceOffDiagonalRowMass D i = 0 then 0 else
    sourceRowMass D i *
      ((if i = j then 0 else sourcePairMass D i j) /
        sourceOffDiagonalRowMass D i)

/-- Exact Markov row identity for every finite nonzero collision row. -/
theorem sourceNormalizedCollisionFlow_row_sum {n : ℕ}
    (D : FiniteScaleSource n) (i : Fin n)
    (hrow0 : sourceOffDiagonalRowMass D i ≠ 0)
    (hrowTop : sourceOffDiagonalRowMass D i ≠ ⊤) :
    ∑ j, sourceNormalizedCollisionFlow D i j = sourceRowMass D i := by
  simp only [sourceNormalizedCollisionFlow, hrow0, if_false]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv]
  have hsum :
      (∑ j : Fin n,
        (if i = j then 0 else sourcePairMass D i j) *
          (sourceOffDiagonalRowMass D i)⁻¹) =
        (∑ j : Fin n, if i = j then 0 else sourcePairMass D i j) *
          (sourceOffDiagonalRowMass D i)⁻¹ := by
    simpa using
      (Finset.sum_mul Finset.univ
        (fun j : Fin n => if i = j then 0 else sourcePairMass D i j)
        (sourceOffDiagonalRowMass D i)⁻¹).symm
  rw [hsum]
  change sourceRowMass D i *
      (sourceOffDiagonalRowMass D i * (sourceOffDiagonalRowMass D i)⁻¹) =
    sourceRowMass D i
  rw [ENNReal.mul_inv_cancel hrow0 hrowTop, mul_one]

/-- Total linear mass of the positive collision rows. -/
noncomputable def sourcePositiveCollisionRowMass {n : ℕ}
    (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, if sourceOffDiagonalRowMass D i = 0 then 0 else sourceRowMass D i

/-- Linear source mass on rows with zero off-diagonal collision degree. -/
noncomputable def sourceZeroCollisionRowPiece {n : ℕ}
    (D : FiniteScaleSource n) (i : Fin n) : ENNReal :=
  if sourceOffDiagonalRowMass D i = 0 then sourceRowMass D i else 0

/-- Linear source mass on rows with zero off-diagonal collision degree. -/
noncomputable def sourceZeroCollisionRowMass {n : ℕ}
    (D : FiniteScaleSource n) : ENNReal :=
  ∑ i, sourceZeroCollisionRowPiece D i

/-- Every finite row is the disjoint sum of its direct zero-collision payment
and its genuine row-normalized collision destinations.  This is the exact
source-level input needed by the contact/Maslov category ledger: no auxiliary
flow can be substituted for the actual weighted shading intersections. -/
theorem sourceRowMass_eq_zeroCollisionRowPiece_add_normalizedCollisionFlow
    {n : ℕ} (D : FiniteScaleSource n) (i : Fin n)
    (hrowTop : sourceOffDiagonalRowMass D i ≠ ⊤) :
    sourceRowMass D i = sourceZeroCollisionRowPiece D i +
      ∑ j, sourceNormalizedCollisionFlow D i j := by
  by_cases hrow0 : sourceOffDiagonalRowMass D i = 0
  · simp [sourceZeroCollisionRowPiece, sourceNormalizedCollisionFlow, hrow0]
  · rw [sourceNormalizedCollisionFlow_row_sum D i hrow0 hrowTop]
    simp [sourceZeroCollisionRowPiece, hrow0]

/-- Summing all normalized collision destinations preserves exactly the mass
of the positive-degree rows. -/
theorem sourceNormalizedCollisionFlow_total {n : ℕ}
    (D : FiniteScaleSource n)
    (hrowTop : ∀ i, sourceOffDiagonalRowMass D i ≠ ⊤) :
    (∑ i, ∑ j, sourceNormalizedCollisionFlow D i j) =
      sourcePositiveCollisionRowMass D := by
  unfold sourcePositiveCollisionRowMass
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hrow0 : sourceOffDiagonalRowMass D i = 0
  · simp [sourceNormalizedCollisionFlow, hrow0]
  · rw [sourceNormalizedCollisionFlow_row_sum D i hrow0 (hrowTop i)]
    simp [hrow0]

/-- A zero row has zero raw pair mass against every genuinely different
index. -/
theorem sourcePairMass_eq_zero_of_offDiagonalRowMass_eq_zero {n : ℕ}
    (D : FiniteScaleSource n) {i j : Fin n}
    (hrow : sourceOffDiagonalRowMass D i = 0) (hij : i ≠ j) :
    sourcePairMass D i j = 0 := by
  have hzeroFun :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun _ : Fin n => (bot_le : (0 : ENNReal) ≤ _))).mp hrow
  have hterm := congrFun hzeroFun j
  simpa [sourceOffDiagonalRowMass, hij] using hterm

/-- Exact finite Fubini expansion of the quadratic source energy into weighted
pairwise shading intersections.  No disjointness or geometric estimate is used
here. -/
theorem sourceEnergy_eq_pair_sum {n : ℕ} (D : FiniteScaleSource n)
    (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    sourceEnergy D =
      ∑ i, ∑ j, (D.weight i * D.weight j) *
        volume (D.shading i ∩ D.shading j) := by
  classical
  unfold sourceEnergy sourceFunction
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [← MeasureTheory.lintegral_indicator_const
        (μ := volume) ((hmeas i).inter (hmeas j))
        (D.weight i * D.weight j)]
      congr 1
      funext x
      by_cases hxi : x ∈ D.shading i <;>
        by_cases hxj : x ∈ D.shading j <;>
          simp [hxi, hxj, mul_comm]
    · intro j _
      exact Measurable.mul
        (Measurable.ite (hmeas i) measurable_const measurable_const)
        (Measurable.ite (hmeas j) measurable_const measurable_const)
  · intro i _
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.mul
        (Measurable.ite (hmeas i) measurable_const measurable_const)
        (Measurable.ite (hmeas j) measurable_const measurable_const)

/-- The quadratic energy is exactly diagonal mass plus off-diagonal collision
mass. -/
theorem sourceEnergy_eq_diagonal_add_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    sourceEnergy D = sourceDiagonalMass D + sourceOffDiagonalMass D := by
  rw [sourceEnergy_eq_pair_sum D hmeas]
  unfold sourceDiagonalMass sourceOffDiagonalMass
  simp_rw [sourcePairMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [hij]

/-- Readback of the diagonal pair sum as the expected weighted self-overlap. -/
theorem sourceDiagonalMass_eq {n : ℕ} (D : FiniteScaleSource n) :
    sourceDiagonalMass D =
      ∑ i, D.weight i * D.weight i * volume (D.shading i) := by
  classical
  unfold sourceDiagonalMass sourcePairMass
  simp

/-- The mass of a finite measurable weighted source is the sum of its
individual weighted shading volumes.  This identity is valid without any
disjointness assumption and is the normalization used when probability cells
are rescaled by the transverse tube volume. -/
theorem sourceMass_eq_sum_weight_mul_volume {n : ℕ} (D : FiniteScaleSource n)
    (hmeas : ∀ i, @MeasurableSet E4
      (MeasureSpace.toMeasurableSpace : MeasurableSpace E4)
      (D.shading i)) :
    sourceMass D = ∑ i, D.weight i * volume (D.shading i) := by
  classical
  unfold sourceMass sourceFunction
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [Set.indicator_apply] using
      (MeasureTheory.lintegral_indicator_const (μ := volume)
        (hmeas i) (D.weight i))
  · intro i _
    exact Measurable.ite (hmeas i) measurable_const measurable_const

/-- For admissible weights, every self-collision is paid by the corresponding
linear source mass.  Thus any excess quadratic energy is genuinely
off-diagonal. -/
theorem sourceDiagonalMass_le_sourceMass {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) :
    sourceDiagonalMass D ≤ sourceMass D := by
  rw [sourceDiagonalMass_eq, sourceMass_eq_sum_weight_mul_volume D hmeas]
  apply Finset.sum_le_sum
  intro i _
  calc
    D.weight i * D.weight i * volume (D.shading i) ≤
        D.weight i * 1 * volume (D.shading i) := by
      gcongr
      exact hweight i
    _ = D.weight i * volume (D.shading i) := by simp

/-- The usable collision-energy inequality: the linear mass pays the diagonal,
so only the off-diagonal pair intersections remain for the geometric routing
argument. -/
theorem sourceEnergy_le_sourceMass_add_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) :
    sourceEnergy D ≤ sourceMass D + sourceOffDiagonalMass D := by
  rw [sourceEnergy_eq_diagonal_add_offDiagonal D hmeas]
  gcongr
  exact sourceDiagonalMass_le_sourceMass D hmeas hweight

/-- Once Cauchy--Schwarz (together with a failed union estimate) has amplified
the quadratic energy by a factor at least two, the off-diagonal collision
ledger alone carries one full copy of the source mass. -/
theorem amplified_sourceEnergy_forces_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) (B : ENNReal)
    (hB : 2 ≤ B) (hmassTop : sourceMass D ≠ ⊤)
    (henergy : B * sourceMass D ≤ sourceEnergy D) :
    sourceMass D ≤ sourceOffDiagonalMass D := by
  have hsum : sourceMass D + sourceMass D ≤
      sourceMass D + sourceOffDiagonalMass D := by
    calc
      sourceMass D + sourceMass D = 2 * sourceMass D := by ring
      _ ≤ B * sourceMass D := by gcongr
      _ ≤ sourceEnergy D := henergy
      _ = sourceDiagonalMass D + sourceOffDiagonalMass D :=
        sourceEnergy_eq_diagonal_add_offDiagonal D hmeas
      _ ≤ sourceMass D + sourceOffDiagonalMass D := by
        gcongr
        exact sourceDiagonalMass_le_sourceMass D hmeas hweight
  exact ENNReal.le_of_add_le_add_left hmassTop hsum

/-- Quantitative form retaining the complete multiplicity gain.  If the
quadratic energy contains `gain + 1` copies of the linear source mass, the
diagonal spends at most one copy and every remaining copy is carried by the
raw off-diagonal collision ledger. -/
theorem amplified_sourceEnergy_forces_scaled_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) (gain : ENNReal)
    (hmassTop : sourceMass D ≠ ⊤)
    (henergy : (gain + 1) * sourceMass D ≤ sourceEnergy D) :
    gain * sourceMass D ≤ sourceOffDiagonalMass D := by
  have hsum :
      sourceMass D + gain * sourceMass D ≤
        sourceMass D + sourceOffDiagonalMass D := by
    calc
      sourceMass D + gain * sourceMass D =
          (gain + 1) * sourceMass D := by ring
      _ ≤ sourceEnergy D := henergy
      _ = sourceDiagonalMass D + sourceOffDiagonalMass D :=
        sourceEnergy_eq_diagonal_add_offDiagonal D hmeas
      _ ≤ sourceMass D + sourceOffDiagonalMass D := by
        gcongr
        exact sourceDiagonalMass_le_sourceMass D hmeas hweight
  exact ENNReal.le_of_add_le_add_left hmassTop hsum

/-- Complete initial incidence reduction for a finite weighted source.  If the
physical union misses the source mass by a factor `B ≥ 2`, then the exact
off-diagonal pair-intersection ledger carries at least one full source mass.
The hypotheses excluding `⊤` are the precise cancellation conditions; they
will be discharged from bounded-tube geometry for admissible sources. -/
theorem union_failure_forces_source_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) (B : ENNReal)
    (hB : 2 ≤ B) (hmass0 : sourceMass D ≠ 0)
    (hmassTop : sourceMass D ≠ ⊤)
    (hunionTop : volume (sourceUnion D) ≠ ⊤)
    (hfailure : B * volume (sourceUnion D) ≤ sourceMass D) :
    sourceMass D ≤ sourceOffDiagonalMass D := by
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union D hmeas
  have hunion0 : volume (sourceUnion D) ≠ 0 := by
    intro hzero
    rw [hzero] at hholder
    simp at hholder
    exact hmass0 hholder
  have hsquare : sourceMass D * sourceMass D ≤
      volume (sourceUnion D) * sourceEnergy D := by
    simpa [pow_two] using sourceMass_sq_le_union_mul_energy D hmeas
  have hscaled : B * volume (sourceUnion D) * sourceMass D ≤
      sourceMass D * sourceMass D := by
    gcongr
  have hcancel : volume (sourceUnion D) * (B * sourceMass D) ≤
      volume (sourceUnion D) * sourceEnergy D := by
    calc
      volume (sourceUnion D) * (B * sourceMass D) =
          B * volume (sourceUnion D) * sourceMass D := by ring
      _ ≤ sourceMass D * sourceMass D := hscaled
      _ ≤ volume (sourceUnion D) * sourceEnergy D := hsquare
  have henergy : B * sourceMass D ≤ sourceEnergy D :=
    (ENNReal.mul_le_mul_iff_right hunion0 hunionTop).mp hcancel
  exact amplified_sourceEnergy_forces_offDiagonal
    D hmeas hweight B hB hmassTop henergy

/-- Quantitative incidence reduction without discarding the high-overlap
gain.  A `(gain + 1)`-fold failure of the physical union estimate leaves
`gain` copies of the source mass in the raw off-diagonal pair energy. -/
theorem scaled_union_failure_forces_source_offDiagonal {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) (gain : ENNReal)
    (hmass0 : sourceMass D ≠ 0)
    (hmassTop : sourceMass D ≠ ⊤)
    (hunionTop : volume (sourceUnion D) ≠ ⊤)
    (hfailure : (gain + 1) * volume (sourceUnion D) ≤ sourceMass D) :
    gain * sourceMass D ≤ sourceOffDiagonalMass D := by
  have hholder := sourceMass_le_sqrt_energy_mul_sqrt_union D hmeas
  have hunion0 : volume (sourceUnion D) ≠ 0 := by
    intro hzero
    rw [hzero] at hholder
    simp at hholder
    exact hmass0 hholder
  have hsquare : sourceMass D * sourceMass D ≤
      volume (sourceUnion D) * sourceEnergy D := by
    simpa [pow_two] using sourceMass_sq_le_union_mul_energy D hmeas
  have hscaled : (gain + 1) * volume (sourceUnion D) * sourceMass D ≤
      sourceMass D * sourceMass D := by
    gcongr
  have hcancel :
      volume (sourceUnion D) * ((gain + 1) * sourceMass D) ≤
        volume (sourceUnion D) * sourceEnergy D := by
    calc
      volume (sourceUnion D) * ((gain + 1) * sourceMass D) =
          (gain + 1) * volume (sourceUnion D) * sourceMass D := by ring
      _ ≤ sourceMass D * sourceMass D := hscaled
      _ ≤ volume (sourceUnion D) * sourceEnergy D := hsquare
  have henergy : (gain + 1) * sourceMass D ≤ sourceEnergy D :=
    (ENNReal.mul_le_mul_iff_right hunion0 hunionTop).mp hcancel
  exact amplified_sourceEnergy_forces_scaled_offDiagonal
    D hmeas hweight gain hmassTop henergy

/-- Uniform per-line tube volume and a bound for the total direction weight
give the root-mass normalization used by the global capacity ledger. -/
theorem sourceMass_le_totalWeight_mul_volumeBound {n : ℕ}
    (D : FiniteScaleSource n) (volumeBound totalWeight : ENNReal)
    (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hvolume : ∀ i, volume (D.shading i) ≤ volumeBound)
    (hweight : ∑ i, D.weight i ≤ totalWeight) :
    sourceMass D ≤ totalWeight * volumeBound := by
  rw [sourceMass_eq_sum_weight_mul_volume D hmeas]
  calc
    (∑ i, D.weight i * volume (D.shading i)) ≤
        ∑ i, D.weight i * volumeBound := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_right (hvolume i) (D.weight i)
    _ = (∑ i, D.weight i) * volumeBound := by
      rw [Finset.sum_mul]
    _ ≤ totalWeight * volumeBound := by
      simpa [mul_comm] using mul_le_mul_right hweight volumeBound

/-- A finite cover of all retained directions converts the local weighted
direction--Carleson bounds into a global total-weight bound.  Overlap of the
cover is harmless because every source index only needs one witnessing ball. -/
theorem totalWeight_le_of_direction_ball_cover {n m : ℕ}
    (D : FiniteScaleSource n) (center : Fin m → E4)
    (r : ℝ) (cap : ENNReal)
    (hcover : ∀ i, ∃ j, dist (direction (D.line i)) (center j) < r)
    (hball : ∀ j,
      directionWeightInBall D (center j) r ≤ cap) :
    (∑ i, D.weight i) ≤ (m : ENNReal) * cap := by
  classical
  calc
    (∑ i, D.weight i) ≤
        ∑ i, ∑ j, if dist (direction (D.line i)) (center j) < r then
          D.weight i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨j, hj⟩ := hcover i
      have hsingle :
          (if dist (direction (D.line i)) (center j) < r then
              D.weight i else 0) ≤
            ∑ j, if dist (direction (D.line i)) (center j) < r then
              D.weight i else 0 := by
        calc
          (if dist (direction (D.line i)) (center j) < r then
              D.weight i else 0) =
              ∑ k : Fin m, if k = j then
                (if dist (direction (D.line i)) (center k) < r then
                  D.weight i else 0) else 0 := by simp
          _ ≤ ∑ k, if dist (direction (D.line i)) (center k) < r then
              D.weight i else 0 := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hkj : k = j
            · simp [hkj]
            · simp [hkj]
      simpa [hj] using hsingle
    _ = ∑ j, directionWeightInBall D (center j) r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      unfold directionWeightInBall
      rfl
    _ ≤ ∑ _j : Fin m, cap :=
      Finset.sum_le_sum fun j _ => hball j
    _ = (m : ENNReal) * cap := by simp

theorem sourceFunction_le_of_fractionalSourceRestriction {n : ℕ}
    {R D : FiniteScaleSource n} (hR : IsFractionalSourceRestriction R D) :
    ∀ x, sourceFunction R x ≤ sourceFunction D x := by
  classical
  intro x
  unfold sourceFunction
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : x ∈ R.shading i
  · have hxD : x ∈ D.shading i := hR.2.2.2.2.2.1 i hx
    simp [hx, hxD, hR.2.2.2.2.2.2 i]
  · simp [hx]

theorem sourceMass_le_of_fractionalSourceRestriction {n : ℕ}
    {R D : FiniteScaleSource n} (hR : IsFractionalSourceRestriction R D) :
    sourceMass R ≤ sourceMass D := by
  unfold sourceMass
  exact lintegral_mono (sourceFunction_le_of_fractionalSourceRestriction hR)

/-- Every shading of an admissible source has finite ambient volume.  The
point is geometric rather than weighted: the shading lies in a bounded closed
neighbourhood of one compact marked unit segment. -/
theorem shading_volume_ne_top_of_admissibleStickySource {n : ℕ}
    {D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C) (i : Fin n) :
    volume (D.shading i) ≠ ⊤ := by
  rcases hD with ⟨hdelta, hdeltaOne, hweight, hmark, hvalid, hmeasurable,
    hvolumeLower, htube, hdirection, hcarrier⟩
  have hfrontNonempty : (unitFront {D.line i}).Nonempty := by
    refine ⟨offset (D.line i) + (mark (D.line i) + 0) • direction (D.line i), ?_⟩
    exact ⟨D.line i, by simp, 0, by norm_num, rfl⟩
  have hfrontCompact : IsCompact (unitFront {D.line i}) :=
    StickyKakeya4.IsCompact.unitFront isCompact_singleton
  have hsubset : D.shading i ⊆
      Metric.cthickening D.thickness (unitFront {D.line i}) := by
    intro x hx
    rw [Metric.mem_cthickening_iff]
    simpa only [Metric.infDist,
        ← ENNReal.le_ofReal_iff_toReal_le
          (Metric.infEDist_ne_top hfrontNonempty) hdelta.le] using
      htube i x hx
  have hbounded : Bornology.IsBounded
      (Metric.cthickening D.thickness (unitFront {D.line i})) :=
    hfrontCompact.isBounded.cthickening
  exact ne_of_lt ((measure_mono hsubset).trans_lt hbounded.measure_lt_top)

/-- Admissibility keeps every shading in a bounded closed neighbourhood of
one compact marked segment.  With finitely many weights bounded by one, the
ambient source mass is therefore finite. -/
theorem sourceMass_ne_top_of_admissibleStickySource {n : ℕ}
    {D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C) : sourceMass D ≠ ⊤ := by
  rcases hD with ⟨hdelta, hdeltaOne, hweight, hmark, hvalid, hmeasurable,
    hvolumeLower, htube, hdirection, hcarrier⟩
  rw [sourceMass_eq_sum_weight_mul_volume D hmeasurable]
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  apply ENNReal.mul_ne_top
  · exact ne_of_lt ((hweight i).trans_lt ENNReal.one_lt_top)
  · exact shading_volume_ne_top_of_admissibleStickySource
      ⟨hdelta, hdeltaOne, hweight, hmark, hvalid, hmeasurable,
        hvolumeLower, htube, hdirection, hcarrier⟩ i

theorem sourceMass_ne_top_of_fractional_admissibleStickySource {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) : sourceMass R ≠ ⊤ := by
  exact ne_of_lt ((sourceMass_le_of_fractionalSourceRestriction hR).trans_lt
    (lt_top_iff_ne_top.mpr (sourceMass_ne_top_of_admissibleStickySource hD)))

/-- The positive support of a finite source is contained in the finite union
of its shadings, independently of any positivity assumption on the weights. -/
theorem sourceUnion_subset_iUnion_shading {n : ℕ}
    (D : FiniteScaleSource n) :
    sourceUnion D ⊆ ⋃ i, D.shading i := by
  classical
  intro x hx
  by_contra hnot
  have houtside : ∀ i, x ∉ D.shading i := by
    intro i hxi
    exact hnot (Set.mem_iUnion.mpr ⟨i, hxi⟩)
  have hzero : sourceFunction D x = 0 := by
    simp [sourceFunction, houtside]
  exact (not_lt_of_ge (bot_le : (0 : ENNReal) ≤ 0)) (by
    simpa [sourceUnion, hzero] using hx)

/-- A shading with positive row weight lies inside the physical source
union. -/
theorem shading_subset_sourceUnion_of_weight_pos {n : ℕ}
    (D : FiniteScaleSource n) (i : Fin n) (hweight : 0 < D.weight i) :
    D.shading i ⊆ sourceUnion D := by
  classical
  intro x hx
  change 0 < sourceFunction D x
  unfold sourceFunction
  calc
    0 < D.weight i := hweight
    _ = if x ∈ D.shading i then D.weight i else 0 := by simp [hx]
    _ ≤ ∑ j, if x ∈ D.shading j then D.weight j else 0 := by
      exact Finset.single_le_sum
        (fun j _ => (bot_le : (0 : ENNReal) ≤
          if x ∈ D.shading j then D.weight j else 0))
        (Finset.mem_univ i)

/-- The measurable shading family supported on zero collision rows with
positive weight. -/
noncomputable def zeroCollisionShading {n : ℕ}
    (D : FiniteScaleSource n) (i : Fin n) : Set E4 :=
  if sourceOffDiagonalRowMass D i = 0 ∧ 0 < D.weight i then
    D.shading i else ∅

theorem measurableSet_zeroCollisionShading {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (i : Fin n) :
    MeasurableSet (zeroCollisionShading D i) := by
  classical
  by_cases hi : sourceOffDiagonalRowMass D i = 0 ∧ 0 < D.weight i
  · simp [zeroCollisionShading, hi, hmeas i]
  · simp [zeroCollisionShading, hi]

/-- Distinct positive-weight zero-collision rows are disjoint modulo volume
null sets. -/
theorem zeroCollisionShading_pairwise_aeDisjoint {n : ℕ}
    (D : FiniteScaleSource n) :
    Pairwise (Function.onFun (AEDisjoint volume) (zeroCollisionShading D)) := by
  classical
  intro i j hij
  by_cases hi : sourceOffDiagonalRowMass D i = 0 ∧ 0 < D.weight i
  · by_cases hj : sourceOffDiagonalRowMass D j = 0 ∧ 0 < D.weight j
    · have hvol : volume (D.shading i ∩ D.shading j) = 0 := by
        have hpair := sourcePairMass_eq_zero_of_offDiagonalRowMass_eq_zero
          D hi.1 hij
        unfold sourcePairMass at hpair
        exact (mul_eq_zero.mp hpair).resolve_left
          (mul_ne_zero (ne_of_gt hi.2) (ne_of_gt hj.2))
      simpa [Function.onFun, zeroCollisionShading, hi, hj, AEDisjoint] using hvol
    · simp [zeroCollisionShading, hi, hj, AEDisjoint]
  · simp [zeroCollisionShading, hi, AEDisjoint]

/-- The zero-collision rows are paid directly by the physical union.  This is
the measure-theoretic form of the zero-degree-row step preceding Markov
normalization. -/
theorem sourceZeroCollisionRowMass_le_volume_sourceUnion {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i))
    (hweight : ∀ i, D.weight i ≤ 1) :
    sourceZeroCollisionRowMass D ≤ volume (sourceUnion D) := by
  classical
  have hterm : ∀ i,
      (if sourceOffDiagonalRowMass D i = 0 then sourceRowMass D i else 0) ≤
        volume (zeroCollisionShading D i) := by
    intro i
    by_cases hrow : sourceOffDiagonalRowMass D i = 0
    · by_cases hweight0 : D.weight i = 0
      · simp [hrow, hweight0, sourceRowMass, zeroCollisionShading]
      · have hweightPos : 0 < D.weight i := bot_lt_iff_ne_bot.mpr hweight0
        simp only [hrow, if_true, zeroCollisionShading, hweightPos, and_self]
        unfold sourceRowMass
        calc
          D.weight i * volume (D.shading i) ≤
              1 * volume (D.shading i) := by
            simpa [mul_comm] using
              mul_le_mul_right (hweight i) (volume (D.shading i))
          _ = volume (D.shading i) := one_mul _
    · simp [hrow, zeroCollisionShading]
  have hzeroLe : sourceZeroCollisionRowMass D ≤
      ∑ i, volume (zeroCollisionShading D i) := by
    unfold sourceZeroCollisionRowMass sourceZeroCollisionRowPiece
    exact Finset.sum_le_sum fun i _ => hterm i
  have hmeasure : volume (⋃ i, zeroCollisionShading D i) =
      ∑ i, volume (zeroCollisionShading D i) := by
    simpa only [tsum_fintype] using
      (measure_iUnion₀ (zeroCollisionShading_pairwise_aeDisjoint D)
        (fun i => (measurableSet_zeroCollisionShading D hmeas i).nullMeasurableSet))
  have hsubset : (⋃ i, zeroCollisionShading D i) ⊆ sourceUnion D := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : sourceOffDiagonalRowMass D i = 0 ∧ 0 < D.weight i
    · exact shading_subset_sourceUnion_of_weight_pos D i hi.2
        (by simpa [zeroCollisionShading, hi] using hxi)
    · simpa [zeroCollisionShading, hi] using hxi
  calc
    sourceZeroCollisionRowMass D ≤
        ∑ i, volume (zeroCollisionShading D i) := hzeroLe
    _ = volume (⋃ i, zeroCollisionShading D i) := hmeasure.symm
    _ ≤ volume (sourceUnion D) := measure_mono hsubset

/-- Exact decomposition of the linear source mass into positive- and
zero-collision rows. -/
theorem sourceMass_eq_positive_add_zeroCollisionRowMass {n : ℕ}
    (D : FiniteScaleSource n) (hmeas : ∀ i, MeasurableSet (D.shading i)) :
    sourceMass D = sourcePositiveCollisionRowMass D +
      sourceZeroCollisionRowMass D := by
  rw [sourceMass_eq_sum_weight_mul_volume D hmeas]
  unfold sourcePositiveCollisionRowMass sourceZeroCollisionRowMass
    sourceZeroCollisionRowPiece sourceRowMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hrow : sourceOffDiagonalRowMass D i = 0 <;> simp [hrow]

/-- The physical union of any fractional restriction of an admissible source
has finite volume.  This discharges the second cancellation condition in the
source-level Cauchy--Schwarz reduction. -/
theorem volume_sourceUnion_ne_top_of_fractional_admissibleStickySource {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) :
    volume (sourceUnion R) ≠ ⊤ := by
  have hshadingTop : ∀ i, volume (R.shading i) ≠ ⊤ := by
    intro i
    exact ne_of_lt ((measure_mono (hR.2.2.2.2.2.1 i)).trans_lt
      (lt_top_iff_ne_top.mpr
        (shading_volume_ne_top_of_admissibleStickySource hD i)))
  have hsumTop : (∑ i, volume (R.shading i)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun i hi => hshadingTop i
  have hunionLe : volume (sourceUnion R) ≤ ∑ i, volume (R.shading i) := by
    exact (measure_mono (sourceUnion_subset_iUnion_shading R)).trans
      (measure_iUnion_fintype_le volume (fun i => R.shading i))
  exact ne_of_lt (hunionLe.trans_lt (lt_top_iff_ne_top.mpr hsumTop))

/-- Every off-diagonal row degree of an admissible fractional restriction is
finite, so the row-normalized contact/Maslov collision kernel is defined
without an extra cancellation hypothesis. -/
theorem sourceOffDiagonalRowMass_ne_top_of_fractional_admissibleStickySource
    {n : ℕ} {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) (i : Fin n) :
    sourceOffDiagonalRowMass R i ≠ ⊤ := by
  have hweightTop : ∀ k, R.weight k ≠ ⊤ := by
    intro k
    exact ne_of_lt (((hR.2.2.2.2.2.2 k).trans (hD.2.2.1 k)).trans_lt
      ENNReal.one_lt_top)
  have hshadingTop : ∀ k, volume (R.shading k) ≠ ⊤ := by
    intro k
    exact ne_of_lt ((measure_mono (hR.2.2.2.2.2.1 k)).trans_lt
      (lt_top_iff_ne_top.mpr
        (shading_volume_ne_top_of_admissibleStickySource hD k)))
  unfold sourceOffDiagonalRowMass
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    unfold sourcePairMass
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (hweightTop i) (hweightTop j)
    · exact ne_of_lt ((measure_mono inter_subset_left).trans_lt
        (lt_top_iff_ne_top.mpr (hshadingTop i)))

/-- The exact zero-row/collision-flow decomposition is available uniformly
for every row of every admissible fractional source restriction. -/
theorem sourceRowMass_eq_zeroCollisionRowPiece_add_normalizedCollisionFlow_of_fractional_admissible
    {n : ℕ} {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) (i : Fin n) :
    sourceRowMass R i = sourceZeroCollisionRowPiece R i +
      ∑ j, sourceNormalizedCollisionFlow R i j := by
  exact sourceRowMass_eq_zeroCollisionRowPiece_add_normalizedCollisionFlow R i
    (sourceOffDiagonalRowMass_ne_top_of_fractional_admissibleStickySource
      hD hR i)

/-- Global exact source decomposition into direct zero-row payments and the
actual normalized collision kernel. -/
theorem sourceMass_eq_sum_zeroCollisionRowPiece_add_normalizedCollisionFlow
    {n : ℕ} {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) :
    sourceMass R = ∑ i, (sourceZeroCollisionRowPiece R i +
      ∑ j, sourceNormalizedCollisionFlow R i j) := by
  rw [sourceMass_eq_sum_weight_mul_volume R hR.2.2.2.2.1]
  change (∑ i, sourceRowMass R i) = _
  apply Finset.sum_congr rfl
  intro i hi
  exact
    sourceRowMass_eq_zeroCollisionRowPiece_add_normalizedCollisionFlow_of_fractional_admissible
      hD hR i

/-- Complete row-normalized collision readback for every admissible
fractional restriction. -/
theorem sourceNormalizedCollisionFlow_total_of_fractional_admissible {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D) :
    (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) =
      sourcePositiveCollisionRowMass R := by
  exact sourceNormalizedCollisionFlow_total R
    (sourceOffDiagonalRowMass_ne_top_of_fractional_admissibleStickySource hD hR)

/-- Under a factor-two union failure, positive collision rows retain at least
half of the complete source mass.  Zero rows have already been paid by the
physical union. -/
theorem factor_two_union_failure_forces_positiveCollisionRowMass {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R) :
    sourceMass R ≤ 2 * sourcePositiveCollisionRowMass R := by
  let positive := sourcePositiveCollisionRowMass R
  let zero := sourceZeroCollisionRowMass R
  have hdecomp : sourceMass R = positive + zero := by
    simpa [positive, zero] using
      sourceMass_eq_positive_add_zeroCollisionRowMass R hR.2.2.2.2.1
  have hzero : zero ≤ volume (sourceUnion R) := by
    simpa [zero] using
      sourceZeroCollisionRowMass_le_volume_sourceUnion R hR.2.2.2.2.1
        (fun i => (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i))
  have hzeroTop : zero ≠ ⊤ := by
    exact ne_of_lt (hzero.trans_lt (lt_top_iff_ne_top.mpr
      (volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR)))
  have hzeroPositive : zero ≤ positive := by
    apply ENNReal.le_of_add_le_add_right hzeroTop
    calc
      zero + zero = 2 * zero := by ring
      _ ≤ 2 * volume (sourceUnion R) := by gcongr
      _ ≤ sourceMass R := hfailure
      _ = positive + zero := hdecomp
  calc
    sourceMass R = positive + zero := hdecomp
    _ ≤ positive + positive := add_le_add le_rfl hzeroPositive
    _ = 2 * sourcePositiveCollisionRowMass R := by
      simp only [positive]
      ring

/-- The normalized contact/Maslov collision destinations carry at least half
of the complete source mass under factor-two union failure. -/
theorem factor_two_union_failure_forces_normalizedCollisionFlow {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D)
    (hfailure : 2 * volume (sourceUnion R) ≤ sourceMass R) :
    sourceMass R ≤
      2 * (∑ i, ∑ j, sourceNormalizedCollisionFlow R i j) := by
  rw [sourceNormalizedCollisionFlow_total_of_fractional_admissible hD hR]
  exact factor_two_union_failure_forces_positiveCollisionRowMass hD hR hfailure

/-- Incidence reduction with all finiteness hypotheses discharged by the
admissible-tube geometry.  It applies uniformly to every fractional source
restriction and preserves all affine fibre marks and carrier data. -/
theorem union_failure_forces_source_offDiagonal_of_fractional_admissible {n : ℕ}
    {R D : FiniteScaleSource n} {ε : ℝ} {C B : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D)
    (hB : 2 ≤ B) (hmass0 : sourceMass R ≠ 0)
    (hfailure : B * volume (sourceUnion R) ≤ sourceMass R) :
    sourceMass R ≤ sourceOffDiagonalMass R := by
  apply union_failure_forces_source_offDiagonal R hR.2.2.2.2.1
  · intro i
    exact (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  · exact hB
  · exact hmass0
  · exact sourceMass_ne_top_of_fractional_admissibleStickySource hD hR
  · exact volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR
  · exact hfailure

/-- Fractional-admissible specialization of the gain-preserving incidence
reduction.  All finiteness hypotheses are discharged by bounded marked-tube
geometry, so the output is ready for the raw collision graph. -/
theorem scaled_union_failure_forces_source_offDiagonal_of_fractional_admissible
    {n : ℕ} {R D : FiniteScaleSource n} {ε : ℝ} {C gain : ENNReal}
    (hD : IsAdmissibleStickySource D ε C)
    (hR : IsFractionalSourceRestriction R D)
    (hmass0 : sourceMass R ≠ 0)
    (hfailure : (gain + 1) * volume (sourceUnion R) ≤ sourceMass R) :
    gain * sourceMass R ≤ sourceOffDiagonalMass R := by
  apply scaled_union_failure_forces_source_offDiagonal R hR.2.2.2.2.1
  · intro i
    exact (hR.2.2.2.2.2.2 i).trans (hD.2.2.1 i)
  · exact hmass0
  · exact sourceMass_ne_top_of_fractional_admissibleStickySource hD hR
  · exact volume_sourceUnion_ne_top_of_fractional_admissibleStickySource hD hR
  · exact hfailure

theorem sourceMass_fullMarkedTubeSource {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) :
    sourceMass (fullMarkedTubeSource delta line hline q C) =
      ∑ i, normalizedPartitionWeight C delta (q i) *
        volume (markedUnitTube (line i) delta) := by
  apply sourceMass_eq_sum_weight_mul_volume
  intro i
  exact measurableSet_markedUnitTube (line i) delta

theorem sum_weight_mul_le_sourceMass_fullMarkedTubeSource {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C L : ENNReal)
    (hvolume : ∀ i, L ≤ volume (markedUnitTube (line i) delta)) :
    (∑ i, normalizedPartitionWeight C delta (q i)) * L ≤
      sourceMass (fullMarkedTubeSource delta line hline q C) := by
  rw [sourceMass_fullMarkedTubeSource, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_right (hvolume i) (normalizedPartitionWeight C delta (q i))

theorem sourceMass_fullMarkedTubeSource_le_sum_weight_mul {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C U : ENNReal)
    (hvolume : ∀ i, volume (markedUnitTube (line i) delta) ≤ U) :
    sourceMass (fullMarkedTubeSource delta line hline q C) ≤
      (∑ i, normalizedPartitionWeight C delta (q i)) * U := by
  rw [sourceMass_fullMarkedTubeSource, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_right (hvolume i) (normalizedPartitionWeight C delta (q i))

theorem sourceMass_fullMarkedTubeSource_normalized_bounds {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C a b : ENNReal) (hCZero : C ≠ 0) (hCTop : C ≠ ⊤)
    (hdelta : 0 < delta) (hq : ∑ i, q i = 1)
    (hlower : ∀ i,
      a * (ENNReal.ofReal delta) ^ 3 ≤
        volume (markedUnitTube (line i) delta))
    (hupper : ∀ i,
      volume (markedUnitTube (line i) delta) ≤
        b * (ENNReal.ofReal delta) ^ 3) :
    C⁻¹ * a ≤ sourceMass (fullMarkedTubeSource delta line hline q C) ∧
      sourceMass (fullMarkedTubeSource delta line hline q C) ≤ C⁻¹ * b := by
  let scale : ENNReal := (ENNReal.ofReal delta) ^ 3
  have hscaleZero : scale ≠ 0 :=
    pow_ne_zero 3 (ENNReal.ofReal_ne_zero_iff.mpr hdelta)
  have hscaleTop : scale ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsum :
      ∑ i, normalizedPartitionWeight C delta (q i) = (C * scale)⁻¹ := by
    simpa [scale] using sum_normalizedPartitionWeight C delta q hq
  constructor
  · calc
      C⁻¹ * a = (C * scale)⁻¹ * (a * scale) :=
        (inv_mul_scaled_cancel C scale a hCZero hCTop hscaleZero hscaleTop).symm
      _ = (∑ i, normalizedPartitionWeight C delta (q i)) *
          (a * scale) := by rw [hsum]
      _ ≤ sourceMass (fullMarkedTubeSource delta line hline q C) := by
        apply sum_weight_mul_le_sourceMass_fullMarkedTubeSource
        intro i
        simpa [scale] using hlower i
  · calc
      sourceMass (fullMarkedTubeSource delta line hline q C) ≤
          (∑ i, normalizedPartitionWeight C delta (q i)) *
            (b * scale) := by
        apply sourceMass_fullMarkedTubeSource_le_sum_weight_mul
        intro i
        simpa [scale] using hupper i
      _ = (C * scale)⁻¹ * (b * scale) := by rw [hsum]
      _ = C⁻¹ * b :=
        inv_mul_scaled_cancel C scale b hCZero hCTop hscaleZero hscaleTop

theorem sourceMass_activeBallRestriction {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (active : Set (Fin n)) [DecidablePred (fun i => i ∈ active)]
    (x : E4) (radius : ℝ) :
    sourceMass (activeBallRestriction delta line hline q C active x radius) =
      ∑ i, if i ∈ active then
        normalizedPartitionWeight C delta (q i) *
          volume (markedUnitTube (line i) delta ∩ Metric.closedBall x radius)
        else 0 := by
  classical
  rw [sourceMass_eq_sum_weight_mul_volume]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hiactive : i ∈ active <;>
      simp [activeBallRestriction, hiactive]
  · intro i
    by_cases hiactive : i ∈ active
    · simp only [activeBallRestriction, hiactive, if_true]
      exact (measurableSet_markedUnitTube (line i) delta).inter
        Metric.isClosed_closedBall.measurableSet
    · simp [activeBallRestriction, hiactive]

theorem active_weight_mul_le_sourceMass_activeBallRestriction {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C L : ENNReal) (active : Set (Fin n)) [DecidablePred (fun i => i ∈ active)]
    (x : E4) (radius : ℝ)
    (hvolume : ∀ i, i ∈ active →
      L ≤ volume (markedUnitTube (line i) delta ∩ Metric.closedBall x radius)) :
    (∑ i, if i ∈ active then normalizedPartitionWeight C delta (q i) else 0) * L ≤
      sourceMass (activeBallRestriction delta line hline q C active x radius) := by
  classical
  rw [sourceMass_activeBallRestriction, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hiactive : i ∈ active
  · simp only [hiactive, if_true]
    exact mul_le_mul_right
      (hvolume i hiactive) (normalizedPartitionWeight C delta (q i))
  · simp [hiactive]

/-- The local four-dimensional ball payment cancels the cubic source
normalization, leaving exactly the one-dimensional fibre factor.  This is the
scale-free algebraic step in the marked local readback estimate. -/
theorem two_delta_mul_active_mass_le_readback_constant_mul_sourceMass {n : ℕ}
    (delta : ℝ) (line : Fin n → MarkedLine)
    (hline : Function.Injective line) (q : Fin n → ENNReal)
    (C : ENNReal) (active : Set (Fin n)) [DecidablePred (fun i => i ∈ active)]
    (x : E4) (hdelta : 0 < delta) (hCZero : C ≠ 0) (hCTop : C ≠ ⊤)
    (hvolume : ∀ i, i ∈ active →
      (ENNReal.ofReal (delta / 4)) ^ 4 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) ≤
        volume (markedUnitTube (line i) delta ∩
          Metric.closedBall x (2 * delta))) :
    ENNReal.ofReal (2 * delta) *
        (∑ i, if i ∈ active then q i else 0) ≤
      (2 * C *
          ((ENNReal.ofReal (1 / 4 : ℝ)) ^ 4 *
            ENNReal.ofReal (Real.pi ^ 2 / 2))⁻¹) *
        sourceMass
          (activeBallRestriction delta line hline q C active x (2 * delta)) := by
  classical
  let scale : ENNReal := (ENNReal.ofReal delta) ^ 3
  let a : ENNReal :=
    (ENNReal.ofReal (1 / 4 : ℝ)) ^ 4 *
      ENNReal.ofReal (Real.pi ^ 2 / 2)
  let Q : ENNReal := ∑ i, if i ∈ active then q i else 0
  have hxZero : ENNReal.ofReal delta ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hxTop : ENNReal.ofReal delta ≠ ⊤ := ENNReal.ofReal_ne_top
  have hscaleZero : scale ≠ 0 := pow_ne_zero 3 hxZero
  have hscaleTop : scale ≠ ⊤ := ENNReal.pow_ne_top hxTop
  have haZero : a ≠ 0 := by
    dsimp [a]
    apply mul_ne_zero
    · exact pow_ne_zero 4 (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num))
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have haTop : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hlocal := active_weight_mul_le_sourceMass_activeBallRestriction
    delta line hline q C
    ((ENNReal.ofReal (delta / 4)) ^ 4 *
      ENNReal.ofReal (Real.pi ^ 2 / 2)) active x (2 * delta) hvolume
  have hhalf : ENNReal.ofReal (delta / 4) =
      ENNReal.ofReal delta * ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [show delta / 4 = delta * (1 / 4 : ℝ) by ring]
    exact ENNReal.ofReal_mul hdelta.le
  have hL :
      (ENNReal.ofReal (delta / 4)) ^ 4 *
          ENNReal.ofReal (Real.pi ^ 2 / 2) =
        (scale * ENNReal.ofReal delta) * a := by
    rw [hhalf, mul_pow]
    simp only [scale, a]
    rw [show (ENNReal.ofReal delta) ^ 4 =
      (ENNReal.ofReal delta) ^ 3 * ENNReal.ofReal delta by ring]
    ring
  have hweights :
      (∑ i, if i ∈ active then normalizedPartitionWeight C delta (q i) else 0) =
        Q / (C * scale) := by
    simpa [Q, scale] using
      sum_active_normalizedPartitionWeight C delta q active
  have hpayment :
      ENNReal.ofReal (2 * delta) * Q =
        (2 * C * a⁻¹) *
          ((Q / (C * scale)) * ((scale * ENNReal.ofReal delta) * a)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    rw [div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hCZero) (Or.inl hCTop)]
    symm
    calc
      (2 * C * a⁻¹) *
          ((Q * (C⁻¹ * scale⁻¹)) *
            ((scale * ENNReal.ofReal delta) * a)) =
        (2 * ENNReal.ofReal delta * Q) *
          (C * C⁻¹) * (scale⁻¹ * scale) * (a⁻¹ * a) := by
            ac_rfl
      _ = 2 * ENNReal.ofReal delta * Q := by
        rw [ENNReal.mul_inv_cancel hCZero hCTop,
          ENNReal.inv_mul_cancel hscaleZero hscaleTop,
          ENNReal.inv_mul_cancel haZero haTop]
        simp
  calc
    ENNReal.ofReal (2 * delta) *
        (∑ i, if i ∈ active then q i else 0) =
      ENNReal.ofReal (2 * delta) * Q := by rfl
    _ = (2 * C * a⁻¹) *
        ((Q / (C * scale)) * ((scale * ENNReal.ofReal delta) * a)) := hpayment
    _ = (2 * C * a⁻¹) *
        ((∑ i, if i ∈ active then
            normalizedPartitionWeight C delta (q i) else 0) *
          ((ENNReal.ofReal (delta / 4)) ^ 4 *
            ENNReal.ofReal (Real.pi ^ 2 / 2))) := by rw [hweights, hL]
    _ ≤ (2 * C * a⁻¹) *
        sourceMass
          (activeBallRestriction delta line hline q C active x (2 * delta)) :=
      mul_le_mul_right hlocal _
    _ = (2 * C *
          ((ENNReal.ofReal (1 / 4 : ℝ)) ^ 4 *
            ENNReal.ofReal (Real.pi ^ 2 / 2))⁻¹) *
        sourceMass
          (activeBallRestriction delta line hline q C active x (2 * delta)) := by
      rfl

end StickyKakeya4
