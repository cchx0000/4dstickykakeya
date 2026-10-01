import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence

open MeasureTheory

namespace StickyKakeya4

/-- The exact infinite-depth ledger required from the three-packet return
branch.  `levelCapacity k` is the total vector-centre charge at generation
`k`; `capacityDominated` records that every finite-tree capacity is charged
once to those generations.  The genuinely geometric input is the uniform
decay `levelDecay`, not a prepackaged terminal Carleson conclusion. -/
structure ThreePacketReturnCarlesonLedger {n : ℕ}
    (capacity : Fin n → ENNReal) where
  levelCapacity : ℕ → ENNReal
  rootBudget : ENNReal
  ratio : ENNReal
  ratio_lt_one : ratio < 1
  capacityDominated :
    Finset.univ.sum capacity ≤ ∑' k, levelCapacity k
  levelDecay : ∀ k, levelCapacity k ≤ rootBudget * ratio ^ k

/-- Geometric decay of the generation charges closes the weighted Carleson
sum with a constant independent of the depth of the retained carrier tree. -/
theorem ThreePacketReturnCarlesonLedger.capacityCarleson
    {n : ℕ} {capacity : Fin n → ENNReal}
    (ledger : ThreePacketReturnCarlesonLedger capacity) :
    Finset.univ.sum capacity ≤
      ledger.rootBudget * (1 - ledger.ratio)⁻¹ := by
  calc
    Finset.univ.sum capacity ≤ ∑' k, ledger.levelCapacity k :=
      ledger.capacityDominated
    _ ≤ ∑' k, ledger.rootBudget * ledger.ratio ^ k :=
      ENNReal.tsum_le_tsum ledger.levelDecay
    _ = ledger.rootBudget * (1 - ledger.ratio)⁻¹ := by
      simp only [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Iteration of the mass-conserving continuation estimate.  The statement is
in `ENNReal`, so it can be applied directly to generation masses without a
finite-mass coercion or a depth-dependent truncation. -/
theorem ennreal_geometric_remaining_bound
    (remaining : ℕ → ENNReal) (rootBudget ratio : ENNReal)
    (hzero : remaining 0 ≤ rootBudget)
    (hstep : ∀ k, remaining (k + 1) ≤ remaining k * ratio) :
    ∀ k, remaining k ≤ rootBudget * ratio ^ k := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      calc
        remaining (k + 1) ≤ remaining k * ratio := hstep k
        _ ≤ (rootBudget * ratio ^ k) * ratio := by gcongr
        _ = rootBudget * ratio ^ (k + 1) := by
          rw [pow_succ]
          ac_rfl

/-- The exact compensation-zone closure needed after a mass-conserving
three-packet stopping.  `remaining` is the total continuing mass, and each
generation's vector-centre charge is bounded by a fixed multiplier times that
mass.  A strict contraction therefore constructs the existing Carleson ledger
with constants independent of the number of retained carrier-tree levels. -/
theorem threePacketReturnCarlesonLedger_of_mass_conserving_decay
    {n : ℕ} (capacity : Fin n → ENNReal)
    (levelCapacity remaining : ℕ → ENNReal)
    (rootMass chargeMultiplier ratio : ENNReal)
    (hratio : ratio < 1)
    (hcapacity : Finset.univ.sum capacity ≤ ∑' k, levelCapacity k)
    (hremainingZero : remaining 0 ≤ rootMass)
    (hremainingStep : ∀ k,
      remaining (k + 1) ≤ remaining k * ratio)
    (hlevelCharge : ∀ k,
      levelCapacity k ≤ chargeMultiplier * remaining k) :
    Nonempty (ThreePacketReturnCarlesonLedger capacity) := by
  have hremaining : ∀ k,
      remaining k ≤ rootMass * ratio ^ k :=
    ennreal_geometric_remaining_bound remaining rootMass ratio
      hremainingZero hremainingStep
  refine ⟨{
    levelCapacity := levelCapacity
    rootBudget := chargeMultiplier * rootMass
    ratio := ratio
    ratio_lt_one := hratio
    capacityDominated := hcapacity
    levelDecay := ?_ }⟩
  intro k
  calc
    levelCapacity k ≤ chargeMultiplier * remaining k := hlevelCharge k
    _ ≤ chargeMultiplier * (rootMass * ratio ^ k) :=
      by simpa [mul_comm] using
        (mul_le_mul_right (hremaining k) chargeMultiplier)
    _ = (chargeMultiplier * rootMass) * ratio ^ k := by ac_rfl

/-- Conservation plus removal of at least half the current mass forces the
continuing mass to be at most one half.  Finiteness is stated explicitly so
the cancellation is valid in `ENNReal`; in applications it follows from the
finite root source mass. -/
theorem ennreal_half_removal_forces_half_continuation
    (current removed continuing : ENNReal)
    (hcurrentFinite : current ≠ ⊤)
    (hconservation : current = removed + continuing)
    (hhalfRemoved : current ≤ removed + removed) :
    continuing ≤ current * (2 : ENNReal)⁻¹ := by
  have hremovedLe : removed ≤ current := by
    rw [hconservation]
    exact le_add_right (le_refl removed)
  have hcontinuingLe : continuing ≤ current := by
    rw [hconservation]
    exact le_add_left (le_refl continuing)
  have hremovedFinite : removed ≠ ⊤ :=
    ne_top_of_le_ne_top hcurrentFinite hremovedLe
  have hcontinuingFinite : continuing ≠ ⊤ :=
    ne_top_of_le_ne_top hcurrentFinite hcontinuingLe
  have hcurrentReal :
      current.toReal = removed.toReal + continuing.toReal := by
    rw [hconservation, ENNReal.toReal_add hremovedFinite hcontinuingFinite]
  have hhalfRemovedReal :
      current.toReal ≤ removed.toReal + removed.toReal := by
    rw [← ENNReal.toReal_add hremovedFinite hremovedFinite]
    exact (ENNReal.toReal_le_toReal hcurrentFinite
      (ENNReal.add_ne_top.2 ⟨hremovedFinite, hremovedFinite⟩)).2 hhalfRemoved
  have hcontinuingRemoved : continuing ≤ removed := by
    apply (ENNReal.toReal_le_toReal hcontinuingFinite hremovedFinite).1
    linarith
  have hdouble : continuing * (2 : ENNReal) ≤ current := by
    calc
      continuing * (2 : ENNReal) = continuing + continuing := by ring
      _ ≤ removed + continuing := add_le_add hcontinuingRemoved (le_refl _)
      _ = current := hconservation.symm
  have hdiv : continuing ≤ current / (2 : ENNReal) :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))).2 hdouble
  simpa [ENNReal.div_eq_inv_mul, mul_comm] using hdiv

/-- Ready-to-use half-removal version of the compensation-zone closure.  It
matches the mass-conserving stopping in the manuscript: every generation is
split into removed and continuing mass, and the removed part is at least one
half of the current mass. -/
theorem threePacketReturnCarlesonLedger_of_half_mass_removal
    {n : ℕ} (capacity : Fin n → ENNReal)
    (levelCapacity current removed : ℕ → ENNReal)
    (rootMass chargeMultiplier : ENNReal)
    (hcapacity : Finset.univ.sum capacity ≤ ∑' k, levelCapacity k)
    (hcurrentZero : current 0 ≤ rootMass)
    (hcurrentFinite : ∀ k, current k ≠ ⊤)
    (hconservation : ∀ k,
      current k = removed k + current (k + 1))
    (hhalfRemoved : ∀ k,
      current k ≤ removed k + removed k)
    (hlevelCharge : ∀ k,
      levelCapacity k ≤ chargeMultiplier * current k) :
    Nonempty (ThreePacketReturnCarlesonLedger capacity) := by
  apply threePacketReturnCarlesonLedger_of_mass_conserving_decay capacity
    levelCapacity current rootMass chargeMultiplier (2 : ENNReal)⁻¹
  · norm_num
  · exact hcapacity
  · exact hcurrentZero
  · intro k
    exact ennreal_half_removal_forces_half_continuation
      (current k) (removed k) (current (k + 1))
      (hcurrentFinite k) (hconservation k) (hhalfRemoved k)
  · exact hlevelCharge

/-- Direct certificate form of the previous closure.  Once the geometric
stopping supplies conservation, local charges, and fixed-ratio continuing
mass, no additional Carleson hypothesis is needed. -/
theorem contactSymplecticEdgeFlowCertificate_of_mass_conserving_threePacketReturn
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming paid terminalMass capacity : Fin n → ENNReal)
    (levelCapacity remaining : ℕ → ENNReal)
    (rootMass chargeMultiplier ratio : ENNReal)
    (hratio : ratio < 1)
    (hcapacity : Finset.univ.sum capacity ≤ ∑' k, levelCapacity k)
    (hremainingZero : remaining 0 ≤ rootMass)
    (hremainingStep : ∀ k,
      remaining (k + 1) ≤ remaining k * ratio)
    (hlevelCharge : ∀ k,
      levelCapacity k ≤ chargeMultiplier * remaining k)
    (hconservation : ∀ i,
      incoming i = paid i + terminalMass i +
        Finset.univ.sum (fun j : Fin n ↦
          if R.tree.parent j = some i then incoming j else 0))
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n ↦
        if R.tree.parent i = none then incoming i else 0))
    (hlocalCharge : ∀ i,
      paid i + terminalMass i ≤ capacity i * volume (sourceUnion R))
    (hrootAbsorption :
      (chargeMultiplier * rootMass) * (1 - ratio)⁻¹ ≤
        A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  have hremaining : ∀ k,
      remaining k ≤ rootMass * ratio ^ k :=
    ennreal_geometric_remaining_bound remaining rootMass ratio
      hremainingZero hremainingStep
  let ledger : ThreePacketReturnCarlesonLedger capacity := {
    levelCapacity := levelCapacity
    rootBudget := chargeMultiplier * rootMass
    ratio := ratio
    ratio_lt_one := hratio
    capacityDominated := hcapacity
    levelDecay := fun k => by
      calc
        levelCapacity k ≤ chargeMultiplier * remaining k := hlevelCharge k
        _ ≤ chargeMultiplier * (rootMass * ratio ^ k) :=
          by simpa [mul_comm] using
            (mul_le_mul_right (hremaining k) chargeMultiplier)
        _ = (chargeMultiplier * rootMass) * ratio ^ k := by ac_rfl }
  apply contactSymplecticEdgeFlowCertificate_of_conservative_capacity
    D R ε A incoming paid terminalMass capacity
    hconservation hsourceAtRoots hlocalCharge
  exact ledger.capacityCarleson.trans hrootAbsorption

/-- A three-packet return ledger supplies the capacity hypothesis of the
finite contact--symplectic certificate as soon as its root geometric budget
is absorbed by the requested source-scale allowance.  No Wang--Zakharov
estimate or carrier-pruning module is used. -/
theorem contactSymplecticEdgeFlowCertificate_of_threePacketReturnCarleson
    {n : ℕ} (D R : FiniteScaleSource n) (ε : ℝ) (A : ENNReal)
    (incoming paid terminalMass capacity : Fin n → ENNReal)
    (ledger : ThreePacketReturnCarlesonLedger capacity)
    (hconservation : ∀ i,
      incoming i = paid i + terminalMass i +
        Finset.univ.sum (fun j : Fin n ↦
          if R.tree.parent j = some i then incoming j else 0))
    (hsourceAtRoots : sourceMass R =
      Finset.univ.sum (fun i : Fin n ↦
        if R.tree.parent i = none then incoming i else 0))
    (hlocalCharge : ∀ i,
      paid i + terminalMass i ≤ capacity i * volume (sourceUnion R))
    (hrootAbsorption :
      ledger.rootBudget * (1 - ledger.ratio)⁻¹ ≤
        A * (ENNReal.ofReal D.thickness).rpow (-ε)) :
    Nonempty (ContactSymplecticEdgeFlowCertificate D R ε A) := by
  apply contactSymplecticEdgeFlowCertificate_of_conservative_capacity
    D R ε A incoming paid terminalMass capacity
    hconservation hsourceAtRoots hlocalCharge
  exact ledger.capacityCarleson.trans hrootAbsorption

end StickyKakeya4
