import Theorems.Thm_StickyKakeya4_finite_four_sample_three_packet
import Theorems.Thm_StickyKakeya4_three_packet_return_carleson

namespace StickyKakeya4

noncomputable section

theorem finiteRestrictedMass_nonneg
    {n : ℕ} (weight : Fin n → ℝ)
    (predicate : Fin n → Prop) [DecidablePred predicate]
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ finiteRestrictedMass weight predicate := by
  unfold finiteRestrictedMass
  exact Finset.sum_nonneg fun i _ ↦ by
    split_ifs
    · exact hweight i
    · exact le_rfl

theorem finiteThreePacketsMass_nonneg
    {n : ℕ} (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (a b c : Fin n) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ finiteThreePacketsMass weight time delta a b c := by
  classical
  exact finiteRestrictedMass_nonneg weight _ hweight

theorem finiteOutsideThreePacketsMass_nonneg
    {n : ℕ} (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (a b c : Fin n) (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ finiteOutsideThreePacketsMass weight time delta a b c := by
  classical
  exact finiteRestrictedMass_nonneg weight _ hweight

/-- The finite four-sample alternative supplies the exact `ENNReal` split
needed by the mass-conserving return ledger.  The three selected Reeb packets
remove at least half the normalized mass, and the strict complement is the
continuing mass. -/
theorem finite_three_packet_split_ennreal_of_four_sample_small
    {n : ℕ} [Nonempty (Fin n)]
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) = 1)
    (hfour : finiteFourSeparatedSamplingMass weight time delta < 1 / 8) :
    ∃ a b c,
      (1 : ENNReal) =
        ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) +
        ENNReal.ofReal (finiteOutsideThreePacketsMass weight time delta a b c) ∧
      (1 : ENNReal) ≤
        ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) +
        ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) := by
  obtain ⟨a, b, c, hhalf⟩ :=
    finite_three_packets_of_four_sample_mass_lt_one_eighth
      weight time delta hweight htotal hfour
  let removed : ℝ := finiteThreePacketsMass weight time delta a b c
  let continuing : ℝ :=
    finiteOutsideThreePacketsMass weight time delta a b c
  have hremoved : 0 ≤ removed := by
    exact finiteThreePacketsMass_nonneg weight time delta a b c hweight
  have hcontinuing : 0 ≤ continuing := by
    exact finiteOutsideThreePacketsMass_nonneg weight time delta a b c hweight
  have hpartition : removed + continuing = 1 := by
    simpa [removed, continuing, htotal] using
      finite_three_packets_add_outside_mass weight time delta a b c
  have hhalfRemoved : (1 / 2 : ℝ) < removed := by
    simpa [removed] using hhalf
  have hdouble : (1 : ℝ) ≤ removed + removed := by
    linarith
  refine ⟨a, b, c, ?_, ?_⟩
  · calc
      (1 : ENNReal) = ENNReal.ofReal (removed + continuing) := by
        rw [hpartition]
        simp
      _ = ENNReal.ofReal removed + ENNReal.ofReal continuing :=
        ENNReal.ofReal_add hremoved hcontinuing
      _ = _ := by rfl
  · calc
      (1 : ENNReal) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (removed + removed) :=
        ENNReal.ofReal_le_ofReal hdouble
      _ = ENNReal.ofReal removed + ENNReal.ofReal removed :=
        ENNReal.ofReal_add hremoved hremoved
      _ = _ := by rfl

/-- Scale the normalized finite three-packet split by an arbitrary current
mass.  This is the exact conservation/half-removal pair consumed generation by
generation by `threePacketReturnCarlesonLedger_of_half_mass_removal`. -/
theorem finite_three_packet_scaled_half_removal_of_four_sample_small
    {n : ℕ} [Nonempty (Fin n)]
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) = 1)
    (hfour : finiteFourSeparatedSamplingMass weight time delta < 1 / 8)
    (current : ENNReal) :
    ∃ a b c, ∃ removed continuing : ENNReal,
      removed = current *
        ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) ∧
      continuing = current *
        ENNReal.ofReal (finiteOutsideThreePacketsMass weight time delta a b c) ∧
      current = removed + continuing ∧
      current ≤ removed + removed := by
  obtain ⟨a, b, c, hconservation, hhalf⟩ :=
    finite_three_packet_split_ennreal_of_four_sample_small
      weight time delta hweight htotal hfour
  let removed := current *
    ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c)
  let continuing := current *
    ENNReal.ofReal (finiteOutsideThreePacketsMass weight time delta a b c)
  refine ⟨a, b, c, removed, continuing, rfl, rfl, ?_, ?_⟩
  · calc
      current = current * 1 := by simp
      _ = current *
          (ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) +
            ENNReal.ofReal
              (finiteOutsideThreePacketsMass weight time delta a b c)) := by
        rw [hconservation]
      _ = removed + continuing := by
        simp only [mul_add, removed, continuing]
  · calc
      current = current * 1 := by simp
      _ ≤ current *
          (ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) +
            ENNReal.ofReal
              (finiteThreePacketsMass weight time delta a b c)) := by
        simpa [mul_comm] using mul_le_mul_left hhalf current
      _ = removed + removed := by
        simp only [mul_add, removed]

/-- Positive four-sample mass is witnessed by four actual positive-weight
indices carrying all six strict Reeb separations.  This is the support-level
output needed to feed the four-probe continuation branch; it does not replace
the weighted law by an unweighted cardinality count. -/
theorem finiteFourSeparatedSamplingMass_pos_has_positive_samples
    {n : ℕ} (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hfour : 0 < finiteFourSeparatedSamplingMass weight time delta) :
    ∃ i₀ i₁ i₂ i₃,
      0 < weight i₀ ∧ 0 < weight i₁ ∧
      0 < weight i₂ ∧ 0 < weight i₃ ∧
      finiteReebSeparated time delta i₁ i₀ ∧
      finiteReebSeparated time delta i₂ i₀ ∧
      finiteReebSeparated time delta i₂ i₁ ∧
      finiteReebSeparated time delta i₃ i₀ ∧
      finiteReebSeparated time delta i₃ i₁ ∧
      finiteReebSeparated time delta i₃ i₂ := by
  classical
  let third : Fin n → Fin n → Fin n → ℝ := fun i₀ i₁ i₂ ↦
    ∑ i₃, if
        finiteReebSeparated time delta i₃ i₀ ∧
        finiteReebSeparated time delta i₃ i₁ ∧
        finiteReebSeparated time delta i₃ i₂ then
      weight i₃ else 0
  let second : Fin n → Fin n → ℝ := fun i₀ i₁ ↦
    ∑ i₂, if
        finiteReebSeparated time delta i₂ i₀ ∧
        finiteReebSeparated time delta i₂ i₁ then
      weight i₂ * third i₀ i₁ i₂ else 0
  let first : Fin n → ℝ := fun i₀ ↦
    ∑ i₁, if finiteReebSeparated time delta i₁ i₀ then
      weight i₁ * second i₀ i₁ else 0
  have hthirdNonneg : ∀ i₀ i₁ i₂, 0 ≤ third i₀ i₁ i₂ := by
    intro i₀ i₁ i₂
    exact Finset.sum_nonneg fun i₃ _ ↦ by
      split_ifs
      · exact hweight i₃
      · exact le_rfl
  have hsecondNonneg : ∀ i₀ i₁, 0 ≤ second i₀ i₁ := by
    intro i₀ i₁
    exact Finset.sum_nonneg fun i₂ _ ↦ by
      split_ifs
      · exact mul_nonneg (hweight i₂) (hthirdNonneg i₀ i₁ i₂)
      · exact le_rfl
  have hfirstNonneg : ∀ i₀, 0 ≤ first i₀ := by
    intro i₀
    exact Finset.sum_nonneg fun i₁ _ ↦ by
      split_ifs
      · exact mul_nonneg (hweight i₁) (hsecondNonneg i₀ i₁)
      · exact le_rfl
  have houter : 0 < ∑ i₀, weight i₀ * first i₀ := by
    simpa [finiteFourSeparatedSamplingMass, first, second, third] using hfour
  obtain ⟨i₀, _hi₀, hi₀term⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun i₀ _ ↦ mul_nonneg (hweight i₀) (hfirstNonneg i₀))).mp houter
  have hi₀ : 0 < weight i₀ :=
    pos_of_mul_pos_left hi₀term (hfirstNonneg i₀)
  have hfirstPos : 0 < first i₀ :=
    pos_of_mul_pos_right hi₀term (hweight i₀)
  obtain ⟨i₁, _hi₁, hi₁term⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (f := fun i₁ ↦
        if finiteReebSeparated time delta i₁ i₀ then
          weight i₁ * second i₀ i₁ else 0)
      (fun i₁ _ ↦ by
        split_ifs
        · exact mul_nonneg (hweight i₁) (hsecondNonneg i₀ i₁)
        · exact le_rfl)).mp (by simpa [first] using hfirstPos)
  have hsep₁₀ : finiteReebSeparated time delta i₁ i₀ := by
    by_contra hsep
    simp [hsep] at hi₁term
  have hi₁mul : 0 < weight i₁ * second i₀ i₁ := by
    simpa [hsep₁₀] using hi₁term
  have hi₁ : 0 < weight i₁ :=
    pos_of_mul_pos_left hi₁mul (hsecondNonneg i₀ i₁)
  have hsecondPos : 0 < second i₀ i₁ :=
    pos_of_mul_pos_right hi₁mul (hweight i₁)
  obtain ⟨i₂, _hi₂, hi₂term⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (f := fun i₂ ↦
        if finiteReebSeparated time delta i₂ i₀ ∧
            finiteReebSeparated time delta i₂ i₁ then
          weight i₂ * third i₀ i₁ i₂ else 0)
      (fun i₂ _ ↦ by
        split_ifs
        · exact mul_nonneg (hweight i₂) (hthirdNonneg i₀ i₁ i₂)
        · exact le_rfl)).mp (by simpa [second] using hsecondPos)
  have hsep₂ :
      finiteReebSeparated time delta i₂ i₀ ∧
      finiteReebSeparated time delta i₂ i₁ := by
    by_contra hsep
    simp [hsep] at hi₂term
  have hi₂mul : 0 < weight i₂ * third i₀ i₁ i₂ := by
    simpa [hsep₂] using hi₂term
  have hi₂ : 0 < weight i₂ :=
    pos_of_mul_pos_left hi₂mul (hthirdNonneg i₀ i₁ i₂)
  have hthirdPos : 0 < third i₀ i₁ i₂ :=
    pos_of_mul_pos_right hi₂mul (hweight i₂)
  obtain ⟨i₃, _hi₃, hi₃term⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (f := fun i₃ ↦
        if finiteReebSeparated time delta i₃ i₀ ∧
            finiteReebSeparated time delta i₃ i₁ ∧
            finiteReebSeparated time delta i₃ i₂ then
          weight i₃ else 0)
      (fun i₃ _ ↦ by
        split_ifs
        · exact hweight i₃
        · exact le_rfl)).mp (by simpa [third] using hthirdPos)
  have hsep₃ :
      finiteReebSeparated time delta i₃ i₀ ∧
      finiteReebSeparated time delta i₃ i₁ ∧
      finiteReebSeparated time delta i₃ i₂ := by
    by_contra hsep
    simp [hsep] at hi₃term
  have hi₃ : 0 < weight i₃ := by simpa [hsep₃] using hi₃term
  exact ⟨i₀, i₁, i₂, i₃, hi₀, hi₁, hi₂, hi₃,
    hsep₁₀, hsep₂.1, hsep₂.2,
    hsep₃.1, hsep₃.2.1, hsep₃.2.2⟩

/-- Complete finite routing at one stopping generation.  A normalized weighted
Reeb population either contains four actual positive-weight separated samples,
or three actual packets remove at least half of an arbitrary current mass with
coefficient-one conservation. -/
theorem finite_positive_four_samples_or_scaled_three_packet_half_removal
    {n : ℕ} [Nonempty (Fin n)]
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) = 1) (current : ENNReal) :
    (∃ i₀ i₁ i₂ i₃,
      0 < weight i₀ ∧ 0 < weight i₁ ∧
      0 < weight i₂ ∧ 0 < weight i₃ ∧
      finiteReebSeparated time delta i₁ i₀ ∧
      finiteReebSeparated time delta i₂ i₀ ∧
      finiteReebSeparated time delta i₂ i₁ ∧
      finiteReebSeparated time delta i₃ i₀ ∧
      finiteReebSeparated time delta i₃ i₁ ∧
      finiteReebSeparated time delta i₃ i₂) ∨
    ∃ a b c, ∃ removed continuing : ENNReal,
      removed = current *
        ENNReal.ofReal (finiteThreePacketsMass weight time delta a b c) ∧
      continuing = current *
        ENNReal.ofReal (finiteOutsideThreePacketsMass weight time delta a b c) ∧
      current = removed + continuing ∧
      current ≤ removed + removed := by
  rcases le_or_gt (1 / 8 : ℝ)
      (finiteFourSeparatedSamplingMass weight time delta) with hlarge | hsmall
  · left
    apply finiteFourSeparatedSamplingMass_pos_has_positive_samples
      weight time delta hweight
    linarith
  · right
    exact finite_three_packet_scaled_half_removal_of_four_sample_small
      weight time delta hweight htotal hsmall current

end

end StickyKakeya4
