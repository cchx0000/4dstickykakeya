import Theorems.Thm_StickyKakeya4_three_packet_support

namespace StickyKakeya4

noncomputable section

/-- Weighted mass of a finite predicate. -/
def finiteRestrictedMass {n : ℕ} (weight : Fin n → ℝ)
    (predicate : Fin n → Prop) [DecidablePred predicate] : ℝ :=
  ∑ i, if predicate i then weight i else 0

/-- Multiplying every retained nonnegative weight by a function bounded below
by `c` bounds the corresponding weighted sum from below. -/
theorem finiteRestrictedMass_mul_lower_bound
    {n : ℕ} (weight value : Fin n → ℝ)
    (predicate : Fin n → Prop) [DecidablePred predicate]
    (c : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hvalue : ∀ i, predicate i → c ≤ value i) :
    c * finiteRestrictedMass weight predicate ≤
      ∑ i, if predicate i then weight i * value i else 0 := by
  unfold finiteRestrictedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : predicate i
  · simp only [hp, if_true]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hvalue i hp) (hweight i)
  · simp [hp]

/-- Two finite Reeb labels are separated at resolution `delta`. -/
def finiteReebSeparated {n : ℕ} (time : Fin n → ℝ)
    (delta : ℝ) (i j : Fin n) : Prop :=
  delta < |time i - time j|

/-- Mass outside the three closed Reeb packets centered at `a`, `b`, `c`. -/
noncomputable def finiteOutsideThreePacketsMass {n : ℕ}
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (a b c : Fin n) : ℝ := by
  classical
  exact finiteRestrictedMass weight (fun i ↦
    finiteReebSeparated time delta i a ∧
    finiteReebSeparated time delta i b ∧
    finiteReebSeparated time delta i c)

/-- Mass in the union of three closed Reeb packets. -/
noncomputable def finiteThreePacketsMass {n : ℕ}
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (a b c : Fin n) : ℝ := by
  classical
  exact finiteRestrictedMass weight (fun i ↦
    |time i - time a| ≤ delta ∨
    |time i - time b| ≤ delta ∨
    |time i - time c| ≤ delta)

/-- The ordered four-sample mass of pairwise `delta`-separated Reeb labels.
The nested expression is the finite Markov-kernel form used by the stopping
argument, so no normalization or fourth power of an absolute source mass is
introduced. -/
noncomputable def finiteFourSeparatedSamplingMass {n : ℕ}
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) : ℝ := by
  classical
  exact ∑ i₀, weight i₀ *
    ∑ i₁, if finiteReebSeparated time delta i₁ i₀ then
      weight i₁ *
        ∑ i₂, if
            finiteReebSeparated time delta i₂ i₀ ∧
            finiteReebSeparated time delta i₂ i₁ then
          weight i₂ *
            ∑ i₃, if
                finiteReebSeparated time delta i₃ i₀ ∧
                finiteReebSeparated time delta i₃ i₁ ∧
                finiteReebSeparated time delta i₃ i₂ then
              weight i₃ else 0
          else 0
      else 0

/-- If every three Reeb packets leave at least half of a finite probability
law uncovered, four independent samples are pairwise separated with mass at
least `1/8`.  This is the quantitative contrapositive used in the manuscript's
lossless three-packet stopping. -/
theorem finite_four_sample_mass_ge_one_eighth_of_three_packet_complements
    {n : ℕ} (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) = 1)
    (houtside : ∀ a b c,
      (1 / 2 : ℝ) ≤
        finiteOutsideThreePacketsMass weight time delta a b c) :
    (1 / 8 : ℝ) ≤
      finiteFourSeparatedSamplingMass weight time delta := by
  classical
  let sep : Fin n → Fin n → Prop := finiteReebSeparated time delta
  let third : Fin n → Fin n → Fin n → ℝ := fun i₀ i₁ i₂ ↦
    ∑ i₃, if sep i₃ i₀ ∧ sep i₃ i₁ ∧ sep i₃ i₂ then
      weight i₃ else 0
  let second : Fin n → Fin n → ℝ := fun i₀ i₁ ↦
    ∑ i₂, if sep i₂ i₀ ∧ sep i₂ i₁ then
      weight i₂ * third i₀ i₁ i₂ else 0
  let first : Fin n → ℝ := fun i₀ ↦
    ∑ i₁, if sep i₁ i₀ then weight i₁ * second i₀ i₁ else 0
  have hthird : ∀ i₀ i₁ i₂, (1 / 2 : ℝ) ≤ third i₀ i₁ i₂ := by
    intro i₀ i₁ i₂
    simpa [third, sep, finiteOutsideThreePacketsMass,
      finiteRestrictedMass] using houtside i₀ i₁ i₂
  have houtsideTwo : ∀ i₀ i₁,
      (1 / 2 : ℝ) ≤
        finiteRestrictedMass weight (fun i₂ ↦ sep i₂ i₀ ∧ sep i₂ i₁) := by
    intro i₀ i₁
    simpa [finiteOutsideThreePacketsMass, finiteRestrictedMass, sep] using
      houtside i₀ i₁ i₁
  have hsecond : ∀ i₀ i₁, (1 / 4 : ℝ) ≤ second i₀ i₁ := by
    intro i₀ i₁
    calc
      (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
      _ ≤ (1 / 2) * finiteRestrictedMass weight
          (fun i₂ ↦ sep i₂ i₀ ∧ sep i₂ i₁) := by
        exact mul_le_mul_of_nonneg_left (houtsideTwo i₀ i₁) (by norm_num)
      _ ≤ second i₀ i₁ := by
        simpa [second] using
          finiteRestrictedMass_mul_lower_bound weight
            (third i₀ i₁) (fun i₂ ↦ sep i₂ i₀ ∧ sep i₂ i₁)
            (1 / 2) hweight (fun i₂ hi₂ ↦ hthird i₀ i₁ i₂)
  have houtsideOne : ∀ i₀,
      (1 / 2 : ℝ) ≤ finiteRestrictedMass weight (fun i₁ ↦ sep i₁ i₀) := by
    intro i₀
    simpa [finiteOutsideThreePacketsMass, finiteRestrictedMass, sep] using
      houtside i₀ i₀ i₀
  have hfirst : ∀ i₀, (1 / 8 : ℝ) ≤ first i₀ := by
    intro i₀
    calc
      (1 / 8 : ℝ) = (1 / 4) * (1 / 2) := by norm_num
      _ ≤ (1 / 4) * finiteRestrictedMass weight (fun i₁ ↦ sep i₁ i₀) := by
        exact mul_le_mul_of_nonneg_left (houtsideOne i₀) (by norm_num)
      _ ≤ first i₀ := by
        simpa [first] using
          finiteRestrictedMass_mul_lower_bound weight (second i₀)
            (fun i₁ ↦ sep i₁ i₀) (1 / 4) hweight
            (fun i₁ hi₁ ↦ hsecond i₀ i₁)
  calc
    (1 / 8 : ℝ) = (1 / 8) * ∑ i, weight i := by rw [htotal, mul_one]
    _ ≤ ∑ i₀, weight i₀ * first i₀ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i₀ hi₀
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (hfirst i₀) (hweight i₀)
    _ = finiteFourSeparatedSamplingMass weight time delta := by
      rfl

/-- A three-packet union and its strict complement partition the entire
finite probability law exactly. -/
theorem finite_three_packets_add_outside_mass
    {n : ℕ} (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (a b c : Fin n) :
    finiteThreePacketsMass weight time delta a b c +
        finiteOutsideThreePacketsMass weight time delta a b c =
      ∑ i, weight i := by
  classical
  unfold finiteThreePacketsMass finiteOutsideThreePacketsMass finiteRestrictedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : |time i - time a| ≤ delta
  · have hnsa : ¬ delta < |time i - time a| := not_lt_of_ge ha
    simp [ha, finiteReebSeparated, hnsa]
  by_cases hb : |time i - time b| ≤ delta
  · have hnsb : ¬ delta < |time i - time b| := not_lt_of_ge hb
    simp [ha, hb, finiteReebSeparated, hnsb]
  by_cases hc : |time i - time c| ≤ delta
  · have hnsc : ¬ delta < |time i - time c| := not_lt_of_ge hc
    simp [ha, hb, hc, finiteReebSeparated, hnsc]
  · have hsa : delta < |time i - time a| := lt_of_not_ge ha
    have hsb : delta < |time i - time b| := lt_of_not_ge hb
    have hsc : delta < |time i - time c| := lt_of_not_ge hc
    simp [ha, hb, hc, finiteReebSeparated, hsa, hsb, hsc]

/-- Quantitative finite four-sample/three-packet dichotomy.  If the ordered
four-sample separated mass is below `1/8`, three closed Reeb packets centered
at actual retained labels carry more than half of the probability mass. -/
theorem finite_three_packets_of_four_sample_mass_lt_one_eighth
    {n : ℕ} [Nonempty (Fin n)]
    (weight : Fin n → ℝ) (time : Fin n → ℝ)
    (delta : ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (htotal : (∑ i, weight i) = 1)
    (hfour : finiteFourSeparatedSamplingMass weight time delta < 1 / 8) :
    ∃ a b c, (1 / 2 : ℝ) <
      finiteThreePacketsMass weight time delta a b c := by
  classical
  by_contra h
  push Not at h
  have houtside : ∀ a b c,
      (1 / 2 : ℝ) ≤ finiteOutsideThreePacketsMass weight time delta a b c := by
    intro a b c
    have hpartition := finite_three_packets_add_outside_mass
      weight time delta a b c
    rw [htotal] at hpartition
    linarith [h a b c]
  exact (not_le_of_gt hfour)
    (finite_four_sample_mass_ge_one_eighth_of_three_packet_complements
      weight time delta hweight htotal houtside)

end

end StickyKakeya4
