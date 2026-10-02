import Theorems.Thm_StickyKakeya4_dimension_witness_extraction

open Filter MeasureTheory Set
open scoped ENNReal

namespace StickyKakeya4.PositiveCellRegularization

/-!
A countable overlapping-cell pruning.  Every cell is charged only at its first
eligible stage, so the total loss is bounded by the sum of thresholds even
when the cells overlap.  The result concerns one fixed positive restriction;
it is not a claim about arbitrary later restrictions of that source.
-/

variable {X ι : Type*} [MeasurableSpace X]

/-- At every stage remove every cell whose current mass is below its threshold. -/
def stage (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) : ℕ → Set X
  | 0 => Set.univ
  | n + 1 => stage μ F a n \ ⋃ i, ⋃ (_h : μ (stage μ F a n ∩ F i) < a i), F i

@[simp] theorem stage_zero (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) :
    stage μ F a 0 = Set.univ := rfl

/-- The pruning sequence is decreasing. -/
theorem stage_antitone (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) :
    Antitone (stage μ F a) := by
  apply antitone_nat_of_succ_le
  intro n
  exact Set.sdiff_subset

/-- Measurability is preserved by every countable deletion stage. -/
theorem measurableSet_stage [Countable ι]
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal)
    (hF : ∀ i, MeasurableSet (F i)) (n : ℕ) :
    MeasurableSet (stage μ F a n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n hn =>
    exact hn.diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hF i)

/-- The part charged to a cell is its surviving part at its first eligible stage. -/
noncomputable def firstCharge (μ : Measure X) (F : ι → Set X)
    (a : ι → ENNReal) (i : ι) : Set X := by
  classical
  exact if h : ∃ n, μ (stage μ F a n ∩ F i) < a i then
    stage μ F a (Nat.find h) ∩ F i else ∅

/-- Each cell incurs a charge of at most its threshold, exactly once. -/
theorem measure_firstCharge_le
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) (i : ι) :
    μ (firstCharge μ F a i) ≤ a i := by
  classical
  unfold firstCharge
  split_ifs with h
  · exact (Nat.find_spec h).le
  · simp

/-- Any part removed from a cell at a later eligible stage lies in its first charge. -/
theorem stage_inter_subset_firstCharge
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal)
    (i : ι) (n : ℕ) (hn : μ (stage μ F a n ∩ F i) < a i) :
    stage μ F a n ∩ F i ⊆ firstCharge μ F a i := by
  classical
  have hex : ∃ m, μ (stage μ F a m ∩ F i) < a i := ⟨n, hn⟩
  simp only [firstCharge, dif_pos hex]
  exact Set.inter_subset_inter_left _ (stage_antitone μ F a (Nat.find_min' hex hn))

/-- All discarded points are covered by the union of the first charges. -/
theorem stage_compl_subset_firstCharges
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) (n : ℕ) :
    (stage μ F a n)ᶜ ⊆ ⋃ i, firstCharge μ F a i := by
  classical
  induction n with
  | zero => simp
  | succ n hn =>
    intro x hx
    by_cases hxn : x ∈ stage μ F a n
    · have hrem : x ∈ ⋃ i, ⋃ (_h : μ (stage μ F a n ∩ F i) < a i), F i := by
        simpa only [stage, Set.mem_compl_iff, Set.mem_sdiff, hxn, true_and,
          not_not] using hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hrem
      obtain ⟨helig, hxFi⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨i,
        stage_inter_subset_firstCharge μ F a i n helig ⟨hxn, hxFi⟩⟩
    · exact hn hxn

/-- The measurable limiting source retained by the simultaneous deletion. -/
def retained (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) : Set X :=
  ⋂ n, stage μ F a n

/-- The fixed retained source is measurable. -/
theorem measurableSet_retained [Countable ι]
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal)
    (hF : ∀ i, MeasurableSet (F i)) :
    MeasurableSet (retained μ F a) :=
  MeasurableSet.iInter (measurableSet_stage μ F a hF)

/-- Loss is charged over cell indices, never over the infinitely many stages. -/
theorem measure_retained_compl_le [Countable ι]
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal) :
    μ (retained μ F a)ᶜ ≤ ∑' i, a i := by
  classical
  have hcover : (retained μ F a)ᶜ ⊆ ⋃ i, firstCharge μ F a i := by
    intro x hx
    have hex : ∃ n, x ∉ stage μ F a n := by
      simpa only [retained, Set.mem_compl_iff, Set.mem_iInter, not_forall] using hx
    obtain ⟨n, hn⟩ := hex
    exact stage_compl_subset_firstCharges μ F a n hn
  calc
    μ (retained μ F a)ᶜ ≤ μ (⋃ i, firstCharge μ F a i) := measure_mono hcover
    _ ≤ ∑' i, μ (firstCharge μ F a i) := measure_iUnion_le _
    _ ≤ ∑' i, a i := ENNReal.tsum_le_tsum (measure_firstCharge_le μ F a)

/-- Every occupied cell of the fixed limit has at least its prescribed mass. -/
theorem retained_cell_zero_or_ge [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : ι → Set X) (a : ι → ENNReal)
    (hF : ∀ i, MeasurableSet (F i)) (i : ι) :
    μ (retained μ F a ∩ F i) = 0 ∨ a i ≤ μ (retained μ F a ∩ F i) := by
  classical
  by_cases hmass : a i ≤ μ (retained μ F a ∩ F i)
  · exact Or.inr hmass
  left
  have hlt : μ (retained μ F a ∩ F i) < a i := lt_of_not_ge hmass
  have hanti : Antitone fun n => stage μ F a n ∩ F i := by
    intro m n hmn
    exact Set.inter_subset_inter_left _ (stage_antitone μ F a hmn)
  have hlimit : μ (retained μ F a ∩ F i) = ⨅ n, μ (stage μ F a n ∩ F i) := by
    have hsets : retained μ F a ∩ F i = ⋂ n, stage μ F a n ∩ F i := by
      ext x
      simp only [retained, Set.mem_inter_iff, Set.mem_iInter]
      simp only [forall_and, forall_const]
    rw [hsets]
    exact hanti.measure_iInter
      (fun n => ((measurableSet_stage μ F a hF n).inter (hF i)).nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩
  rw [hlimit, iInf_lt_iff] at hlt
  obtain ⟨n, hn⟩ := hlt
  have hempty : retained μ F a ∩ F i = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxnext : x ∈ stage μ F a (n + 1) := Set.mem_iInter.mp hx.1 (n + 1)
    exact hxnext.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hn, hx.2⟩⟩)
  simp [hempty]

/-- A threshold sum below the original total mass leaves a positive source. -/
theorem measure_retained_pos [Countable ι]
    (μ : Measure X) (F : ι → Set X) (a : ι → ENNReal)
    (hsum : (∑' i, a i) < μ Set.univ) :
    0 < μ (retained μ F a) := by
  have hloss : μ (retained μ F a)ᶜ < μ Set.univ :=
    (measure_retained_compl_le μ F a).trans_lt hsum
  by_contra hnot
  have hz : μ (retained μ F a) = 0 := le_antisymm (le_of_not_gt hnot) bot_le
  have htotal : μ Set.univ ≤ μ (retained μ F a) + μ (retained μ F a)ᶜ := by
    calc
      μ Set.univ = μ (retained μ F a ∪ (retained μ F a)ᶜ) := by simp
      _ ≤ μ (retained μ F a) + μ (retained μ F a)ᶜ := measure_union_le _ _
  rw [hz, zero_add] at htotal
  exact (not_lt_of_ge htotal) hloss

/-- Construct a positive measurable restriction with zero-or-threshold mass in
all countably many, possibly overlapping, cells. No lower-mass certificate is
assumed: the set and all cell bounds are produced by the pruning construction. -/
theorem exists_positive_restriction [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : ι → Set X) (a : ι → ENNReal)
    (hF : ∀ i, MeasurableSet (F i))
    (hsum : (∑' i, a i) < μ Set.univ) :
    ∃ B : Set X, MeasurableSet B ∧ μ Bᶜ ≤ ∑' i, a i ∧ 0 < μ B ∧
      ∀ i, (μ.restrict B) (F i) = 0 ∨ a i ≤ (μ.restrict B) (F i) := by
  refine ⟨retained μ F a, measurableSet_retained μ F a hF,
    measure_retained_compl_le μ F a, measure_retained_pos μ F a hsum, ?_⟩
  intro i
  simpa only [Measure.restrict_apply (hF i), Set.inter_comm] using
    retained_cell_zero_or_ge μ F a hF i

/-- Finite total weight allows one positive uniform threshold factor while
losing less than half the source mass. The factor is chosen before any later
finite-scale construction. -/
theorem exists_positive_restriction_of_finite_weight [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : ι → Set X) (w : ι → ENNReal)
    (hF : ∀ i, MeasurableSet (F i))
    (hμ : 0 < μ Set.univ) (hw : (∑' i, w i) ≠ ⊤) :
    ∃ c : ENNReal, 0 < c ∧ c ≤ 1 ∧
      ∃ B : Set X, MeasurableSet B ∧ μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
        ∀ i, (μ.restrict B) (F i) = 0 ∨ c * w i ≤ (μ.restrict B) (F i) := by
  classical
  have hhalf : 0 < μ Set.univ / 2 :=
    ENNReal.div_pos_iff.mpr ⟨hμ.ne', by norm_num⟩
  obtain ⟨c₀, hc₀, hsmall⟩ := ENNReal.exists_pos_mul_lt hw hhalf.ne'
  let c := min c₀ 1
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hbudget : (∑' i, c * w i) < μ Set.univ / 2 := by
    rw [ENNReal.tsum_mul_left]
    exact (mul_le_mul' (min_le_left c₀ 1) le_rfl).trans_lt hsmall
  have hsum : (∑' i, c * w i) < μ Set.univ := by
    exact hbudget.trans_le ENNReal.half_le_self
  obtain ⟨B, hB, hloss, hpos, hcells⟩ :=
    exists_positive_restriction μ F (fun i => c * w i) hF hsum
  exact ⟨c, hc, min_le_right _ _, B, hB, hloss.trans_lt hbudget, hpos, hcells⟩

/-- The dyadic radius, in the extended nonnegative reals. -/
noncomputable def dyadicScale (n : ℕ) : ENNReal := (1 / 2 : ENNReal) ^ n

/-- Any positive power slack pays for all scales of a finite family with
power-law cardinality. No uniform positive lower bound on the original cell
masses is used. -/
theorem multiscale_weight_ne_top
    (β : ℕ → Type*) [∀ n, Fintype (β n)]
    (C : ENNReal) (hC : C ≠ ⊤) (d κ : ℝ) (hκ : 0 < κ)
    (hcard : ∀ n, (Fintype.card (β n) : ENNReal) ≤ C * (dyadicScale n) ^ (-d)) :
    (∑' p : Sigma β, (dyadicScale p.1) ^ (d + κ)) ≠ ⊤ := by
  have hbase0 : (1 / 2 : ENNReal) ≠ 0 := by norm_num
  have hbaseTop : (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
  have hbound (n : ℕ) :
      (∑' _i : β n, (dyadicScale n) ^ (d + κ)) ≤
        C * ((1 / 2 : ENNReal) ^ κ) ^ n := by
    have hn0 : dyadicScale n ≠ 0 := pow_ne_zero _ hbase0
    have hnTop : dyadicScale n ≠ ⊤ := ENNReal.pow_ne_top hbaseTop
    calc
      (∑' _i : β n, (dyadicScale n) ^ (d + κ)) =
          (Fintype.card (β n) : ENNReal) * (dyadicScale n) ^ (d + κ) := by
        simp [tsum_fintype, nsmul_eq_mul]
      _ ≤ (C * (dyadicScale n) ^ (-d)) * (dyadicScale n) ^ (d + κ) :=
        mul_le_mul' (hcard n) le_rfl
      _ = C * (dyadicScale n) ^ κ := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hn0 hnTop]
        congr 2
        ring
      _ = C * ((1 / 2 : ENNReal) ^ κ) ^ n := by
        rw [dyadicScale, ← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ) κ,
          ENNReal.rpow_mul, ENNReal.rpow_natCast]
  have hgeom : (∑' n : ℕ, ((1 / 2 : ENNReal) ^ κ) ^ n) ≠ ⊤ := by
    exact (tsum_geometric_lt_top.mpr
      (ENNReal.rpow_lt_one (by norm_num) hκ)).ne
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hgeom)
  rw [ENNReal.tsum_sigma (fun n (_i : β n) => (dyadicScale n) ^ (d + κ)),
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hbound

/-- Construct one positive source with a fixed-power lower bound in every
occupied cell at every dyadic scale of a power-cardinality family. -/
theorem exists_multiscale_positive_restriction
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : 0 < μ Set.univ)
    (β : ℕ → Type*) [∀ n, Fintype (β n)]
    (F : ∀ n, β n → Set X) (hF : ∀ n i, MeasurableSet (F n i))
    (C : ENNReal) (hC : C ≠ ⊤) (d κ : ℝ) (hκ : 0 < κ)
    (hcard : ∀ n, (Fintype.card (β n) : ENNReal) ≤ C * (dyadicScale n) ^ (-d)) :
    ∃ c : ENNReal, 0 < c ∧ c ≤ 1 ∧
      ∃ B : Set X, MeasurableSet B ∧ μ Bᶜ < μ Set.univ / 2 ∧ 0 < μ B ∧
        ∀ n i, (μ.restrict B) (F n i) = 0 ∨
          c * (dyadicScale n) ^ (d + κ) ≤ (μ.restrict B) (F n i) := by
  obtain ⟨c, hc, hc1, B, hB, hloss, hpos, hcells⟩ :=
    exists_positive_restriction_of_finite_weight μ
      (fun p : Sigma β => F p.1 p.2)
      (fun p : Sigma β => (dyadicScale p.1) ^ (d + κ))
      (fun p => hF p.1 p.2) hμ (multiscale_weight_ne_top β C hC d κ hκ hcard)
  exact ⟨c, hc, hc1, B, hB, hloss, hpos, fun n i => hcells ⟨n, i⟩⟩

/-- Remove the union of all zero-mass prescribed cells without changing the
restricted measure. Every cell that still meets the cleaned set then has
strictly positive restricted mass. This gives literal occupied-cell covers,
not just almost-everywhere covers. -/
theorem exists_clean_restriction [Countable ι]
    (μ : Measure X) (B : Set X) (hB : MeasurableSet B)
    (F : ι → Set X) (hF : ∀ i, MeasurableSet (F i)) :
    ∃ B' : Set X, B' ⊆ B ∧ MeasurableSet B' ∧ B' =ᵐ[μ] B ∧
      μ.restrict B' = μ.restrict B ∧
      ∀ i, (B' ∩ F i).Nonempty → 0 < (μ.restrict B') (F i) := by
  classical
  let Z : Set X := ⋃ i, ⋃ (_h : μ (B ∩ F i) = 0), B ∩ F i
  have hZmeas : MeasurableSet Z :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB.inter (hF i)
  have hZ : μ Z = 0 := by
    apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro hi
    exact hi
  have hae : B \ Z =ᵐ[μ] B :=
    sdiff_ae_eq_self.mpr (measure_mono_null Set.inter_subset_right hZ)
  have hrestrict : μ.restrict (B \ Z) = μ.restrict B :=
    Measure.restrict_congr_set hae
  refine ⟨B \ Z, Set.sdiff_subset, hB.diff hZmeas, hae, hrestrict, ?_⟩
  intro i ⟨x, hx⟩
  rw [hrestrict]
  by_contra hnot
  have hzero : μ (B ∩ F i) = 0 := by
    have hz : (μ.restrict B) (F i) = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    simpa only [Measure.restrict_apply (hF i), Set.inter_comm] using hz
  exact hx.1.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hzero, hx.1.1, hx.2⟩⟩)

end StickyKakeya4.PositiveCellRegularization
