import Definitions.Def_sticky_kakeya4_core
import Theorems.Thm_StickyKakeya4_compact_front

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace StickyKakeya4

/-- A finite positive-volume piece of the physical front already gives the
full Frostman alternative.  We normalize Lebesgue measure restricted to the
piece.  The four-dimensional ball formula supplies exponent `4`, which is
stronger than every requested exponent `4 - ε` on radii at most one. -/
theorem hasFrontFrostmanMeasures_of_positive_finite_volume_subset
    (selector : Set MarkedLine) (piece : Set E4)
    (hpieceMeasurable : MeasurableSet piece)
    (hpieceFront : piece ⊆ unitFront selector)
    (hpiecePositive : volume piece ≠ 0)
    (hpieceFinite : volume piece ≠ ⊤) :
    HasFrontFrostmanMeasures selector := by
  let hfinite : IsFiniteMeasure (volume.restrict piece) :=
    isFiniteMeasure_restrict.mpr hpieceFinite
  let m : FiniteMeasure E4 :=
    ⟨volume.restrict piece, hfinite⟩
  have hm : m ≠ 0 := by
    intro hmzero
    have hmeasure : volume.restrict piece = 0 :=
      congrArg (fun q : FiniteMeasure E4 => (q : Measure E4)) hmzero
    exact hpiecePositive (Measure.restrict_eq_zero.mp hmeasure)
  intro ε hε hεFour
  let μ : Measure E4 := (m.normalize : Measure E4)
  have hμProbability : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let κ : ENNReal := ENNReal.ofReal (Real.pi ^ 2 / 2)
  let C : ENNReal := (↑m.mass⁻¹ : ENNReal) * κ
  have hCtop : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  refine ⟨μ, hμProbability, ?_, C, hCtop, ?_⟩
  · have hrestrictedSupport :
        (volume.restrict piece) (unitFront selector)ᶜ = 0 := by
      have hcomplement : (unitFront selector)ᶜ ⊆ pieceᶜ := by
        intro x hx hxinPiece
        exact hx (hpieceFront hxinPiece)
      apply measure_mono_null hcomplement
      rw [Measure.restrict_apply hpieceMeasurable.compl]
      simp
    rw [show μ = (m.normalize : Measure E4) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ENNReal) *
        (volume.restrict piece) (unitFront selector)ᶜ = 0
    rw [hrestrictedSupport, mul_zero]
  · intro x r hr hrOne
    have hrBase : ENNReal.ofReal r ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hrOne
    have hExponent : 4 - ε ≤ 4 := by linarith
    have hrpowFour :
        (ENNReal.ofReal r) ^ 4 =
          (ENNReal.ofReal r).rpow (4 : ℝ) :=
      (ENNReal.rpow_natCast (ENNReal.ofReal r) 4).symm
    have hrpow :
        (ENNReal.ofReal r) ^ 4 ≤
          (ENNReal.ofReal r).rpow (4 - ε) := by
      rw [hrpowFour]
      exact ENNReal.rpow_le_rpow_of_exponent_ge hrBase hExponent
    have hrestrictBall :
        (volume.restrict piece) (Metric.ball x r) ≤
          volume (Metric.ball x r) := by
      rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet]
      exact measure_mono inter_subset_left
    rw [show μ = (m.normalize : Measure E4) by rfl,
      m.toMeasure_normalize_eq_of_nonzero hm, Measure.smul_apply]
    change (↑m.mass⁻¹ : ENNReal) *
        (volume.restrict piece) (Metric.ball x r) ≤
      C * (ENNReal.ofReal r).rpow (4 - ε)
    calc
      (↑m.mass⁻¹ : ENNReal) *
            (volume.restrict piece) (Metric.ball x r) ≤
          (↑m.mass⁻¹ : ENNReal) * volume (Metric.ball x r) := by
        gcongr
      _ = (↑m.mass⁻¹ : ENNReal) *
          ((ENNReal.ofReal r) ^ 4 * κ) := by
        rw [volume_ball_E4]
      _ = C * (ENNReal.ofReal r) ^ 4 := by
        simp only [C, κ]
        ac_rfl
      _ ≤ C * (ENNReal.ofReal r).rpow (4 - ε) := by
        gcongr

/-- A positive Frostman exponent forces the measure to have no atoms. -/
theorem measure_singleton_eq_zero_of_ball_growth
    (mu : Measure E4) (C : ENNReal) (hCtop : C ≠ ⊤)
    (d : ℝ) (hd : 0 < d)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow d)
    (x : E4) : mu {x} = 0 := by
  apply bot_unique
  have hlim : Tendsto (fun r : ENNReal => C * r.rpow d)
      (𝓝[>] (0 : ENNReal)) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hCtop hd).mono_left
      inf_le_left
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ENNReal) < 1 by norm_num)).filter_mono
        inf_le_left] with r hrpos hrle
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hrtop : r ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hrle
  have hrRealPos : 0 < r.toReal := ENNReal.toReal_pos hr0 hrtop
  have hrRealLe : r.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hrtop ENNReal.one_ne_top).2 hrle
  have hsingleton : {x} ⊆ Metric.ball x r.toReal := by
    intro y hy
    rcases hy with rfl
    simpa [Metric.mem_ball] using hrRealPos
  calc
    mu {x} ≤ mu (Metric.ball x r.toReal) := measure_mono hsingleton
    _ ≤ C * (ENNReal.ofReal r.toReal).rpow d :=
      hball x r.toReal hrRealPos hrRealLe
    _ = C * r.rpow d := by rw [ENNReal.ofReal_toReal hrtop]

/-- A ball Frostman bound gives the arbitrary-set bound required by
`Measure.le_hausdorffMeasure`, with the harmless factor `2^d`. -/
theorem measure_le_const_mul_ediam_rpow_of_ball_growth
    (mu : Measure E4) (C : ENNReal) (hCtop : C ≠ ⊤)
    (d : ℝ) (hd : 0 < d)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow d)
    (s : Set E4) (hsdiam : Metric.ediam s ≤ (1 / 2 : ENNReal)) :
    mu s ≤ (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  by_cases hdiam0 : Metric.ediam s = 0
  · have hsubsingle : s.Subsingleton := Metric.ediam_eq_zero_iff.mp hdiam0
    obtain ⟨x, hx⟩ := hs
    have hsx : s = {x} := (subsingleton_iff_singleton hx).mp hsubsingle
    rw [hsx, measure_singleton_eq_zero_of_ball_growth mu C hCtop d hd hball x]
    simp
  · obtain ⟨x, hx⟩ := hs
    have hdiamtop : Metric.ediam s ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hsdiam
    have hdiampos : 0 < (Metric.ediam s).toReal :=
      ENNReal.toReal_pos hdiam0 hdiamtop
    have hsubset : s ⊆ Metric.ball x (2 * (Metric.ediam s).toReal) := by
      intro y hy
      rw [Metric.mem_ball]
      have hdist : dist y x ≤ (Metric.ediam s).toReal := by
        rw [dist_edist]
        exact (ENNReal.toReal_le_toReal (edist_ne_top _ _) hdiamtop).2
          (Metric.edist_le_ediam_of_mem hy hx)
      nlinarith
    have hrpos : 0 < 2 * (Metric.ediam s).toReal := by positivity
    have hrle : 2 * (Metric.ediam s).toReal ≤ 1 := by
      have hdiamRealLe : (Metric.ediam s).toReal ≤ (1 / 2 : ENNReal).toReal :=
        (ENNReal.toReal_le_toReal hdiamtop (by norm_num)).2 hsdiam
      norm_num at hdiamRealLe ⊢
      linarith
    calc
      mu s ≤ mu (Metric.ball x (2 * (Metric.ediam s).toReal)) :=
        measure_mono hsubset
      _ ≤ C * (ENNReal.ofReal (2 * (Metric.ediam s).toReal)).rpow d :=
        hball x (2 * (Metric.ediam s).toReal) hrpos hrle
      _ = (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2),
          ENNReal.ofReal_toReal hdiamtop]
        simp only [ENNReal.ofReal_ofNat]
        calc
          C * (2 * Metric.ediam s).rpow d =
              C * ((2 : ENNReal).rpow d * Metric.ediam s ^ d) := by
                change C * ((2 * Metric.ediam s) ^ d) =
                  C * ((2 : ENNReal) ^ d * Metric.ediam s ^ d)
                rw [ENNReal.mul_rpow_of_nonneg _ _ hd.le]
          _ = (C * (2 : ENNReal).rpow d) * Metric.ediam s ^ d := by ac_rfl

/-- Mass distribution principle in the exact form used by the selector closure. -/
theorem hausdorffMeasure_ne_zero_of_ball_growth
    (mu : Measure E4) [IsProbabilityMeasure mu]
    (s : Set E4) (hsupport : mu s.compl = 0)
    (C : ENNReal) (hCtop : C ≠ ⊤)
    (dnn : NNReal) (hdnn : 0 < dnn)
    (hball : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ C * (ENNReal.ofReal r).rpow (dnn : ℝ)) :
    MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ) s ≠ 0 := by
  let K : ENNReal := max 1 (C * (2 : ENNReal).rpow (dnn : Real))
  have hK0 : K ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (le_max_left _ _))
  have hKtop : K ≠ ⊤ := by
    apply ne_of_lt
    dsimp [K]
    rw [max_lt_iff]
    constructor
    · exact ENNReal.one_lt_top
    · exact lt_top_iff_ne_top.mpr <|
        ENNReal.mul_ne_top hCtop
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
  let nu : Measure E4 := K⁻¹ • mu
  have hnu_le : nu ≤ MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ) := by
    apply MeasureTheory.Measure.le_hausdorffMeasure (dnn : ℝ) nu (1 / 2) (by norm_num)
    intro t htdiam
    rw [show nu t = K⁻¹ * mu t by simp [nu]]
    calc
      K⁻¹ * mu t ≤ K⁻¹ *
          ((C * (2 : ENNReal).rpow (dnn : ℝ)) * Metric.ediam t ^ (dnn : ℝ)) := by
        gcongr
        exact measure_le_const_mul_ediam_rpow_of_ball_growth
          mu C hCtop (dnn : ℝ) (by exact_mod_cast hdnn) hball t htdiam
      _ ≤ K⁻¹ * (K * Metric.ediam t ^ (dnn : ℝ)) := by
        gcongr
        exact le_max_right _ _
      _ = Metric.ediam t ^ (dnn : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 hKtop, one_mul]
  have hmus : mu s ≠ 0 := by
    intro hmus0
    have hsunion : mu (s ∪ s.compl) = 0 :=
      measure_union_null hmus0 hsupport
    have hcover : s ∪ s.compl = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ s
      · exact Or.inl hx
      · exact Or.inr hx
    rw [hcover, measure_univ] at hsunion
    exact one_ne_zero hsunion
  have hnus : nu s ≠ 0 := by
    rw [show nu s = K⁻¹ * mu s by simp [nu]]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hKtop) hmus
  intro hzero
  apply hnus
  apply bot_unique
  simpa [hzero] using hnu_le s

/-- Frostman measures at every exponent below four force the unit front to
have Hausdorff dimension at least four. -/
theorem dimH_ge_four_of_front_frostman_measures
    (selector : Set MarkedLine)
    (hfrost : HasFrontFrostmanMeasures selector) :
    (4 : ENNReal) ≤ dimH (unitFront selector) := by
  by_contra hnot
  have hlt : dimH (unitFront selector) < (4 : ENNReal) := lt_of_not_ge hnot
  have hfourltTop : (4 : ENNReal) < ⊤ := by norm_num
  have hdimtop : dimH (unitFront selector) ≠ ⊤ :=
    ne_top_of_lt (hlt.trans hfourltTop)
  have hfourtop : (4 : ENNReal) ≠ ⊤ := by norm_num
  have hdimRealLt : (dimH (unitFront selector)).toReal < 4 := by
    exact (ENNReal.toReal_lt_toReal hdimtop hfourtop).2 hlt
  let ε : ℝ := (4 - (dimH (unitFront selector)).toReal) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hε4 : ε < 4 := by
    have hdimRealNonneg : 0 ≤ (dimH (unitFront selector)).toReal :=
      ENNReal.toReal_nonneg
    dsimp [ε]
    linarith
  obtain ⟨mu, hmuProb, hsupport, C, hCtop, hball⟩ :=
    hfrost ε hε hε4
  letI : IsProbabilityMeasure mu := hmuProb
  let dnn : NNReal := ⟨4 - ε, le_of_lt (sub_pos.mpr hε4)⟩
  have hdnnReal : (dnn : ℝ) = 4 - ε := by rfl
  have hballD : ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤
        C * (ENNReal.ofReal r).rpow (dnn : ℝ) := by
    intro x r hr hr1
    rw [hdnnReal]
    exact hball x r hr hr1
  have hhaus :
      MeasureTheory.Measure.hausdorffMeasure (dnn : ℝ)
        (unitFront selector) ≠ 0 :=
    hausdorffMeasure_ne_zero_of_ball_growth
      mu (unitFront selector) hsupport C hCtop dnn
        (by exact_mod_cast (sub_pos.mpr hε4)) hballD
  have hdimLower : (dnn : ENNReal) ≤ dimH (unitFront selector) :=
    le_dimH_of_hausdorffMeasure_ne_zero hhaus
  have hdimRealLower : (dnn : ENNReal).toReal ≤
      (dimH (unitFront selector)).toReal :=
    (ENNReal.toReal_le_toReal (by simp) hdimtop).2 hdimLower
  have hdnnToReal : (dnn : ENNReal).toReal = 4 - ε := by
    change (dnn : ℝ) = 4 - ε
    exact hdnnReal
  have hmidLower : 4 - ε ≤ (dimH (unitFront selector)).toReal := by
    rw [← hdnnToReal]
    exact hdimRealLower
  dsimp [ε] at hmidLower
  linarith

end StickyKakeya4
