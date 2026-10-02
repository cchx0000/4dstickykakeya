import Theorems.Thm_StickyKakeya4_line_tube_inverse_potential
import Theorems.Thm_StickyKakeya4_spacetime_collision_energy
import Theorems.Thm_StickyKakeya4_packet_free_bush_bound
import Theorems.Thm_StickyKakeya4_energy_dimension

/-!
# Moving-focus escape with the original source and marked times

The retained measure is a restriction of the literal marked source/time law.
Focus times remain arbitrary measurable functions of the original slope.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section
namespace StickyKakeya4.MovingFocusEnergyEscape
open PacketFreeBushBound

/-- The literal intercept of the moving-focus family. -/
def movingFocusIntercept (c : E3) (τ : E3 → ℝ) (a : E3) : E3 := c - τ a • a

/-- A fixed separation from each source trajectory's actual focus time. -/
def goodFocusTimes (τ : E3 → ℝ) (g : ℝ) : Set (ℝ × E3) :=
  {p | g ≤ |p.1 - τ p.2|}

/-- A restriction of the actual original marked source/time product. -/
def goodSourceTime (σ : Measure E3) (τ : E3 → ℝ) (u v : ℝ) : Measure (ℝ × E3) :=
  ((volume.restrict (Icc u v)).prod σ).restrict (goodFocusTimes τ ((v-u)/4))

theorem measurable_movingFocusIntercept (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ) :
    Measurable (movingFocusIntercept c τ) := by
  unfold movingFocusIntercept
  fun_prop

theorem measurableSet_goodFocusTimes {τ : E3 → ℝ} (hτ : Measurable τ) (g : ℝ) :
    MeasurableSet (goodFocusTimes τ g) := by
  exact measurableSet_le measurable_const ((measurable_fst.sub (hτ.comp measurable_snd)).abs)

theorem goodSourceTime_le (σ : Measure E3) (τ : E3 → ℝ) (u v : ℝ) :
    goodSourceTime σ τ u v ≤ (volume.restrict (Icc u v)).prod σ :=
  Measure.restrict_le_self

instance goodSourceTime_isFiniteMeasure (σ : Measure E3) [IsFiniteMeasure σ]
    (τ : E3 → ℝ) (u v : ℝ) : IsFiniteMeasure (goodSourceTime σ τ u v) := by
  unfold goodSourceTime
  infer_instance

/-- At least a quarter of the marked interval stays away from any one focus. -/
theorem good_time_fiber_volume_ge (u v τ : ℝ) (huv : u < v) :
    ENNReal.ofReal ((v-u)/4) ≤
      (volume.restrict (Icc u v)) {t | (v-u)/4 ≤ |t-τ|} := by
  have hm : MeasurableSet {t : ℝ | (v-u)/4 ≤ |t-τ|} := by
    exact measurableSet_le measurable_const (measurable_id.sub_const τ).abs
  rw [Measure.restrict_apply hm]
  by_cases hτ : τ ≤ (u+v)/2
  · calc
      _ = volume (Icc (v-(v-u)/4) v) := by rw [Real.volume_Icc]; congr 1; ring
      _ ≤ _ := by
        apply measure_mono
        intro t ht
        refine ⟨?_, ?_⟩
        · exact le_trans (by linarith [ht.1]) (le_abs_self (t-τ))
        · exact ⟨by linarith [ht.1], ht.2⟩
  · calc
      _ = volume (Icc u (u+(v-u)/4)) := by rw [Real.volume_Icc]; congr 1; ring
      _ ≤ _ := by
        apply measure_mono
        intro t ht
        refine ⟨?_, ?_⟩
        · exact le_trans (by linarith [ht.2]) (neg_le_abs (t-τ))
        · exact ⟨ht.1, by linarith [ht.2]⟩

/-- The good-time restriction retains uniformly positive actual product mass. -/
theorem goodSourceTime_mass_ge (σ : Measure E3) [IsFiniteMeasure σ]
    {τ : E3 → ℝ} (hτ : Measurable τ) (u v : ℝ) (huv : u < v) :
    ENNReal.ofReal ((v-u)/4) * σ univ ≤ goodSourceTime σ τ u v univ := by
  rw [goodSourceTime, Measure.restrict_apply_univ,
    Measure.prod_apply_symm (measurableSet_goodFocusTimes hτ _)]
  calc
    _ = ∫⁻ _a, ENNReal.ofReal ((v-u)/4) ∂σ := (lintegral_const _).symm
    _ ≤ _ := lintegral_mono (fun a => good_time_fiber_volume_ge u v (τ a) huv)

theorem goodSourceTime_ne_zero (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≠ 0)
    {τ : E3 → ℝ} (hτ : Measurable τ) (u v : ℝ) (huv : u < v) :
    goodSourceTime σ τ u v ≠ 0 := by
  have hmass := goodSourceTime_mass_ge σ hτ u v huv
  have hpos : 0 < ENNReal.ofReal ((v-u)/4) * σ univ :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      (Measure.measure_univ_pos.mpr hσ).ne'
  intro hzero
  simp only [hzero, Measure.coe_zero, Pi.zero_apply] at hmass
  exact (not_lt_of_ge hmass) hpos

/-- Collision localization uses both signs of the leaf focus displacement. -/
theorem moving_focus_collision_line_localization
    (a a' c : E3) (τ : E3 → ℝ) (t κ g r : ℝ)
    (hκ : 0 < κ) (hg : 0 < g) (hr : 0 ≤ r)
    (hsmall : r ≤ κ*g/4) (ha : κ ≤ ‖a‖) (ha' : ‖a'‖ ≤ 1)
    (hgood : g ≤ |t-τ a|)
    (hc : ‖(movingFocusIntercept c τ a - movingFocusIntercept c τ a') +
      t • (a-a')‖ ≤ 2*r) :
    ‖lineResidual a' 0 a‖ ≤ 2 * (4*r/(κ*g)) := by
  have hkg : 0 < κ*g := mul_pos hκ hg
  let y := (t-τ a) • a
  let z := (t-τ a') • a'
  have heq : (movingFocusIntercept c τ a - movingFocusIntercept c τ a') +
      t • (a-a') = y-z := by dsimp [movingFocusIntercept, y, z]; module
  rw [heq] at hc
  have hy : κ*g ≤ ‖y‖ := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs]
    calc
      κ*g = g*κ := mul_comm _ _
      _ ≤ |t-τ a| * ‖a‖ := mul_le_mul hgood ha hκ.le (abs_nonneg _)
  have hz : κ*g/2 ≤ ‖z‖ := by
    have hh := norm_sub_norm_le y z
    linarith
  have hden : κ*g/2 ≤ |t-τ a'| := by
    have hh : ‖z‖ ≤ |t-τ a'| := by
      dsimp [z]
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) ha'
    exact hz.trans hh
  have hdpos : 0 < |t-τ a'| := lt_of_lt_of_le (by positivity) hden
  have hd : t-τ a' ≠ 0 := abs_pos.mp hdpos
  apply norm_lineResidual_le a' 0 a (4*r/(κ*g))
  refine ⟨(t-τ a)/(t-τ a'), ?_⟩
  have hid : a' - (0 + ((t-τ a)/(t-τ a')) • a) =
      (-(t-τ a')⁻¹) • (y-z) := by
    dsimp [y,z]
    rw [smul_sub, smul_smul, smul_smul]
    field_simp
    module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv]
  calc
    |t-τ a'|⁻¹ * ‖y-z‖ ≤ |t-τ a'|⁻¹ * (2*r) :=
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (abs_nonneg _))
    _ ≤ 4*r/(κ*g) := by
      rw [inv_mul_eq_div, div_le_div_iff₀ hdpos hkg]
      nlinarith



/-- The retained root-time collision event, before averaging over roots. -/
def rootTimeCollision (b : E3 → E3) (τ : E3 → ℝ) (a : E3) (g r : ℝ) :
    Set (ℝ × E3) :=
  {p | g ≤ |p.1-τ a| ∧ ‖(b a-b p.2)+p.1 • (a-p.2)‖ ≤ 2*r}

theorem measurableSet_rootTimeCollision {b : E3 → E3} (hb : Measurable b)
    (τ : E3 → ℝ) (a : E3) (g r : ℝ) :
    MeasurableSet (rootTimeCollision b τ a g r) := by
  have hc : Measurable (fun p : ℝ × E3 => ‖(b a-b p.2)+p.1 • (a-p.2)‖) := by fun_prop
  exact (measurableSet_le measurable_const
    (measurable_fst.sub_const (τ a)).abs).inter
      (measurableSet_le hc measurable_const)

/-- Tonelli identifies the original row integral with the actual collision event. -/
theorem rootTimeCollision_mass_eq (σ : Measure E3) [IsFiniteMeasure σ]
    {b : E3 → E3} (hb : Measurable b) (τ : E3 → ℝ) (a : E3) (g r u v : ℝ) :
    ((volume.restrict (Icc u v)).prod σ) (rootTimeCollision b τ a g r) =
      ∫⁻ t in Icc u v, {t | g ≤ |t-τ a|}.indicator
        (fun t => σ {a' | ‖(b a-b a')+t • (a-a')‖ ≤ 2*r}) t := by
  rw [Measure.prod_apply (measurableSet_rootTimeCollision hb τ a g r)]
  apply lintegral_congr
  intro t
  by_cases ht : g ≤ |t-τ a|
  · simp [rootTimeCollision, ht]
  · simp [rootTimeCollision, ht]

/-- The collision-time factor and the root-only line tube are combined before
integrating any roots. No time-dependent slope law is introduced. -/
theorem rootTimeCollision_mass_le_line_potential
    (σ : Measure E3) [IsFiniteMeasure σ]
    (hunit : ∀ᵐ a' ∂σ, ‖a'‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (a : E3) (κ g r u v : ℝ) (hκ : 0 < κ) (hg : 0 < g)
    (hr : 0 < r) (hsmall : r ≤ κ*g/4) (ha : κ ≤ ‖a‖) :
    ((volume.restrict (Icc u v)).prod σ)
      (rootTimeCollision (movingFocusIntercept c τ) τ a g r) ≤
      ENNReal.ofReal (4*r) *
        ∫⁻ a' in {a' | ‖lineResidual a' 0 a‖ ≤ 2*(4*r/(κ*g))},
          (ENNReal.ofReal ‖a'-a‖)⁻¹ ∂σ := by
  classical
  let b := movingFocusIntercept c τ
  let T : Set E3 := {a' | ‖lineResidual a' 0 a‖ ≤ 2*(4*r/(κ*g))}
  have hb : Measurable b := measurable_movingFocusIntercept c hτ
  have hT : MeasurableSet T := measurableSet_le
    (measurable_lineResidual _ _ _ measurable_id measurable_const measurable_const).norm
      measurable_const
  rw [Measure.prod_apply_symm (measurableSet_rootTimeCollision hb τ a g r)]
  calc
    _ ≤ ∫⁻ a', ENNReal.ofReal (4*r) *
        T.indicator (fun a' => (ENNReal.ofReal ‖a'-a‖)⁻¹) a' ∂σ := by
      apply lintegral_mono_ae
      filter_upwards [hunit] with a' ha'
      by_cases ht : a' ∈ T
      · rw [Set.indicator_of_mem ht]
        by_cases haa : a'=a
        · subst a'
          simp only [sub_self, norm_zero, ENNReal.ofReal_zero, ENNReal.inv_zero]
          rw [ENNReal.mul_top ((ENNReal.ofReal_pos.mpr (by positivity)).ne')]
          exact le_top
        · have hdiff : a-a' ≠ 0 := sub_ne_zero.mpr (Ne.symm haa)
          calc
            _ ≤ volume (collisionTimeFiber (Icc u v) (a-a') (b a-b a') (2*r)) := by
              have hm : MeasurableSet ((fun t : ℝ => (t,a')) ⁻¹' rootTimeCollision b τ a g r) :=
                (measurableSet_rootTimeCollision hb τ a g r).preimage
                  (measurable_id.prodMk measurable_const)
              rw [Measure.restrict_apply hm]
              apply measure_mono
              intro t ht'
              exact ⟨ht'.2, ht'.1.2⟩
            _ ≤ ENNReal.ofReal (2*(2*r)/‖a-a'‖) :=
              collisionTimeFiber_volume_le _ _ _ hdiff _ (by positivity)
            _ = ENNReal.ofReal (4*r) * (ENNReal.ofReal ‖a'-a‖)⁻¹ := by
              rw [show 2*(2*r)=4*r by ring,
                ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr hdiff), div_eq_mul_inv,
                norm_sub_rev a a']
      · rw [Set.indicator_of_notMem ht, mul_zero]
        have he : (fun t : ℝ => (t,a')) ⁻¹' rootTimeCollision b τ a g r = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht'
          apply ht
          exact moving_focus_collision_line_localization a a' c τ t κ g r
            hκ hg hr.le hsmall ha ha' ht'.1 ht'.2
        simp only [he, measure_empty, le_refl]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hT]



/-- The second physical time contributes its full factor `2r`, while the first
physical time is restricted only by its own actual focus label. -/
theorem goodSourceTime_pair_sublevel_le_root_collisions
    (σ : Measure E3) [IsFiniteMeasure σ]
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    {b : E3 → E3} (hb : Measurable b) {τ : E3 → ℝ} (hτ : Measurable τ)
    (u v r : ℝ) (hr : 0 ≤ r) :
    ((goodSourceTime σ τ u v).prod (goodSourceTime σ τ u v))
      {p | ‖slopeSpacetimePoint b p.1-slopeSpacetimePoint b p.2‖ ≤ r} ≤
      ENNReal.ofReal (2*r) * ∫⁻ a,
        ((volume.restrict (Icc u v)).prod σ)
          (rootTimeCollision b τ a ((v-u)/4) r) ∂σ := by
  let η := goodSourceTime σ τ u v
  let μbase := (volume.restrict (Icc u v)).prod σ
  let g := (v-u)/4
  let H : ℝ × E3 → ℝ≥0∞ := fun p =>
    σ {a' | ‖(b p.2-b a')+p.1 • (p.2-a')‖ ≤ 2*r}
  have hH : Measurable H := by
    have hm : MeasurableSet {z : (ℝ × E3) × E3 |
        ‖(b z.1.2-b z.2)+z.1.1 • (z.1.2-z.2)‖ ≤ 2*r} :=
      measurableSet_le (by fun_prop) measurable_const
    exact measurable_measure_prodMk_left (ν := σ) hm
  have hG := measurableSet_goodFocusTimes hτ g
  have hF := measurable_slopeSpacetimePoint b hb
  have hs : MeasurableSet {p : (ℝ × E3) × (ℝ × E3) |
      ‖slopeSpacetimePoint b p.1-slopeSpacetimePoint b p.2‖ ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (2*r) * H p ∂η := by
      apply lintegral_mono
      intro p
      calc
        _ ≤ μbase {q | ‖slopeSpacetimePoint b p-slopeSpacetimePoint b q‖ ≤ r} :=
          goodSourceTime_le σ τ u v _
        _ ≤ _ := by
          simpa only [H, one_add_one_eq_two] using
            spacetime_source_row_mass_le σ b hb p.2 p.1 u v 1 r hr hunit
    _ = ENNReal.ofReal (2*r) * ∫⁻ p, H p ∂η :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2*r) *
        ∫⁻ a, ∫⁻ t in Icc u v, (goodFocusTimes τ g).indicator H (t,a) ∂volume ∂σ := by
      congr 1
      change (∫⁻ p in goodFocusTimes τ g, H p ∂μbase) = _
      rw [← lintegral_indicator hG,
        lintegral_prod_symm' _ (hH.indicator hG)]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro a
      rw [rootTimeCollision_mass_eq σ hb τ a g r u v]
      apply lintegral_congr
      intro t
      by_cases ht : g ≤ |t-τ a| <;> simp [goodFocusTimes, H, ht]



/-- Integration of a uniform tube-potential estimate gives the actual
four-dimensional pair sublevel power. This is an intermediate quantitative
lemma; the geometric potential estimate is supplied below. -/
theorem goodSourceTime_pair_sublevel_le_of_potential_bound
    (σ : Measure E3) [IsFiniteMeasure σ]
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v ε : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖)
    (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (hpot : ∀ a : E3, ‖a‖ ≤ 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∫⁻ a' in {a' | ‖lineResidual a' 0 a‖ ≤ 2*δ},
        (ENNReal.ofReal ‖a'-a‖)⁻¹ ∂σ) ≤ K * ENNReal.ofReal (δ^(2-ε))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < κ*((v-u)/4)/4 →
      ((goodSourceTime σ τ u v).prod (goodSourceTime σ τ u v))
        {p | ‖slopeSpacetimePoint (movingFocusIntercept c τ) p.1-
          slopeSpacetimePoint (movingFocusIntercept c τ) p.2‖ ≤ r} ≤
        ENNReal.ofReal (C*r^(4-ε)) := by
  let g := (v-u)/4
  let L := 4/(κ*g)
  let m := (σ univ).toReal
  let C := 8*K.toReal*m*L^(2-ε)
  have hg : 0 < g := by dsimp [g]; linarith
  have hkg : 0 < κ*g := mul_pos hκ hg
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C,m]; positivity
  refine ⟨C,hC,?_⟩
  intro r hr hsmall
  have hδ : 0 < 4*r/(κ*g) := by positivity
  have hδ1 : 4*r/(κ*g) ≤ 1 := by
    rw [div_le_iff₀ hkg]
    dsimp [g] at *
    linarith
  have hrow : (∫⁻ a,
      ((volume.restrict (Icc u v)).prod σ)
        (rootTimeCollision (movingFocusIntercept c τ) τ a g r) ∂σ) ≤
      (ENNReal.ofReal (4*r) * (K * ENNReal.ofReal ((4*r/(κ*g))^(2-ε)))) * σ univ := by
    rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hann,hunit] with a ha hau
    exact (rootTimeCollision_mass_le_line_potential σ hunit c hτ a κ g r u v
      hκ hg hr hsmall.le ha).trans (mul_le_mul_right (hpot a hau _ hδ hδ1) _)
  calc
    _ ≤ ENNReal.ofReal (2*r) * ∫⁻ a,
        ((volume.restrict (Icc u v)).prod σ)
          (rootTimeCollision (movingFocusIntercept c τ) τ a g r) ∂σ :=
      goodSourceTime_pair_sublevel_le_root_collisions σ hunit
        (measurable_movingFocusIntercept c hτ) hτ u v r hr.le
    _ ≤ ENNReal.ofReal (2*r) *
        ((ENNReal.ofReal (4*r) * (K * ENNReal.ofReal ((4*r/(κ*g))^(2-ε)))) * σ univ) :=
      mul_le_mul_right hrow _
    _ = ENNReal.ofReal (C*r^(4-ε)) := by
      rw [← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_toReal (measure_ne_top σ univ)]
      repeat' rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hscale : 4*r/(κ*g) = L*r := by dsimp [L]; ring
      rw [hscale, Real.mul_rpow hL.le hr.le,
        show (4-ε : ℝ) = (2-ε)+1+1 by ring,
        Real.rpow_add hr, Real.rpow_add hr, Real.rpow_one]
      dsimp [C,m]
      ring



/-- The sub-four pair sublevel bound is proved for the actual fixed good-time
restriction of the original moving-focus source. -/
theorem moving_focus_pair_sublevel_power
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v ε : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r < κ*((v-u)/4)/4 →
      ((goodSourceTime σ τ u v).prod (goodSourceTime σ τ u v))
        {p | ‖slopeSpacetimePoint (movingFocusIntercept c τ) p.1-
          slopeSpacetimePoint (movingFocusIntercept c τ) p.2‖ ≤ r} ≤
        ENNReal.ofReal (C*r^(4-ε)) := by
  obtain ⟨K,hK,hpot⟩ :=
    LineTubeInversePotential.exists_uniform_line_tube_inverse_potential ε hε hε1
  exact goodSourceTime_pair_sublevel_le_of_potential_bound σ hunit c hτ
    κ u v ε hκ huv hann K hK (hpot σ hσ hunit)

/-- Every positive inverse-energy exponent below four is finite for the same
literal restricted source/time law. The source does not depend on the exponent. -/
theorem moving_focus_finite_pair_energy
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v s : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hs : 0 < s) (hs4 : s < 4) :
    (∫⁻ p : (ℝ × E3) × (ℝ × E3),
      (ENNReal.ofReal ‖slopeSpacetimePoint (movingFocusIntercept c τ) p.1-
        slopeSpacetimePoint (movingFocusIntercept c τ) p.2‖)^(-s)
      ∂((goodSourceTime σ τ u v).prod (goodSourceTime σ τ u v))) < ∞ := by
  let ε := min (1/2 : ℝ) ((4-s)/2)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hsε : s < 4-ε := by
    have hh := min_le_right (1/2 : ℝ) ((4-s)/2)
    dsimp [ε]
    linarith
  obtain ⟨C,hC,hsub⟩ := moving_focus_pair_sublevel_power σ hσ hunit c hτ
    κ u v ε hκ huv hann hε hε1
  have hF := measurable_slopeSpacetimePoint (movingFocusIntercept c τ)
    (measurable_movingFocusIntercept c hτ)
  exact finite_inverse_energy_of_local_sublevel_power
    ((goodSourceTime σ τ u v).prod (goodSourceTime σ τ u v))
    _ (by fun_prop) (fun _ => norm_nonneg _) C (4-ε) s (κ*((v-u)/4)/4)
    hC hs hsε (by positivity) hsub

/-- The finite-energy measure is the actual spacetime pushforward, with the
original physical time coordinate and original moving-focus intercept. -/
theorem moving_focus_finite_front_energy
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v s : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hs : 0 < s) (hs4 : s < 4) :
    (∫⁻ x, EnergyDimension.inverseDistancePotential
      ((goodSourceTime σ τ u v).map (slopeSpacetimePoint (movingFocusIntercept c τ))) s x
      ∂(goodSourceTime σ τ u v).map (slopeSpacetimePoint (movingFocusIntercept c τ))) < ∞ := by
  unfold EnergyDimension.inverseDistancePotential
  rw [map_inverse_energy_eq_distance_pair_integral _ _
    (measurable_slopeSpacetimePoint _ (measurable_movingFocusIntercept c hτ))]
  simpa only [dist_eq_norm] using
    moving_focus_finite_pair_energy σ hσ hunit c hτ κ u v s hκ huv hann hs hs4

/-- A genuine supported Frostman measure is extracted on the literal original
front, for every exponent below four. Only the original source is restricted. -/
theorem moving_focus_original_front_frostman
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) (hσpos : σ ≠ 0)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v s : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hs : 0 < s) (hs4 : s < 4)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint (movingFocusIntercept c τ))) Kᶜ = 0) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C*ENNReal.ofReal r^s := by
  have hF := measurable_slopeSpacetimePoint (movingFocusIntercept c τ)
    (measurable_movingFocusIntercept c hτ)
  have hm : (goodSourceTime σ τ u v).map (slopeSpacetimePoint (movingFocusIntercept c τ)) ≠ 0 :=
    (Measure.map_ne_zero_iff hF.aemeasurable).mpr
      (goodSourceTime_ne_zero σ hσpos hτ u v huv)
  have hk : ((goodSourceTime σ τ u v).map
      (slopeSpacetimePoint (movingFocusIntercept c τ))) Kᶜ = 0 :=
    le_antisymm (((Measure.map_mono (goodSourceTime_le σ τ u v) hF) Kᶜ).trans_eq hsupport) bot_le
  exact EnergyDimension.exists_supported_frostman_probability_of_finite_energy _ hm K hk s hs
    (moving_focus_finite_front_energy σ hσ hunit c hτ κ u v s hκ huv hann hs hs4)



/-- The original front has full Hausdorff dimension. No compactness assumption
is needed once its literal source/time pushforward is carried by it. -/
theorem moving_focus_original_front_dimH_eq_four
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) (hσpos : σ ≠ 0)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint (movingFocusIntercept c τ))) Kᶜ = 0) :
    dimH K = 4 := by
  apply le_antisymm
  · calc
      dimH K ≤ dimH (univ : Set E4) := dimH_mono (subset_univ _)
      _ = 4 := by simp [E4, Real.dimH_univ_eq_finrank]
  · by_contra hn
    have hlt : dimH K < (4 : ℝ≥0∞) := lt_of_not_ge hn
    have htop : dimH K ≠ ⊤ := ne_top_of_lt (hlt.trans (show (4 : ℝ≥0∞) < ⊤ by norm_num))
    have hdlt : (dimH K).toReal < 4 :=
      (ENNReal.toReal_lt_toReal htop (by norm_num)).mpr hlt
    let s := ((dimH K).toReal+4)/2
    have hs : 0 < s := by dsimp [s]; linarith [ENNReal.toReal_nonneg (a := dimH K)]
    have hs4 : s < 4 := by dsimp [s]; linarith
    obtain ⟨ν,hν,hνK,C,hC,hball⟩ :=
      moving_focus_original_front_frostman σ hσ hσpos hunit c hτ
        κ u v s hκ huv hann hs hs4 K hsupport
    let : IsProbabilityMeasure ν := hν
    let snn : NNReal := ⟨s,hs.le⟩
    have hsnn : 0 < snn := hs
    have hhaus := hausdorffMeasure_ne_zero_of_ball_growth ν K hνK C hC snn hsnn
      (fun x r hr _ => hball x r hr)
    have hdim : (snn : ℝ≥0∞) ≤ dimH K := le_dimH_of_hausdorffMeasure_ne_zero hhaus
    have hreal : s ≤ (dimH K).toReal := by
      exact (ENNReal.toReal_le_toReal (by simp) htop).mpr hdim
    dsimp [s] at hreal
    linarith

/-- An almost-everywhere moving-focus identity identifies the literal original
front law exactly, rather than changing either the source or its time labels. -/
theorem original_spacetime_map_eq_of_ae_moving_focus
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3)
    (c : E3) (τ : E3 → ℝ) (u v : ℝ)
    (hrep : ∀ᵐ a ∂σ, b a = movingFocusIntercept c τ a) :
    (((volume.restrict (Icc u v)).prod σ).map (slopeSpacetimePoint b)) =
      (((volume.restrict (Icc u v)).prod σ).map
        (slopeSpacetimePoint (movingFocusIntercept c τ))) := by
  apply Measure.map_congr
  have hh : ∀ᵐ p ∂(volume.restrict (Icc u v)).prod σ,
      b p.2 = movingFocusIntercept c τ p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hrep
  filter_upwards [hh] with p hp
  simp only [slopeSpacetimePoint,hp]

/-- Final original-input statement: the selector is the given `b`,
and the moving-focus representation is required only on its original source.
The front `K` is kept literally unchanged. -/
theorem original_front_dimH_eq_four_of_ae_moving_focus
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) (hσpos : σ ≠ 0)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (b : E3 → E3) (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖)
    (hrep : ∀ᵐ a ∂σ, b a = c-τ a • a)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint b)) Kᶜ = 0) : dimH K = 4 := by
  have hmap := original_spacetime_map_eq_of_ae_moving_focus σ b c τ u v hrep
  rw [hmap] at hsupport
  exact moving_focus_original_front_dimH_eq_four σ hσ hσpos hunit c hτ
    κ u v hκ huv hann K hsupport



/-- Almost-everywhere representation also preserves the good-time pushforward
itself, not merely a resulting dimension inequality. -/
theorem original_goodSourceTime_map_eq_of_ae_moving_focus
    (σ : Measure E3) [IsFiniteMeasure σ] (b : E3 → E3)
    (c : E3) (τ : E3 → ℝ) (u v : ℝ)
    (hrep : ∀ᵐ a ∂σ, b a = movingFocusIntercept c τ a) :
    ((goodSourceTime σ τ u v).map (slopeSpacetimePoint b)) =
      ((goodSourceTime σ τ u v).map
        (slopeSpacetimePoint (movingFocusIntercept c τ))) := by
  apply Measure.map_congr
  have hh : ∀ᵐ p ∂(volume.restrict (Icc u v)).prod σ,
      b p.2 = movingFocusIntercept c τ p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hrep
  have hh' : ∀ᵐ p ∂goodSourceTime σ τ u v,
      b p.2 = movingFocusIntercept c τ p.2 := ae_restrict_of_ae hh
  filter_upwards [hh'] with p hp
  simp only [slopeSpacetimePoint,hp]

/-- Finite energy of the original selector's literal restricted spacetime law,
under only an almost-everywhere moving-focus identity. -/
theorem original_finite_front_energy_of_ae_moving_focus
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (b : E3 → E3) (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v s : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hs : 0 < s) (hs4 : s < 4)
    (hrep : ∀ᵐ a ∂σ, b a = c-τ a • a) :
    (∫⁻ x, EnergyDimension.inverseDistancePotential
      ((goodSourceTime σ τ u v).map (slopeSpacetimePoint b)) s x
      ∂(goodSourceTime σ τ u v).map (slopeSpacetimePoint b)) < ∞ := by
  rw [original_goodSourceTime_map_eq_of_ae_moving_focus σ b c τ u v hrep]
  exact moving_focus_finite_front_energy σ hσ hunit c hτ κ u v s hκ huv hann hs hs4

/-- Supported Frostman output for the original selector `b` and original front. -/
theorem original_front_frostman_of_ae_moving_focus
    (σ : Measure E3) [IsFiniteMeasure σ] (hσ : σ ≤ volume) (hσpos : σ ≠ 0)
    (hunit : ∀ᵐ a ∂σ, ‖a‖ ≤ 1)
    (b : E3 → E3) (c : E3) {τ : E3 → ℝ} (hτ : Measurable τ)
    (κ u v s : ℝ) (hκ : 0 < κ) (huv : u < v)
    (hann : ∀ᵐ a ∂σ, κ ≤ ‖a‖) (hs : 0 < s) (hs4 : s < 4)
    (hrep : ∀ᵐ a ∂σ, b a = c-τ a • a)
    (K : Set E4)
    (hsupport : (((volume.restrict (Icc u v)).prod σ).map
      (slopeSpacetimePoint b)) Kᶜ = 0) :
    ∃ ν : Measure E4, IsProbabilityMeasure ν ∧ ν Kᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x r, 0 < r →
        ν (Metric.ball x r) ≤ C*ENNReal.ofReal r^s := by
  rw [original_spacetime_map_eq_of_ae_moving_focus σ b c τ u v hrep] at hsupport
  exact moving_focus_original_front_frostman σ hσ hσpos hunit c hτ
    κ u v s hκ huv hann hs hs4 K hsupport

end StickyKakeya4.MovingFocusEnergyEscape
