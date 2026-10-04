import Theorems.Thm_StickyKakeya4_native_parent_spines
import Theorems.Thm_StickyKakeya4_parentwise_angular_selection
import Theorems.Thm_StickyKakeya4_dyadic_alignment_parameters

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeAngularChartSelection

open NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open ActualTubeFootprintProfiles DisjointProfileEpochs
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A genuine sup-unit direction supplies one of the two literal coordinate charts. -/
def chart (T : TubeData 1) : Fin 2 := if |T.direction 0| = 1 then 0 else 1

lemma chart_unit (T : TubeData 1) : |T.direction (chart T)| = 1 := by
  unfold chart
  split_ifs with h
  · exact h
  · obtain ⟨i, hi⟩ := T.unit.2
    fin_cases i
    · exact (h hi).elim
    · exact hi

def chartPerm (j : Fin 2) : Equiv.Perm (Fin 2) := Equiv.swap 0 j

def chartPoint (j : Fin 2) (p : Plane) : Plane := p ∘ chartPerm j

def chartTube (j : Fin 2) (T : TubeData 1) : TubeData 1 where
  center := chartPoint j T.center
  direction := chartPoint j T.direction
  unit := ⟨fun i => T.unit.1 _, by
    obtain ⟨i, hi⟩ := T.unit.2
    exact ⟨(chartPerm j).symm i, by simpa [chartPoint] using hi⟩⟩

lemma chartPoint_zero (j : Fin 2) (p : Plane) : chartPoint j p 0 = p j := by
  simp [chartPoint, chartPerm]

lemma chartPoint_involutive (j : Fin 2) (p : Plane) : chartPoint j (chartPoint j p) = p := by
  funext k
  simp [chartPoint, chartPerm]

lemma chartTube_involutive (j : Fin 2) (T : TubeData 1) : chartTube j (chartTube j T) = T := by
  cases T
  simp only [chartTube, chartPoint_involutive]

lemma chartTube_unit_zero (j : Fin 2) (T : TubeData 1) (h : |T.direction j| = 1) :
    |(chartTube j T).direction 0| = 1 := by
  simpa only [chartTube, chartPoint_zero] using h

lemma chartPoint_injective (j : Fin 2) : Function.Injective (chartPoint j) := by
  intro p q h
  funext i
  have hh := congrFun h ((chartPerm j).symm i)
  simpa [chartPoint] using hh

lemma chartPoint_dist (j : Fin 2) (p q : Plane) :
    dist (chartPoint j p) (chartPoint j q) = dist p q := by
  exact (IsometryEquiv.piCongrLeft' (Y := fun _ : Fin 2 => ℝ) (chartPerm j).symm).dist_eq p q

lemma chart_carrierBall (j : Fin 2) (A : Finset Plane) (p : Plane) (r : ℝ) :
    carrierBall (A.image (chartPoint j)) (chartPoint j p) r =
      (carrierBall A p r).image (chartPoint j) := by
  ext x
  simp only [mem_carrierBall, Finset.mem_image]
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hdist⟩
    exact ⟨q, ⟨hq, by simpa only [chartPoint_dist] using hdist⟩, rfl⟩
  · rintro ⟨q, ⟨hq, hdist⟩, rfl⟩
    exact ⟨⟨q, hq, rfl⟩, by simpa only [chartPoint_dist] using hdist⟩

lemma chart_AD (j : Fin 2) (A : Finset Plane) (δ K t : ℝ) (h : ADBounds A δ K t) :
    ADBounds (A.image (chartPoint j)) δ K t := by
  intro x hx r hrδ hrone
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  rw [chart_carrierBall, Finset.card_image_of_injective _ (chartPoint_injective j)]
  exact h p hp r hrδ hrone

lemma chart_inTube_iff (j : Fin 2) (T : TubeData 1) (ρ τ : ℝ) (p : Plane) :
    InTube (chartTube j T) ρ τ (chartPoint j p) ↔ InTube T ρ τ p := by
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, fun i => by simpa [chartTube, chartPoint] using he ((chartPerm j).symm i)⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, fun i => he (chartPerm j i)⟩

lemma chart_grid {α : Type*} (j : Fin 2) (p : α → Plane) (r : ℝ) (a : α) :
    grid (chartPoint j ∘ p) r a = grid p r a ∘ chartPerm j := rfl

lemma chart_grid_card {α : Type*} (j : Fin 2) (p : α → Plane) (r : ℝ) (S : Finset α) :
    (S.image (grid (chartPoint j ∘ p) r)).card = (S.image (grid p r)).card := by
  classical
  have hinj : Function.Injective (fun k : GridLabel 1 => k ∘ chartPerm j) := by
    intro k l h
    funext i
    have hh := congrFun h ((chartPerm j).symm i)
    simpa using hh
  have he : S.image (grid (chartPoint j ∘ p) r) =
      (S.image (grid p r)).image (fun k => k ∘ chartPerm j) := by
    rw [Finset.image_image]
    rfl
  rw [he, Finset.card_image_of_injective _ hinj]

lemma chart_trace {α : Type*} [Fintype α] [DecidableEq α] (j : Fin 2)
    (p : α → Plane) (ρ τ : ℝ) (T : TubeData 1) :
    trace (chartPoint j ∘ p) ρ τ (chartTube j T) = trace p ρ τ T := by
  ext a
  simp only [mem_trace, Function.comp_apply, chart_inTube_iff]

lemma chart_trace_inverse {α : Type*} [Fintype α] [DecidableEq α] (j : Fin 2)
    (p : α → Plane) (ρ τ : ℝ) (T : TubeData 1) :
    trace (chartPoint j ∘ p) ρ τ T = trace p ρ τ (chartTube j T) := by
  simpa only [chartTube_involutive] using chart_trace j p ρ τ (chartTube j T)

lemma chart_footprints {α : Type*} [Fintype α] [DecidableEq α] (j : Fin 2)
    (p : α → Plane) (ρ τ : ℝ) : footprints (chartPoint j ∘ p) ρ τ = footprints p ρ τ := by
  ext W
  simp only [mem_footprints]
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨chartTube j T, chart_trace_inverse j p ρ τ T⟩
  · rintro ⟨T, rfl⟩
    exact ⟨chartTube j T, (chart_trace j p ρ τ T).symm⟩

lemma chart_profile {α : Type*} [Fintype α] [DecidableEq α] (j : Fin 2)
    (p : α → Plane) (ρ τ : ℝ) (E : Finset α) :
    coverProfile (chartPoint j ∘ p) ρ τ E = coverProfile p ρ τ E := by
  unfold coverProfile
  rw [chart_footprints]
  apply Finset.sup_congr rfl
  intro W _hW
  exact chart_grid_card j p ρ (E ∩ W)

def chartSlope (j : Fin 2) (T : TubeData 1) : ℝ :=
  (chartTube j T).direction 1 / (chartTube j T).direction 0

lemma chartSlope_bound (j : Fin 2) (T : TubeData 1) (h : |T.direction j| = 1) :
    |chartSlope j T| ≤ 1 := by
  unfold chartSlope
  rw [abs_div, chartTube_unit_zero j T h, div_one]
  exact (chartTube j T).unit.1 1

/-- Select whole genuine fibers by their actual maximizing direction coordinate.
The retained quantity is the number of ORIGINAL points in their union. -/
theorem exists_heavy_chart {α : Type*} [DecidableEq α]
    (Fs : List (Finset α)) (T : Finset α → TubeData 1) :
    ∃ j : Fin 2, ∃ Gs : List (Finset α),
      Gs = Fs.filter (fun F => chart (T F) = j) ∧
      (support Fs).card ≤ 2 * (support Gs).card ∧
      (∀ F ∈ Gs, F ∈ Fs ∧ |(T F).direction j| = 1) := by
  classical
  obtain ⟨j, hj⟩ := SeparatedAlignmentPatches.maximum_weight_color
    (support Fs) (fun _ => 1) (fun a => chart (T (owner Fs a)))
  have hj' : (support Fs).card ≤
      2 * ((support Fs).filter (fun a => chart (T (owner Fs a)) = j)).card := by
    simpa using hj
  let Gs := Fs.filter (fun F => chart (T F) = j)
  have hsub : (support Fs).filter (fun a => chart (T (owner Fs a)) = j) ⊆ support Gs := by
    intro a ha
    obtain ⟨haF, haC⟩ := Finset.mem_filter.mp ha
    have ho := owner_spec Fs haF
    exact (mem_support Gs a).mpr ⟨owner Fs a, List.mem_filter.mpr ⟨ho.1, by simpa using haC⟩, ho.2⟩
  refine ⟨j, Gs, rfl, hj'.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)), ?_⟩
  intro F hF
  obtain ⟨hFF, hC⟩ := List.mem_filter.mp hF
  have hC' : chart (T F) = j := by simpa using hC
  exact ⟨hFF, hC' ▸ chart_unit (T F)⟩

def angleLabel (n : ℕ) (θ : ℝ) : ℤ := ⌊(n : ℝ) * θ⌋

lemma angleLabel_bounds (n : ℕ) {θ : ℝ} (hθ : |θ| ≤ 1) :
    -(n : ℤ) ≤ angleLabel n θ ∧ angleLabel n θ ≤ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hl, hu⟩ := abs_le.mp hθ
  constructor
  · apply Int.le_floor.mpr
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hl hn]
  · have h := Int.floor_mono (mul_le_mul_of_nonneg_left hu hn)
    simpa [angleLabel] using h

lemma angle_menu_card {α : Type*} (S : Finset α) (θ : α → ℝ) (n : ℕ)
    (hθ : ∀ a ∈ S, |θ a| ≤ 1) : (S.image (fun a => angleLabel n (θ a))).card ≤ 2 * n + 1 := by
  classical
  have hsub : S.image (fun a => angleLabel n (θ a)) ⊆ Finset.Icc (-(n : ℤ)) n := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr (angleLabel_bounds n (hθ a ha))
  have hc := Finset.card_le_card hsub
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  rwa [hi] at hc

def angularBudget (n m : ℕ) : ℕ := ⌈((2 * n + 1 : ℕ) : ℝ) ^ (m : ℝ)⁻¹⌉₊

lemma angularBudget_power (n : ℕ) {m : ℕ} (hm : 0 < m) :
    2 * n + 1 ≤ angularBudget n m ^ m := by
  have hx : (0 : ℝ) ≤ (2 * n + 1 : ℕ) := Nat.cast_nonneg _
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hx _) (Nat.le_ceil (((2 * n + 1 : ℕ) : ℝ) ^ (m : ℝ)⁻¹)) m
  rw [Real.rpow_inv_natCast_pow hx hm.ne'] at hp
  exact_mod_cast hp

def workingLevel (lo M m k : ℕ) : ℕ := lo + DyadicAlignmentParameters.level M m k

def angularResolution (M m : ℕ) : ℕ := 2 ^ DyadicAlignmentParameters.gap M m

lemma angularResolution_pos (M m : ℕ) : 0 < angularResolution M m := by
  unfold angularResolution
  positivity

lemma workingLevel_mono (lo M m : ℕ) : Monotone (workingLevel lo M m) := by
  intro i j hij
  exact Nat.add_le_add_left (DyadicAlignmentParameters.level_monotone M m hij) lo

lemma workingLevel_bounds (lo hi m k : ℕ) (hlohi : lo ≤ hi) (hm : 0 < m) (hk : k ≤ m) :
    lo ≤ workingLevel lo (hi - lo) m k ∧ workingLevel lo (hi - lo) m k ≤ hi := by
  have h := DyadicAlignmentParameters.level_le_endpoint (hi - lo) m k hm hk
  unfold workingLevel
  omega

/-- The literal angular resolution works for every candidate pair before the
winning pair is selected: gamma=1/n and gamma*b<=a. -/
lemma workingLevel_angle_scale {δ : ℝ} (hδ : 0 < δ) (lo M k : ℕ) {m : ℕ} (hm : 0 < m) :
    (1 / (angularResolution M m : ℝ)) * scale δ (workingLevel lo M m (k + 1)) ≤
      scale δ (workingLevel lo M m k) := by
  have hlevel : workingLevel lo M m (k + 1) ≤
      workingLevel lo M m k + DyadicAlignmentParameters.gap M m := by
    have h := DyadicAlignmentParameters.adjacent_level_le M m k hm
    unfold workingLevel
    omega
  have hscale := scale_mono hδ.le hlevel
  rw [scale_add] at hscale
  have hn : (0 : ℝ) < angularResolution M m := by exact_mod_cast angularResolution_pos M m
  have heq : (2 : ℝ) ^ DyadicAlignmentParameters.gap M m = angularResolution M m := by
    simp only [angularResolution, Nat.cast_pow, Nat.cast_ofNat]
  rw [heq] at hscale
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ hn).mpr hscale

def selectedSlope (n : ℕ) (k : ℤ) : ℝ := max (-1) (min 1 ((k : ℝ) / n))

lemma selectedSlope_bound (n : ℕ) (k : ℤ) : |selectedSlope n k| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma angleLabel_close {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ : |θ| ≤ 1) :
    |θ - selectedSlope n (angleLabel n θ)| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hl, hu⟩ := angleLabel_bounds n hθ
  have hlow : (-1 : ℝ) ≤ (angleLabel n θ : ℝ) / n := by
    apply (le_div_iff₀ hnR).mpr
    rw [neg_one_mul]
    exact_mod_cast hl
  have hupp : (angleLabel n θ : ℝ) / n ≤ 1 := by
    apply (div_le_iff₀ hnR).mpr
    simpa using (Int.cast_le.mpr hu : (angleLabel n θ : ℝ) ≤ (n : ℤ))
  rw [selectedSlope, min_eq_right hupp, max_eq_right hlow]
  have hlo := Int.floor_le ((n : ℝ) * θ)
  have hhi := Int.lt_floor_add_one ((n : ℝ) * θ)
  change (angleLabel n θ : ℝ) ≤ (n : ℝ) * θ at hlo
  change (n : ℝ) * θ < (angleLabel n θ : ℝ) + 1 at hhi
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hnR).mpr (by simpa [mul_comm] using hlo)))]
  apply (le_div_iff₀ hnR).mpr
  have hcancel : ((angleLabel n θ : ℝ) / n) * n = angleLabel n θ := div_mul_cancel₀ _ hnR.ne'
  nlinarith only [hhi, hcancel]

lemma grid_scale_ancestor {α : Type*} (p : α → Plane) {δ : ℝ}
    (i k : ℕ) (a : α) :
    grid p (scale δ (i + k)) a = fun j => grid p (scale δ i) a j / (2 : ℕ) ^ k := by
  funext j
  change ⌊p a j / scale δ (i + k)⌋ = ⌊p a j / scale δ i⌋ / (2 : ℕ) ^ k
  rw [scale_add, ← div_div]
  norm_cast
  rw [Int.floor_div_natCast]

lemma grid_scale_nested {α : Type*} (p : α → Plane) {δ : ℝ} {i k : ℕ}
    (hik : i ≤ k) {a b : α} (h : grid p (scale δ i) a = grid p (scale δ i) b) :
    grid p (scale δ k) a = grid p (scale δ k) b := by
  have hk : k = i + (k - i) := by omega
  rw [hk, grid_scale_ancestor, grid_scale_ancestor, h]

lemma uniform_cell_card {α β : Type*} [DecidableEq β] (B : Finset α)
    (f : α → β) (Q : ℕ) (h : UniformPartition B f Q) {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) :
    (AngularMenuStabilization.cell B f (f a)).card ≤
      Q ^ 2 * (AngularMenuStabilization.cell B f (f b)).card := by
  simpa only [unit_degree_eq_card, AngularMenuStabilization.cell] using h a b ha hb

lemma uniform_joint_card {α β : Type*} [DecidableEq β] (B : Finset α)
    (f : α → β) (θ : α → ℤ) (Q : ℕ)
    (h : UniformPartition B (fun a => (f a, θ a)) Q) {a b : α}
    (ha : a ∈ B) (hb : b ∈ B) :
    (AngularMenuStabilization.joint B f θ (f a) (θ a)).card ≤
      Q ^ 2 * (AngularMenuStabilization.joint B f θ (f b) (θ b)).card := by
  have hh := h a b ha hb
  rw [unit_degree_eq_card, unit_degree_eq_card] at hh
  simpa only [AngularMenuStabilization.joint, Prod.mk.injEq] using hh

/-- A literal angular grid supplies the menu budget; the same core supplies
both uniformities. The adjacent scale and every parent's slope are constructed.
The genuine spine stays at width 2rho and contacts each retained point in its
original child cell. No tube membership of the retained point is asserted. -/
theorem select_parent_core_angles (A : Finset Plane) (Fs : List (Finset A))
    {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t N E₀)
    (T : Finset A → TubeData 1) (j : Fin 2)
    (hchart : ∀ F ∈ Fs, |(T F).direction j| = 1)
    (htube : ∀ F ∈ Fs, ∀ a ∈ F,
      InTube (T F) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a))
    {C₀ m Q L n Bang : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hbudget : 2 * n + 1 ≤ Bang ^ m) (level : ℕ → ℕ)
    (hlevel : ∀ i, i < m → level i ≤ level (i + 1))
    (B : ParentCore A Fs D C₀ Q L (fun k : Fin (m + 1) => level k)
      (fun _ a => angleLabel n (chartSlope j (T (owner Fs a))))) :
    ∃ i < m, ∃ Ω ⊆ B.points, Ω.Nonempty ∧ ∃ α : GridLabel 1 → ℝ,
      (∀ c, |α c| ≤ 1) ∧
      (∀ c, (B.points.filter (fun q => grid (position A) (scale δ (level (i + 1))) q = c)).card ≤
        Q ^ 2 * Q ^ 2 * Bang *
          (Ω.filter (fun q => grid (position A) (scale δ (level (i + 1))) q = c)).card) ∧
      B.points.card ≤ Q ^ 2 * Q ^ 2 * Bang * Ω.card ∧
      Ω.image (grid (position A) (scale δ (level (i + 1)))) =
        B.points.image (grid (position A) (scale δ (level (i + 1)))) ∧
      (∀ q r, q ∈ Ω → r ∈ B.points →
        grid (position A) (scale δ (level i)) r = grid (position A) (scale δ (level i)) q → r ∈ Ω) ∧
      (∀ q ∈ Ω, ∃ z ∈ Ω,
        grid (position A) (scale δ (level i)) z = grid (position A) (scale δ (level i)) q ∧
        |chartSlope j (T (owner Fs z)) - α (grid (position A) (scale δ (level (i + 1))) q)| ≤ 1 / n ∧
        InTube (T (owner Fs z)) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A z) ∧
        (∀ a ∈ parentSpine A Fs B.points (scale δ (level (i + 1))) z,
          a ∈ B.points ∧
          grid (position A) (scale δ (level (i + 1))) a = grid (position A) (scale δ (level (i + 1))) q ∧
          InTube (T (owner Fs z)) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a)) ∧
        spineConstant N (m + 1) Q L K t D.loss *
          (scale δ (level (i + 1)) / scale δ D.pair.1) ^ D.exponent ≤
            (((parentSpine A Fs B.points (scale δ (level (i + 1))) z).image
              (grid (position A) (scale δ D.pair.1))).card : ℝ)) := by
  classical
  let θ : A → ℝ := fun a => chartSlope j (T (owner Fs a))
  let bins : A → ℤ := fun a => angleLabel n (θ a)
  let p : ℕ → A → GridLabel 1 := fun k => grid (position A) (scale δ (level k))
  have hθ : ∀ a ∈ B.points, |θ a| ≤ 1 := by
    intro a ha
    exact chartSlope_bound j _ (hchart _ (owner_spec Fs (B.subset ha)).1)
  have hbins : (B.points.image bins).card ≤ Bang ^ m :=
    (angle_menu_card B.points θ n hθ).trans hbudget
  have hsp : ∀ k, k ≤ m → ∀ a b, a ∈ B.points → b ∈ B.points →
      SelfUniform.mass (fun _ => 1) (AngularMenuStabilization.cell B.points (p k) (p k a)) ≤
        Q ^ 2 * SelfUniform.mass (fun _ => 1) (AngularMenuStabilization.cell B.points (p k) (p k b)) := by
    intro k hk a b ha hb
    simpa only [SelfUniform.mass, Finset.sum_const, smul_eq_mul, mul_one] using
      uniform_cell_card B.points (p k) Q (B.spatial_uniform ⟨k, by omega⟩) ha hb
  have hjoint : ∀ k, k ≤ m → ∀ a b, a ∈ B.points → b ∈ B.points →
      SelfUniform.mass (fun _ => 1) (AngularMenuStabilization.joint B.points (p k) bins (p k a) (bins a)) ≤
        Q ^ 2 * SelfUniform.mass (fun _ => 1) (AngularMenuStabilization.joint B.points (p k) bins (p k b) (bins b)) := by
    intro k hk a b ha hb
    simpa only [SelfUniform.mass, Finset.sum_const, smul_eq_mul, mul_one] using
      uniform_joint_card B.points (p k) bins Q (B.angular_uniform ⟨k, by omega⟩) ha hb
  obtain ⟨i, hi, _hstep, Ω, hΩ, hne, angles, hlocal, hglobal, hparents, hwhole, hwitness⟩ :=
    ParentwiseAngularSelection.stabilize_and_select_parentwise (fun _ => 1) B.points p bins
      (Q ^ 2) (Q ^ 2) Bang m hm B.nonempty (fun _ _ => Nat.zero_lt_one)
      (fun k hk _a _b _ha _hb he => grid_scale_nested (position A) (hlevel k hk) he)
      hsp hjoint hbins
  refine ⟨i, hi, Ω, hΩ, hne, fun c => selectedSlope n (angles c),
    fun c => selectedSlope_bound n (angles c), ?_, ?_, hparents, hwhole, ?_⟩
  · simpa only [SelfUniform.mass, AngularMenuStabilization.cell,
      Finset.sum_const, smul_eq_mul, mul_one] using hlocal
  · simpa only [SelfUniform.mass, Finset.sum_const, smul_eq_mul, mul_one] using hglobal
  · intro q hq
    obtain ⟨z, hz, hchild, hang⟩ := hwitness q hq
    have hzB := hΩ hz
    have ho := owner_spec Fs (B.subset hzB)
    have hparent : p (i + 1) z = p (i + 1) q := grid_scale_nested (position A) (hlevel i hi) hchild
    refine ⟨z, hz, hchild, ?_, htube _ ho.1 z ho.2, ?_, B.spine_rich ⟨i + 1, by omega⟩ z hzB⟩
    · have hc := angleLabel_close hn (hθ z hzB)
      change |θ z - selectedSlope n (angles (p (i + 1) q))| ≤ _
      rw [← hang]
      exact hc
    · intro a ha
      refine ⟨(Finset.mem_filter.mp ha).1, ?_,
        htube _ ho.1 a (parentSpine_subset_owner A Fs B.points B.subset _ z ha)⟩
      exact (parentSpine_same_cell A Fs B.points _ z a ha).trans hparent

/-- Original AD produces the chart and assigns one genuine tube to each whole
retained fiber before the first refinement. Its angular maps are literal floor
bins of those assigned directions. The sole extra chart loss is a factor two. -/
theorem exists_native_chart_parent_preparation (A : Finset Plane) (δ ε K t : ℝ) (N : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (hN : 0 < N) (htop : scale δ N ≤ 1)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ CoverProfileStopping.stepBudget ε * (N : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t) :
    ∃ e : Epoch A (Index N), ∃ D : StoppedProfile (position A) δ ε K t N e.start,
      D.pair = e.index.val ∧ ∃ T : Finset A → TubeData 1, ∃ j : Fin 2,
      ∃ Fs : List (Finset A), Fs = e.pieces.filter (fun F => chart (T F) = j) ∧
      Fs.Pairwise Disjoint ∧
      A.card ≤ 4 * (Fintype.card (Index N) * rank 2 A.card) * (support Fs).card ∧
      (∀ F ∈ Fs, F ⊆ e.start ∧ |(T F).direction j| = 1 ∧
        ∀ a ∈ F, InTube (T F) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a)) ∧
      ∀ (m Q L n : ℕ), 4 ≤ Q → A.card ≤ Q ^ L →
        ∀ (level : Fin (m + 1) → ℕ),
          (∀ k, D.pair.1 ≤ level k ∧ level k ≤ D.pair.2) →
          Nonempty (ParentCore A Fs D (4 * (Fintype.card (Index N) * rank 2 A.card)) Q L level
            (fun _ a => angleLabel n (chartSlope j (T (owner Fs a))))) := by
  classical
  obtain ⟨e, D, hD, _hFnonempty, hdisj, hret, _hphysical, hpieces⟩ :=
    exists_native_disjoint_epoch A δ ε K t N hne hδ hN htop hε hεhalf hK ht ht2 hlarge hdiam hAD
  have hsub : ∀ F ∈ e.pieces, F ⊆ e.start := by
    intro F hF
    obtain ⟨E, hE, _T, _hreg, hFE, _hwhole, _hTube, _hgrid, _hmass⟩ := hpieces F hF
    exact hFE.trans hE
  have hfiber : ∀ F ∈ e.pieces,
      pruningRate N K t / 4 * (scale δ D.pair.1 / δ) ^ t *
        (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤ (F.card : ℝ) := by
    intro F hF
    obtain ⟨_E, _hE, _T, _hreg, _hFE, _hwhole, _hTube, _hgrid, hmass⟩ := hpieces F hF
    have hr : realThreshold δ N K t e.index = pruningRate N K t * (scale δ D.pair.1 / δ) ^ t := by
      simp only [realThreshold, hD]
    rw [hr] at hmass
    convert hmass using 1; ring
  have htubes : ∀ F ∈ e.pieces, ∃ T : TubeData 1,
      ∀ a ∈ F, InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a) := by
    intro F hF
    obtain ⟨_E, _hE, T, _hreg, _hFE, _hwhole, hTube, _hgrid, _hmass⟩ := hpieces F hF
    exact ⟨T, by simpa only [hD] using hTube⟩
  let T : Finset A → TubeData 1 := fun F =>
    if hF : F ∈ e.pieces then Classical.choose (htubes F hF)
    else ⟨0, axisDirection 1, axisDirection_unit 1⟩
  have hT : ∀ F ∈ e.pieces, ∀ a ∈ F,
      InTube (T F) (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a) := by
    intro F hF
    simpa only [T, dif_pos hF] using Classical.choose_spec (htubes F hF)
  obtain ⟨j, Fs, hFs, hchartret, hchart⟩ := exists_heavy_chart e.pieces T
  have hFsdisj : Fs.Pairwise Disjoint := by
    rw [hFs]
    exact hdisj.filter _
  have hret' : A.card ≤ 4 * (Fintype.card (Index N) * rank 2 A.card) * (support Fs).card := by
    have hh := hret.trans (Nat.mul_le_mul_left (2 * (Fintype.card (Index N) * rank 2 A.card)) hchartret)
    nlinarith only [hh]
  have hsource : (support Fs).Nonempty := by
    apply Finset.card_pos.mp
    have hApos := hne.card_pos
    by_contra h
    have hz : (support Fs).card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hret'
    omega
  refine ⟨e, D, hD, T, j, Fs, hFs, hFsdisj, hret', ?_, ?_⟩
  · intro F hF
    exact ⟨hsub F (hchart F hF).1, (hchart F hF).2, hT F (hchart F hF).1⟩
  · intro m Q L n hQ hheight level hlevel
    have hheight' : (support Fs).card ≤ Q ^ L := by
      have hc := Finset.card_le_card (Finset.subset_univ (support Fs))
      rw [source_card] at hc
      exact hc.trans hheight
    exact exists_parent_core A D Fs hδ hε.le htop hK ht ht2 hdiam hAD hsource hFsdisj
      (fun F hF => hsub F (hchart F hF).1) (fun F hF => hfiber F (hchart F hF).1)
      (fun F hF => ⟨T F, hT F (hchart F hF).1⟩) (by omega) hQ hret' level hlevel
      (fun _ a => angleLabel n (chartSlope j (T (owner Fs a)))) hheight'

end
end NativeAngularChartSelection
