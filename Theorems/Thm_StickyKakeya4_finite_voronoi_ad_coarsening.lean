import Theorems.Thm_StickyKakeya4_finite_voronoi_population
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace FiniteVoronoiADCoarsening

open FiniteVoronoiPopulation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

local instance : DecidableEq X := Classical.decEq X

/-- AD bounds count actual points of the finite carrier in closed metric balls. -/
def ADBounds (P : Finset X) (δ K : ℝ) : Prop :=
  ∀ c ∈ P, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    (r / δ) ^ 3 / K ≤ ((carrierBall P c r).card : ℝ) ∧
      ((carrierBall P c r).card : ℝ) ≤ K * (r / δ) ^ 3

/-- Equivalent cross-multiplied bounds, convenient for mass conservation. -/
def ScaledADBounds (P : Finset X) (δ K : ℝ) : Prop :=
  ∀ c ∈ P, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    r ^ 3 ≤ K * δ ^ 3 * ((carrierBall P c r).card : ℝ) ∧
      δ ^ 3 * ((carrierBall P c r).card : ℝ) ≤ K * r ^ 3

theorem scaled_bounds_of_ADBounds {P : Finset X} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hAD : ADBounds P δ K) :
    ScaledADBounds P δ K := by
  intro c hc r hδr hr
  obtain ⟨hlo, hup⟩ := hAD c hc r hδr hr
  rw [div_pow, div_div] at hlo
  rw [div_pow, ← mul_div_assoc] at hup
  have hlo' := (div_le_iff₀ (mul_pos (pow_pos hδ 3) hK)).mp hlo
  have hup' := (le_div_iff₀ (pow_pos hδ 3)).mp hup
  constructor <;> nlinarith [hlo', hup']

theorem ADBounds_of_scaled_bounds {P : Finset X} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hAD : ScaledADBounds P δ K) :
    ADBounds P δ K := by
  intro c hc r hδr hr
  obtain ⟨hlo, hup⟩ := hAD c hc r hδr hr
  constructor
  · rw [div_pow, div_div]
    apply (div_le_iff₀ (mul_pos (pow_pos hδ 3) hK)).mpr
    nlinarith [hlo]
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hδ 3)).mpr
    nlinarith [hup]

/-- Cubing preserves a nonnegative inequality. -/
theorem cube_le_cube {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 3 ≤ b ^ 3 :=
  pow_le_pow_left₀ ha hab 3

/-- The sum of populations over any set of centers is the actual union size. -/
theorem sum_cluster_card_subfamily (P C S : Finset X) (hC : C.Nonempty) :
    ∑ d ∈ S, (cluster P C hC d).card = (S.biUnion (cluster P C hC)).card := by
  exact (Finset.card_biUnion (fun _d _hd _e _he hde => clusters_disjoint P C hC hde)).symm

theorem cluster_union_subset (P C S : Finset X) (hC : C.Nonempty) :
    S.biUnion (cluster P C hC) ⊆ P := by
  intro p hp
  obtain ⟨d, _hd, hpd⟩ := Finset.mem_biUnion.mp hp
  exact ((mem_cluster P C hC p d).mp hpd).1

theorem sum_cluster_card_subfamily_le_total (P C S : Finset X) (hC : C.Nonempty) :
    ∑ d ∈ S, ((cluster P C hC d).card : ℝ) ≤ (P.card : ℝ) := by
  rw [← Nat.cast_sum, sum_cluster_card_subfamily]
  exact Nat.cast_le.mpr (Finset.card_le_card (cluster_union_subset P C S hC))

/-- The union of clusters whose centers lie in the radius-r ball lies in the
actual radius-(r+ρ) carrier ball. -/
theorem nearby_cluster_union_subset_ball (P C : Finset X) (hC : C.Nonempty)
    {ρ r : ℝ} (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ) (c : X) :
    (carrierBall C c r).biUnion (cluster P C hC) ⊆ carrierBall P c (r + ρ) := by
  intro p hp
  obtain ⟨d, hd, hpd⟩ := Finset.mem_biUnion.mp hp
  have hdc := ((mem_carrierBall C d c r).mp hd).2
  have hpc := (cluster_subset_carrierBall P C hC hcover d) hpd
  obtain ⟨hpP, hdist⟩ := (mem_carrierBall P p d ρ).mp hpc
  apply (mem_carrierBall P p c (r + ρ)).mpr
  refine ⟨hpP, ?_⟩
  have htri := dist_triangle p d c
  linarith

/-- A fine point within r/2 is owned by a center within r whenever 2ρ≤r. -/
theorem half_ball_subset_nearby_cluster_union (P C : Finset X) (hC : C.Nonempty)
    {ρ r : ℝ} (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hlarge : 2 * ρ ≤ r) (c : X) :
    carrierBall P c (r / 2) ⊆ (carrierBall C c r).biUnion (cluster P C hC) := by
  intro p hp
  obtain ⟨hpP, hpc⟩ := (mem_carrierBall P p c (r / 2)).mp hp
  apply Finset.mem_biUnion.mpr
  refine ⟨owner C hC p, ?_, (mem_cluster P C hC p _).mpr ⟨hpP, rfl⟩⟩
  apply (mem_carrierBall C (owner C hC p) c r).mpr
  refine ⟨owner_mem C hC p, ?_⟩
  have hnear := owner_dist_lt P C hC hcover hpP
  have htri := dist_triangle (owner C hC p) p c
  rw [dist_comm (owner C hC p) p] at htri
  linarith

theorem sum_nearby_cluster_card_le_ball (P C : Finset X) (hC : C.Nonempty)
    {ρ r : ℝ} (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ) (c : X) :
    ∑ d ∈ carrierBall C c r, ((cluster P C hC d).card : ℝ) ≤
      ((carrierBall P c (r + ρ)).card : ℝ) := by
  rw [← Nat.cast_sum, sum_cluster_card_subfamily]
  exact Nat.cast_le.mpr (Finset.card_le_card
    (nearby_cluster_union_subset_ball P C hC hcover c))

theorem half_ball_card_le_sum_nearby_clusters (P C : Finset X) (hC : C.Nonempty)
    {ρ r : ℝ} (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hlarge : 2 * ρ ≤ r) (c : X) :
    ((carrierBall P c (r / 2)).card : ℝ) ≤
      ∑ d ∈ carrierBall C c r, ((cluster P C hC d).card : ℝ) := by
  rw [← Nat.cast_sum, sum_cluster_card_subfamily]
  exact Nat.cast_le.mpr (Finset.card_le_card
    (half_ball_subset_nearby_cluster_union P C hC hcover hlarge c))

/-- The constructed cluster populations have uniform two-sided bounds.
For ρ<3δ, the lower bound uses the center itself, not a lower-AD hypothesis
below its valid range. -/
theorem cluster_scaled_population_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1) (hK : 1 ≤ K)
    (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hAD : ScaledADBounds P δ K) {c : X} (hc : c ∈ C) :
    ρ ^ 3 ≤ 27 * K * δ ^ 3 * ((cluster P C hC c).card : ℝ) ∧
      δ ^ 3 * ((cluster P C hC c).card : ℝ) ≤ K * ρ ^ 3 := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hδcube : 0 ≤ δ ^ 3 := (pow_pos hδ 3).le
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsandwich := cluster_card_sandwich P C hC hρpos hsep hcover hc
  have hballupper := (hAD c (hCP hc) ρ hδρ hρ).2
  have hcardupper : ((cluster P C hC c).card : ℝ) ≤ (carrierBall P c ρ).card :=
    Nat.cast_le.mpr hsandwich.2
  refine ⟨?_, (mul_le_mul_of_nonneg_left hcardupper hδcube).trans hballupper⟩
  by_cases hlarge : 3 * δ ≤ ρ
  · have hδthird : δ ≤ ρ / 3 := by linarith
    have hthirdone : ρ / 3 ≤ 1 := by linarith
    have hballlower := (hAD c (hCP hc) (ρ / 3) hδthird hthirdone).1
    have hcardlower : ((carrierBall P c (ρ / 3)).card : ℝ) ≤ (cluster P C hC c).card :=
      Nat.cast_le.mpr hsandwich.1
    have hprod := mul_le_mul_of_nonneg_left hcardlower (mul_nonneg hKpos.le hδcube)
    nlinarith [hballlower]
  · have hρsmall : ρ ≤ 3 * δ := le_of_lt (lt_of_not_ge hlarge)
    have hcube := cube_le_cube hρpos.le hρsmall
    have hone : (1 : ℝ) ≤ (cluster P C hC c).card :=
      Nat.one_le_cast.mpr (one_le_cluster_card P C hC hCP hρpos hsep hc)
    have hfactor : (1 : ℝ) ≤ K * (cluster P C hC c).card :=
      one_le_mul_of_one_le_of_one_le hK hone
    have hmul := mul_le_mul_of_nonneg_left hfactor hδcube
    nlinarith [hcube]

/-- The uniform cluster bounds in the usual dimensionless form. -/
theorem cluster_population_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1) (hK : 1 ≤ K)
    (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hAD : ADBounds P δ K) {c : X} (hc : c ∈ C) :
    (ρ / δ) ^ 3 / (27 * K) ≤ ((cluster P C hC c).card : ℝ) ∧
      ((cluster P C hC c).card : ℝ) ≤ K * (ρ / δ) ^ 3 := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hscaled := cluster_scaled_population_bounds P C hC hδ hδρ hρ hK hCP hsep
    hcover (scaled_bounds_of_ADBounds hδ hKpos hAD) hc
  constructor
  · rw [div_pow, div_div]
    apply (div_le_iff₀ (mul_pos (pow_pos hδ 3) (mul_pos (by norm_num) hKpos))).mpr
    nlinarith [hscaled.1]
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hδ 3)).mpr
    nlinarith [hscaled.2]

/-- Summing actual cluster populations over any subfamily of centers. -/
theorem subfamily_scaled_population_bounds (P C S : Finset X) (hC : C.Nonempty)
    {δ ρ K : ℝ} (hSC : S ⊆ C)
    (hpop : ∀ c ∈ C,
      ρ ^ 3 ≤ 27 * K * δ ^ 3 * ((cluster P C hC c).card : ℝ) ∧
        δ ^ 3 * ((cluster P C hC c).card : ℝ) ≤ K * ρ ^ 3) :
    (S.card : ℝ) * ρ ^ 3 ≤
        27 * K * δ ^ 3 * ∑ d ∈ S, ((cluster P C hC d).card : ℝ) ∧
      δ ^ 3 * (∑ d ∈ S, ((cluster P C hC d).card : ℝ)) ≤
        (S.card : ℝ) * K * ρ ^ 3 := by
  constructor
  · calc
      (S.card : ℝ) * ρ ^ 3 = ∑ _d ∈ S, ρ ^ 3 := by simp
      _ ≤ ∑ d ∈ S, 27 * K * δ ^ 3 * ((cluster P C hC d).card : ℝ) :=
        Finset.sum_le_sum (fun d hd => (hpop d (hSC hd)).1)
      _ = 27 * K * δ ^ 3 * ∑ d ∈ S, ((cluster P C hC d).card : ℝ) :=
        (Finset.mul_sum S _ _).symm
  · calc
      δ ^ 3 * (∑ d ∈ S, ((cluster P C hC d).card : ℝ)) =
          ∑ d ∈ S, δ ^ 3 * ((cluster P C hC d).card : ℝ) :=
        Finset.mul_sum S _ _
      _ ≤ ∑ _d ∈ S, K * ρ ^ 3 :=
        Finset.sum_le_sum (fun d hd => (hpop d (hSC hd)).2)
      _ = (S.card : ℝ) * K * ρ ^ 3 := by simp [mul_assoc]

/-- Diameter at most one makes the unit ball the whole finite carrier. -/
theorem carrierBall_one_eq (P : Finset X)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1) {c : X} (hc : c ∈ P) :
    carrierBall P c 1 = P := by
  ext p
  rw [mem_carrierBall]
  exact ⟨And.left, fun hp => ⟨hp, hdiam p hp c hc⟩⟩

theorem global_scaled_card_le (P : Finset X) (hP : P.Nonempty)
    {δ K : ℝ} (hδone : δ ≤ 1)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ScaledADBounds P δ K) : δ ^ 3 * (P.card : ℝ) ≤ K := by
  obtain ⟨c, hc⟩ := hP
  have hu := (hAD c hc 1 hδone le_rfl).2
  simpa only [carrierBall_one_eq P hdiam hc, one_pow, mul_one] using hu

/-- Quantitative coarse-ball bounds for the actual constructed nearest-center
clusters. The lower bound is stronger than the final common AD constant. -/
theorem coarse_scaled_ball_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1) (hK : 1 ≤ K)
    (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ScaledADBounds P δ K) {c : X} (hc : c ∈ C)
    {r : ℝ} (hρr : ρ ≤ r) (hr : r ≤ 1) :
    r ^ 3 ≤ 8 * K ^ 2 * ρ ^ 3 * ((carrierBall C c r).card : ℝ) ∧
      ρ ^ 3 * ((carrierBall C c r).card : ℝ) ≤ 216 * K ^ 2 * r ^ 3 := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hrpos : 0 < r := hρpos.trans_le hρr
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hδcube : 0 ≤ δ ^ 3 := (pow_pos hδ 3).le
  have hρcube : 0 ≤ ρ ^ 3 := (pow_pos hρpos 3).le
  let S := carrierBall C c r
  let M : ℝ := ∑ d ∈ S, ((cluster P C hC d).card : ℝ)
  have hSC : S ⊆ C := fun d hd => ((mem_carrierBall C d c r).mp hd).1
  have hpop := fun d hd => cluster_scaled_population_bounds P C hC hδ hδρ hρ hK
    hCP hsep hcover hAD (c := d) hd
  have hsum := subfamily_scaled_population_bounds P C S hC hSC hpop
  change (S.card : ℝ) * ρ ^ 3 ≤ 27 * K * δ ^ 3 * M ∧
    δ ^ 3 * M ≤ (S.card : ℝ) * K * ρ ^ 3 at hsum
  change r ^ 3 ≤ 8 * K ^ 2 * ρ ^ 3 * (S.card : ℝ) ∧
    ρ ^ 3 * (S.card : ℝ) ≤ 216 * K ^ 2 * r ^ 3
  constructor
  · by_cases hlarge : 2 * ρ ≤ r
    · have hδhalf : δ ≤ r / 2 := by linarith
      have hhalfone : r / 2 ≤ 1 := by linarith
      have hfine := (hAD c (hCP hc) (r / 2) hδhalf hhalfone).1
      have hball : ((carrierBall P c (r / 2)).card : ℝ) ≤ M :=
        half_ball_card_le_sum_nearby_clusters P C hC hcover hlarge c
      have hballmul := mul_le_mul_of_nonneg_left hball (mul_nonneg hKpos.le hδcube)
      have hsumup := mul_le_mul_of_nonneg_left hsum.2 hKpos.le
      nlinarith [hfine]
    · have hrsmall : r ≤ 2 * ρ := le_of_lt (lt_of_not_ge hlarge)
      have hcube := cube_le_cube hrpos.le hrsmall
      have hcS : c ∈ S :=
        (mem_carrierBall C c c r).mpr ⟨hc, by simpa only [dist_self] using hrpos.le⟩
      have hN : (1 : ℝ) ≤ S.card := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨c, hcS⟩)
      have hKsq : (1 : ℝ) ≤ K ^ 2 := by nlinarith [hK]
      have hfactor := one_le_mul_of_one_le_of_one_le hKsq hN
      have hmul := mul_le_mul_of_nonneg_left hfactor hρcube
      nlinarith [hcube]
  · by_cases hsmall : r + ρ ≤ 1
    · have hδouter : δ ≤ r + ρ := by linarith
      have hfine := (hAD c (hCP hc) (r + ρ) hδouter hsmall).2
      have hball : M ≤ ((carrierBall P c (r + ρ)).card : ℝ) :=
        sum_nearby_cluster_card_le_ball P C hC hcover c
      have hmass : δ ^ 3 * M ≤ K * (r + ρ) ^ 3 :=
        (mul_le_mul_of_nonneg_left hball hδcube).trans hfine
      have hmassmul := mul_le_mul_of_nonneg_left hmass
        (show 0 ≤ 27 * K by positivity)
      have hcube := cube_le_cube (show 0 ≤ r + ρ by linarith)
        (show r + ρ ≤ 2 * r by linarith)
      have hcubemul := mul_le_mul_of_nonneg_left hcube
        (show 0 ≤ 27 * K ^ 2 by positivity)
      nlinarith [hsum.1]
    · have hglobal := global_scaled_card_le P ⟨c, hCP hc⟩ (hδρ.trans hρ) hdiam hAD
      have htotal : M ≤ (P.card : ℝ) := sum_cluster_card_subfamily_le_total P C S hC
      have hmass : δ ^ 3 * M ≤ K :=
        (mul_le_mul_of_nonneg_left htotal hδcube).trans hglobal
      have hmassmul := mul_le_mul_of_nonneg_left hmass
        (show 0 ≤ 27 * K by positivity)
      have htwor : (1 : ℝ) ≤ 2 * r := by linarith
      have hcube := cube_le_cube (by norm_num : (0 : ℝ) ≤ 1) htwor
      have hcubemul := mul_le_mul_of_nonneg_left hcube
        (show 0 ≤ 27 * K ^ 2 by positivity)
      nlinarith [hsum.1]

/-- Coarse AD regularity follows from the actual fine carrier counts and the
constructed nearest-center clusters, with common constant 216 K². -/
theorem coarse_ADBounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1) (hK : 1 ≤ K)
    (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ADBounds P δ K) : ADBounds C ρ (216 * K ^ 2) := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  apply ADBounds_of_scaled_bounds hρpos (by positivity)
  intro c hc r hρr hr
  have hbounds := coarse_scaled_ball_bounds P C hC hδ hδρ hρ hK hCP hsep hcover
    hdiam (scaled_bounds_of_ADBounds hδ hKpos hAD) hc hρr hr
  refine ⟨?_, hbounds.2⟩
  have hnonneg : 0 ≤ K ^ 2 * ρ ^ 3 * ((carrierBall C c r).card : ℝ) := by positivity
  nlinarith [hbounds.1]

/-- A nonempty finite metric carrier satisfying dimension-three AD bounds at
scale δ has an actual separated, covering coarse carrier with AD bounds at
scale ρ. The center set and all cluster/coverage facts are constructed. -/
theorem exists_AD_coarsening (P : Finset X) (hP : P.Nonempty)
    {δ ρ K : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1) (hK : 1 ≤ K)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ADBounds P δ K) :
    ∃ (C : Finset X) (hC : C.Nonempty), C ⊆ P ∧ Separated C ρ ∧
      (∀ p ∈ P, ∃ c ∈ C, dist p c < ρ) ∧
      ADBounds C ρ (216 * K ^ 2) ∧
      C.biUnion (cluster P C hC) = P ∧
      (∑ c ∈ C, (cluster P C hC c).card) = P.card ∧
      (∀ c ∈ C, (ρ / δ) ^ 3 / (27 * K) ≤ ((cluster P C hC c).card : ℝ) ∧
        ((cluster P C hC c).card : ℝ) ≤ K * (ρ / δ) ^ 3) := by
  obtain ⟨C, hC, hCP, hsep, hcover, _hnear, _hdisjoint, hunion, hsum, _hsandwich,
    _hcenter⟩ := exists_voronoi_partition P hP (hδ.trans_le hδρ)
  refine ⟨C, hC, hCP, hsep, hcover,
    coarse_ADBounds P C hC hδ hδρ hρ hK hCP hsep hcover hdiam hAD, hunion, hsum, ?_⟩
  intro c hc
  exact cluster_population_bounds P C hC hδ hδρ hρ hK hCP hsep hcover hAD hc

end
end FiniteVoronoiADCoarsening
