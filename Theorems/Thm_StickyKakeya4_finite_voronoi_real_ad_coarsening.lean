import Theorems.Thm_StickyKakeya4_finite_voronoi_ad_coarsening
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true

namespace FiniteVoronoiRealADCoarsening

open FiniteVoronoiPopulation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

local instance : DecidableEq X := Classical.decEq X

/-- Real-dimensional AD bounds count actual points in closed metric balls. -/
def ADBounds (P : Finset X) (δ K t : ℝ) : Prop :=
  ∀ c ∈ P, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    (r / δ) ^ t / K ≤ ((carrierBall P c r).card : ℝ) ∧
      ((carrierBall P c r).card : ℝ) ≤ K * (r / δ) ^ t

/-- Cross-multiplied real-dimensional bounds. -/
def ScaledADBounds (P : Finset X) (δ K t : ℝ) : Prop :=
  ∀ c ∈ P, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    r ^ t ≤ K * δ ^ t * ((carrierBall P c r).card : ℝ) ∧
      δ ^ t * ((carrierBall P c r).card : ℝ) ≤ K * r ^ t

theorem scaled_bounds_of_ADBounds {P : Finset X} {δ K t : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hAD : ADBounds P δ K t) :
    ScaledADBounds P δ K t := by
  intro c hc r hδr hr
  have hrpos : 0 < r := hδ.trans_le hδr
  obtain ⟨hlo, hup⟩ := hAD c hc r hδr hr
  rw [Real.div_rpow hrpos.le hδ.le, div_div] at hlo
  rw [Real.div_rpow hrpos.le hδ.le, ← mul_div_assoc] at hup
  have hlo' := (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hδ t) hK)).mp hlo
  have hup' := (le_div_iff₀ (Real.rpow_pos_of_pos hδ t)).mp hup
  constructor <;> nlinarith [hlo', hup']

theorem ADBounds_of_scaled_bounds {P : Finset X} {δ K t : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hAD : ScaledADBounds P δ K t) :
    ADBounds P δ K t := by
  intro c hc r hδr hr
  have hrpos : 0 < r := hδ.trans_le hδr
  obtain ⟨hlo, hup⟩ := hAD c hc r hδr hr
  constructor
  · rw [Real.div_rpow hrpos.le hδ.le, div_div]
    apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hδ t) hK)).mpr
    nlinarith [hlo]
  · rw [Real.div_rpow hrpos.le hδ.le, ← mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ t)).mpr
    nlinarith [hup]

/-- Two-sided populations of the actual nearest-center clusters. At scales
ρ<3δ the lower bound uses the center itself, so no fine lower bound is used
outside its valid scale range. This works also at exponent t=0. -/
theorem cluster_scaled_population_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hAD : ScaledADBounds P δ K t) {c : X} (hc : c ∈ C) :
    ρ ^ t ≤ (3 : ℝ) ^ t * K * δ ^ t * ((cluster P C hC c).card : ℝ) ∧
      δ ^ t * ((cluster P C hC c).card : ℝ) ≤ K * ρ ^ t := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hδpow : 0 ≤ δ ^ t := (Real.rpow_pos_of_pos hδ t).le
  have hthree : 0 < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsandwich := cluster_card_sandwich P C hC hρpos hsep hcover hc
  have hballupper := (hAD c (hCP hc) ρ hδρ hρ).2
  have hcardupper : ((cluster P C hC c).card : ℝ) ≤ (carrierBall P c ρ).card :=
    Nat.cast_le.mpr hsandwich.2
  refine ⟨?_, (mul_le_mul_of_nonneg_left hcardupper hδpow).trans hballupper⟩
  by_cases hlarge : 3 * δ ≤ ρ
  · have hδthird : δ ≤ ρ / 3 := by linarith
    have hthirdone : ρ / 3 ≤ 1 := by linarith
    have hballlower := (hAD c (hCP hc) (ρ / 3) hδthird hthirdone).1
    rw [Real.div_rpow hρpos.le (by norm_num)] at hballlower
    have hballlower' := (div_le_iff₀ hthree).mp hballlower
    have hcardlower : ((carrierBall P c (ρ / 3)).card : ℝ) ≤ (cluster P C hC c).card :=
      Nat.cast_le.mpr hsandwich.1
    have hprod := mul_le_mul_of_nonneg_left hcardlower
      (mul_nonneg (mul_nonneg hthree.le hKpos.le) hδpow)
    nlinarith [hballlower']
  · have hρsmall : ρ ≤ 3 * δ := le_of_lt (lt_of_not_ge hlarge)
    have hpow := Real.rpow_le_rpow hρpos.le hρsmall ht
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hδ.le] at hpow
    have hone : (1 : ℝ) ≤ (cluster P C hC c).card :=
      Nat.one_le_cast.mpr (one_le_cluster_card P C hC hCP hρpos hsep hc)
    have hfactor : (1 : ℝ) ≤ K * (cluster P C hC c).card :=
      one_le_mul_of_one_le_of_one_le hK hone
    have hmul := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hthree.le hδpow)
    nlinarith [hpow]

/-- Uniform real-dimensional cluster populations in dimensionless form. -/
theorem cluster_population_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hAD : ADBounds P δ K t) {c : X} (hc : c ∈ C) :
    (ρ / δ) ^ t / ((3 : ℝ) ^ t * K) ≤ ((cluster P C hC c).card : ℝ) ∧
      ((cluster P C hC c).card : ℝ) ≤ K * (ρ / δ) ^ t := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hthree : 0 < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hscaled := cluster_scaled_population_bounds P C hC hδ hδρ hρ hK ht hCP hsep
    hcover (scaled_bounds_of_ADBounds hδ hKpos hAD) hc
  constructor
  · rw [Real.div_rpow hρpos.le hδ.le, div_div]
    apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hδ t) (mul_pos hthree hKpos))).mpr
    nlinarith [hscaled.1]
  · rw [Real.div_rpow hρpos.le hδ.le, ← mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ t)).mpr
    nlinarith [hscaled.2]

/-- Mass conservation transfers uniform cluster bounds to every center subfamily. -/
theorem subfamily_scaled_population_bounds (P C S : Finset X) (hC : C.Nonempty)
    {δ ρ K t : ℝ} (hSC : S ⊆ C)
    (hpop : ∀ c ∈ C,
      ρ ^ t ≤ (3 : ℝ) ^ t * K * δ ^ t * ((cluster P C hC c).card : ℝ) ∧
        δ ^ t * ((cluster P C hC c).card : ℝ) ≤ K * ρ ^ t) :
    (S.card : ℝ) * ρ ^ t ≤
        (3 : ℝ) ^ t * K * δ ^ t * ∑ d ∈ S, ((cluster P C hC d).card : ℝ) ∧
      δ ^ t * (∑ d ∈ S, ((cluster P C hC d).card : ℝ)) ≤
        (S.card : ℝ) * K * ρ ^ t := by
  constructor
  · calc
      (S.card : ℝ) * ρ ^ t = ∑ _d ∈ S, ρ ^ t := by simp
      _ ≤ ∑ d ∈ S, (3 : ℝ) ^ t * K * δ ^ t * ((cluster P C hC d).card : ℝ) :=
        Finset.sum_le_sum (fun d hd => (hpop d (hSC hd)).1)
      _ = (3 : ℝ) ^ t * K * δ ^ t * ∑ d ∈ S, ((cluster P C hC d).card : ℝ) :=
        (Finset.mul_sum S _ _).symm
  · calc
      δ ^ t * (∑ d ∈ S, ((cluster P C hC d).card : ℝ)) =
          ∑ d ∈ S, δ ^ t * ((cluster P C hC d).card : ℝ) :=
        Finset.mul_sum S _ _
      _ ≤ ∑ _d ∈ S, K * ρ ^ t :=
        Finset.sum_le_sum (fun d hd => (hpop d (hSC hd)).2)
      _ = (S.card : ℝ) * K * ρ ^ t := by simp [mul_assoc]

/-- Diameter at most one controls total fine mass by the unit-ball upper bound. -/
theorem global_scaled_card_le (P : Finset X) (hP : P.Nonempty)
    {δ K t : ℝ} (hδone : δ ≤ 1)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ScaledADBounds P δ K t) : δ ^ t * (P.card : ℝ) ≤ K := by
  obtain ⟨c, hc⟩ := hP
  have hu := (hAD c hc 1 hδone le_rfl).2
  simpa only [FiniteVoronoiADCoarsening.carrierBall_one_eq P hdiam hc,
    Real.one_rpow, mul_one] using hu

/-- Actual coarse balls inherit quantitative real-dimensional bounds through
nearest-center cluster mass. The lower constant is 2^t K²; the upper constant
is 6^t K². No positive lower bound on t is required. -/
theorem coarse_scaled_ball_bounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ScaledADBounds P δ K t) {c : X} (hc : c ∈ C)
    {r : ℝ} (hρr : ρ ≤ r) (hr : r ≤ 1) :
    r ^ t ≤ (2 : ℝ) ^ t * K ^ 2 * ρ ^ t * ((carrierBall C c r).card : ℝ) ∧
      ρ ^ t * ((carrierBall C c r).card : ℝ) ≤ (6 : ℝ) ^ t * K ^ 2 * r ^ t := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hrpos : 0 < r := hρpos.trans_le hρr
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hδpow : 0 ≤ δ ^ t := (Real.rpow_pos_of_pos hδ t).le
  have hρpow : 0 ≤ ρ ^ t := (Real.rpow_pos_of_pos hρpos t).le
  have htwo : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hthree : 0 < (3 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hsix : (6 : ℝ) ^ t = (3 : ℝ) ^ t * (2 : ℝ) ^ t := by
    calc
      (6 : ℝ) ^ t = ((3 : ℝ) * 2) ^ t := by norm_num
      _ = _ := Real.mul_rpow (by norm_num) (by norm_num)
  let S := carrierBall C c r
  let M : ℝ := ∑ d ∈ S, ((cluster P C hC d).card : ℝ)
  have hSC : S ⊆ C := fun d hd => ((mem_carrierBall C d c r).mp hd).1
  have hpop := fun d hd => cluster_scaled_population_bounds P C hC hδ hδρ hρ hK ht
    hCP hsep hcover hAD (c := d) hd
  have hsum := subfamily_scaled_population_bounds P C S hC hSC hpop
  change (S.card : ℝ) * ρ ^ t ≤ (3 : ℝ) ^ t * K * δ ^ t * M ∧
    δ ^ t * M ≤ (S.card : ℝ) * K * ρ ^ t at hsum
  change r ^ t ≤ (2 : ℝ) ^ t * K ^ 2 * ρ ^ t * (S.card : ℝ) ∧
    ρ ^ t * (S.card : ℝ) ≤ (6 : ℝ) ^ t * K ^ 2 * r ^ t
  constructor
  · by_cases hlarge : 2 * ρ ≤ r
    · have hδhalf : δ ≤ r / 2 := by linarith
      have hhalfone : r / 2 ≤ 1 := by linarith
      have hfine := (hAD c (hCP hc) (r / 2) hδhalf hhalfone).1
      have hball : ((carrierBall P c (r / 2)).card : ℝ) ≤ M :=
        FiniteVoronoiADCoarsening.half_ball_card_le_sum_nearby_clusters
          P C hC hcover hlarge c
      have hballmul := mul_le_mul_of_nonneg_left hball (mul_nonneg hKpos.le hδpow)
      have hsumup := mul_le_mul_of_nonneg_left hsum.2 hKpos.le
      have hhalf : (r / 2) ^ t ≤ K ^ 2 * ρ ^ t * (S.card : ℝ) := by
        nlinarith [hfine]
      rw [Real.div_rpow hrpos.le (by norm_num)] at hhalf
      have hhalf' := (div_le_iff₀ htwo).mp hhalf
      nlinarith [hhalf']
    · have hrsmall : r ≤ 2 * ρ := le_of_lt (lt_of_not_ge hlarge)
      have hpow := Real.rpow_le_rpow hrpos.le hrsmall ht
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hρpos.le] at hpow
      have hcS : c ∈ S :=
        (mem_carrierBall C c c r).mpr ⟨hc, by simpa only [dist_self] using hrpos.le⟩
      have hN : (1 : ℝ) ≤ S.card := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨c, hcS⟩)
      have hKsq : (1 : ℝ) ≤ K ^ 2 := by nlinarith [hK]
      have hfactor := one_le_mul_of_one_le_of_one_le hKsq hN
      have hmul := mul_le_mul_of_nonneg_left hfactor (mul_nonneg htwo.le hρpow)
      nlinarith [hpow]
  · rw [hsix]
    by_cases hsmall : r + ρ ≤ 1
    · have hδouter : δ ≤ r + ρ := by linarith
      have hfine := (hAD c (hCP hc) (r + ρ) hδouter hsmall).2
      have hball : M ≤ ((carrierBall P c (r + ρ)).card : ℝ) :=
        FiniteVoronoiADCoarsening.sum_nearby_cluster_card_le_ball P C hC hcover c
      have hmass : δ ^ t * M ≤ K * (r + ρ) ^ t :=
        (mul_le_mul_of_nonneg_left hball hδpow).trans hfine
      have hmassmul := mul_le_mul_of_nonneg_left hmass (mul_nonneg hthree.le hKpos.le)
      have hpow := Real.rpow_le_rpow (show 0 ≤ r + ρ by linarith)
        (show r + ρ ≤ 2 * r by linarith) ht
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrpos.le] at hpow
      have hpowmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg hthree.le (sq_nonneg K))
      nlinarith [hsum.1]
    · have hglobal := global_scaled_card_le P ⟨c, hCP hc⟩ (hδρ.trans hρ) hdiam hAD
      have htotal : M ≤ (P.card : ℝ) :=
        FiniteVoronoiADCoarsening.sum_cluster_card_subfamily_le_total P C S hC
      have hmass : δ ^ t * M ≤ K :=
        (mul_le_mul_of_nonneg_left htotal hδpow).trans hglobal
      have hmassmul := mul_le_mul_of_nonneg_left hmass (mul_nonneg hthree.le hKpos.le)
      have htwor : (1 : ℝ) ≤ 2 * r := by linarith
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) htwor ht
      rw [Real.one_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrpos.le] at hpow
      have hpowmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg hthree.le (sq_nonneg K))
      nlinarith [hsum.1]

/-- Coarse real-dimensional AD regularity with common constant 6^t K². -/
theorem coarse_ADBounds (P C : Finset X) (hC : C.Nonempty)
    {δ ρ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (hCP : C ⊆ P) (hsep : Separated C ρ)
    (hcover : ∀ p ∈ P, ∃ d ∈ C, dist p d < ρ)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ADBounds P δ K t) : ADBounds C ρ ((6 : ℝ) ^ t * K ^ 2) t := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsixpos : 0 < (6 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  apply ADBounds_of_scaled_bounds hρpos (mul_pos hsixpos (sq_pos_of_pos hKpos))
  intro c hc r hρr hr
  have hbounds := coarse_scaled_ball_bounds P C hC hδ hδρ hρ hK ht hCP hsep hcover
    hdiam (scaled_bounds_of_ADBounds hδ hKpos hAD) hc hρr hr
  refine ⟨?_, hbounds.2⟩
  have htwosix : (2 : ℝ) ^ t ≤ (6 : ℝ) ^ t :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) ht
  have hnonneg : 0 ≤ K ^ 2 * ρ ^ t * ((carrierBall C c r).card : ℝ) :=
    mul_nonneg (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg hρpos.le t)) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right htwosix hnonneg
  nlinarith [hbounds.1]

/-- Every nonempty finite t-AD carrier, for arbitrary real t≥0, has an actual
ρ-separated covering subcarrier which is t-AD at scale ρ with constant 6^t K².
All centers, cluster fibers and covering statements are constructed from P.
No occupied-cell lower bound or coarse regularity certificate is an input. -/
theorem exists_AD_coarsening (P : Finset X) (hP : P.Nonempty)
    {δ ρ K t : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ADBounds P δ K t) :
    ∃ (C : Finset X) (hC : C.Nonempty), C ⊆ P ∧ Separated C ρ ∧
      (∀ p ∈ P, ∃ c ∈ C, dist p c < ρ) ∧
      ADBounds C ρ ((6 : ℝ) ^ t * K ^ 2) t ∧
      C.biUnion (cluster P C hC) = P ∧
      (∑ c ∈ C, (cluster P C hC c).card) = P.card ∧
      (∀ c ∈ C, (ρ / δ) ^ t / ((3 : ℝ) ^ t * K) ≤ ((cluster P C hC c).card : ℝ) ∧
        ((cluster P C hC c).card : ℝ) ≤ K * (ρ / δ) ^ t) := by
  obtain ⟨C, hC, hCP, hsep, hcover, _hnear, _hdisjoint, hunion, hsum, _hsandwich,
    _hcenter⟩ := exists_voronoi_partition P hP (hδ.trans_le hδρ)
  refine ⟨C, hC, hCP, hsep, hcover,
    coarse_ADBounds P C hC hδ hδρ hρ hK ht hCP hsep hcover hdiam hAD, hunion, hsum, ?_⟩
  intro c hc
  exact cluster_population_bounds P C hC hδ hδρ hρ hK ht hCP hsep hcover hAD hc

end
end FiniteVoronoiRealADCoarsening
