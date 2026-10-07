import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening
import Theorems.Thm_StickyKakeya4_original_height_rescaling

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeFiniteSliceUnionAD
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]
local instance : DecidableEq X := Classical.decEq X

lemma carrierBall_biUnion {ι : Type*} (I : Finset ι) (P : ι → Finset X)
    (x : X) (r : ℝ) :
    carrierBall (I.biUnion P) x r = I.biUnion (fun i => carrierBall (P i) x r) := by
  classical
  ext y
  simp only [mem_carrierBall, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, hy⟩, hd⟩
    exact ⟨i, hi, hy, hd⟩
  · rintro ⟨i, hi, hy, hd⟩
    exact ⟨⟨i, hi, hy⟩, hd⟩

/-- An upper bound about an arbitrary center. For 2r<=1, recenter at an
actual point of the intersection. For 2r>1, use the independently derived
global source count instead of applying AD beyond its valid radius. -/
theorem arbitrary_center_ball_upper (P : Finset X) {mu K s : ℝ}
    (hmu : 0 < mu) (hK : 0 < K) (hs : 0 ≤ s)
    (hAD : ADBounds P mu K s) (hglobal : (P.card : ℝ) ≤ K*mu^(-s))
    (x : X) {r : ℝ} (hmur : mu ≤ r) :
    ((carrierBall P x r).card : ℝ) ≤ (2:ℝ)^s*K*(r/mu)^s := by
  classical
  have hr : 0 < r := hmu.trans_le hmur
  have hdouble : K*((2*r)/mu)^s = (2:ℝ)^s*K*(r/mu)^s := by
    have heq : (2*r)/mu = 2*(r/mu) := by ring
    rw [heq, Real.mul_rpow (by norm_num) (div_nonneg hr.le hmu.le)]
    ring
  by_cases hsmall : 2*r ≤ 1
  · by_cases hmeet : (carrierBall P x r).Nonempty
    · obtain ⟨y, hy⟩ := hmeet
      obtain ⟨hyP, hyx⟩ := (mem_carrierBall P y x r).mp hy
      have hxy : dist x y ≤ r := by simpa only [dist_comm] using hyx
      have hsub : carrierBall P x r ⊆ carrierBall P y (2*r) := by
        intro z hz
        obtain ⟨hzP, hzx⟩ := (mem_carrierBall P z x r).mp hz
        apply (mem_carrierBall P z y (2*r)).mpr
        refine ⟨hzP, ?_⟩
        have ht := dist_triangle z x y
        linarith only [ht, hzx, hxy]
      have hcard : ((carrierBall P x r).card : ℝ) ≤ (carrierBall P y (2*r)).card :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      have hu := (hAD y hyP (2*r) (by linarith only [hmur, hr]) hsmall).2
      exact (hcard.trans hu).trans_eq hdouble
    · have hempty : carrierBall P x r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hmeet
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  · have hcard : ((carrierBall P x r).card : ℝ) ≤ P.card := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro z hz
      exact ((mem_carrierBall P z x r).mp hz).1
    have hratio : 1/mu ≤ (2*r)/mu :=
      div_le_div_of_nonneg_right (by linarith only [hsmall]) hmu.le
    have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/mu) hratio hs
    have hunit : (1/mu)^s = mu^(-s) := by
      rw [Real.div_rpow (by norm_num) hmu.le, Real.one_rpow,
        Real.rpow_neg hmu.le, one_div]
    rw [hunit] at hpow
    exact (hcard.trans (hglobal.trans (mul_le_mul_of_nonneg_left hpow hK.le))).trans_eq hdouble

/-- A union of at most N literal slices retains lower AD from a slice
containing the chosen center. The upper estimate sums arbitrary-center
counts. Empty pieces and overlapping pieces are allowed. -/
theorem finite_union_ADBounds {ι : Type*} (I : Finset ι) (P : ι → Finset X) (N : ℕ)
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 0 < K) (hs : 0 ≤ s)
    (hN : 1 ≤ N) (hcard : I.card ≤ N)
    (hAD : ∀i∈I, ADBounds (P i) mu K s)
    (hglobal : ∀i∈I, ((P i).card : ℝ) ≤ K*mu^(-s)) :
    ADBounds (I.biUnion P) mu ((N:ℝ)*(2:ℝ)^s*K) s := by
  classical
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have htwo : (1:ℝ) ≤ (2:ℝ)^s := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
    simpa only [Real.rpow_zero] using hh
  have hfactor : (1:ℝ) ≤ (N:ℝ)*(2:ℝ)^s := one_le_mul_of_one_le_of_one_le hNr htwo
  have hKle : K ≤ (N:ℝ)*(2:ℝ)^s*K := le_mul_of_one_le_left hK.le hfactor
  intro x hx r hmur hr1
  have hr : 0 < r := hmu.trans_le hmur
  constructor
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    have hsub : carrierBall (P i) x r ⊆ carrierBall (I.biUnion P) x r := by
      intro y hy
      obtain ⟨hyP, hyd⟩ := (mem_carrierBall (P i) y x r).mp hy
      exact (mem_carrierBall (I.biUnion P) y x r).mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, hi, hyP⟩, hyd⟩
    have hmass : ((carrierBall (P i) x r).card : ℝ) ≤ (carrierBall (I.biUnion P) x r).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hlo := (hAD i hi x hxi r hmur hr1).1
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (div_nonneg hr.le hmu.le) _) hK hKle).trans
      (hlo.trans hmass)
  · calc
      ((carrierBall (I.biUnion P) x r).card : ℝ) =
          (I.biUnion (fun i => carrierBall (P i) x r)).card := by
        rw [carrierBall_biUnion I P x r]
      _ ≤ ∑i∈I, ((carrierBall (P i) x r).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s:=I) (t:=fun i => carrierBall (P i) x r))
      _ ≤ ∑_i∈I, (2:ℝ)^s*K*(r/mu)^s := Finset.sum_le_sum (fun i hi =>
        arbitrary_center_ball_upper (P i) hmu hK hs (hAD i hi) (hglobal i hi) x hmur)
      _ = (I.card:ℝ)*((2:ℝ)^s*K*(r/mu)^s) := by simp
      _ ≤ (N:ℝ)*((2:ℝ)^s*K*(r/mu)^s) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
      _ = _ := by ring

omit [PseudoMetricSpace X] in
/-- Adapter for the stronger global quotient-count normalization already
available at the source. This is a scalar weakening, not a support claim. -/
lemma global_bound_of_half_mesh (P : Finset X) {mu K s : ℝ}
    (hmu : 0 < mu) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hglobal : (P.card:ℝ) ≤ K*(1/(2*mu))^s) :
    (P.card:ℝ) ≤ K*mu^(-s) := by
  have hratio : 1/(2*mu) ≤ 1/mu :=
    div_le_div_of_nonneg_left (by norm_num) hmu (by linarith only [hmu])
  have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/(2*mu)) hratio hs
  have hunit : (1/mu)^s = mu^(-s) := by
    rw [Real.div_rpow (by norm_num) hmu.le, Real.one_rpow,
      Real.rpow_neg hmu.le, one_div]
  rw [hunit] at hpow
  exact hglobal.trans (mul_le_mul_of_nonneg_left hpow hK)

def heightSlice {Ω : Type*} (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X) (z : ℤ) : Finset X := by
  classical
  exact (A.filter (fun a => height a=z)).image value

def heightWindow {Ω : Type*} (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X)
    (H : ℕ) (q : ℤ) : Finset X := by
  classical
  exact (A.filter (fun a => height a/(H:ℤ)=q)).image value

omit [PseudoMetricSpace X] in
/-- Exact original-height decomposition. Its H-piece count is a theorem
about integer division, including negative heights, rather than a density
or regularity assumption. -/
theorem heightWindow_eq_biUnion {Ω : Type*} (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X)
    (H : ℕ) (hH : 0 < H) (q : ℤ) :
    heightWindow A height value H q =
      (OriginalHeightRescaling.timeFiber H q).biUnion (heightSlice A height value) := by
  classical
  ext x
  constructor
  · intro hx
    change x∈(A.filter (fun a => height a/(H:ℤ)=q)).image value at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨haA, haq⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨height a, (OriginalHeightRescaling.mem_timeFiber H hH q (height a)).mpr haq, ?_⟩
    change value a∈(A.filter (fun b => height b=height a)).image value
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haA, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.mp hx
    change x∈(A.filter (fun a => height a=z)).image value at hxz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxz
    obtain ⟨haA, haz⟩ := Finset.mem_filter.mp ha
    have haq : height a/(H:ℤ)=q := by
      rw [haz]
      exact (OriginalHeightRescaling.mem_timeFiber H hH q z).mp hz
    change value a∈(A.filter (fun b => height b/(H:ℤ)=q)).image value
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haA, haq⟩, rfl⟩

/-- Source-facing finest-window endpoint: H=1,2,4,8 (and every other
positive H<=8) is the literal union of at most eight original Y slices.
The actual global quotient-count theorem supplies hglobal. -/
theorem heightWindow_eight_ADBounds {Ω : Type*} (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X)
    (H : ℕ) (hH : 0 < H) (hH8 : H ≤ 8) (q : ℤ)
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 0 < K) (hs : 0 ≤ s)
    (hAD : ∀z∈OriginalHeightRescaling.timeFiber H q, ADBounds (heightSlice A height value z) mu K s)
    (hglobal : ∀z∈OriginalHeightRescaling.timeFiber H q,
      ((heightSlice A height value z).card:ℝ) ≤ K*mu^(-s)) :
    ADBounds (heightWindow A height value H q) mu (8*(2:ℝ)^s*K) s := by
  rw [heightWindow_eq_biUnion A height value H hH q]
  have hcard : (OriginalHeightRescaling.timeFiber H q).card ≤ 8 := by
    rw [OriginalHeightRescaling.card_timeFiber]
    exact hH8
  simpa only [Nat.cast_ofNat] using finite_union_ADBounds
    (OriginalHeightRescaling.timeFiber H q) (heightSlice A height value) 8
    hmu hK hs (by norm_num) hcard hAD hglobal

end NativeFiniteSliceUnionAD
