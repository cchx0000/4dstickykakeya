import Theorems.Thm_StickyKakeya4_projection_pair_slope_interval
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ProjectionAnnulusEnergy

open scoped BigOperators
open ProjectionPairSlopeInterval

noncomputable section

abbrev Point := ℝ × ℝ

def projection (lam : ℝ) (p : Point) : ℝ := p.1 - lam * p.2

def distance (p q : Point) : ℝ := pairDistance (p.1 - q.1) (p.2 - q.2)

noncomputable def farPairs (P : Finset Point) (lam r : ℝ) : Finset (Point × Point) :=
  (P.product P).filter (fun pq => 4 * r ≤ distance pq.1 pq.2 ∧
    |projection lam pq.1 - projection lam pq.2| ≤ r)

noncomputable def energy (P : Finset Point) (Lambda : Finset ℝ) (r : ℝ) : ℝ :=
  ∑ lam ∈ Lambda, ((farPairs P lam r).card : ℝ)

noncomputable def slopeFiber (Lambda : Finset ℝ) (p q : Point) (r : ℝ) : Finset ℝ :=
  Lambda.filter (fun lam => |projection lam p - projection lam q| ≤ r)

noncomputable def annularPairs (P : Finset Point) (r s : ℝ) : Finset (Point × Point) :=
  (P.product P).filter (fun pq => s / 2 < distance pq.1 pq.2 ∧
    distance pq.1 pq.2 ≤ s ∧ 4 * r ≤ distance pq.1 pq.2)

noncomputable def annularEnergy (P : Finset Point) (Lambda : Finset ℝ) (r s : ℝ) : ℝ :=
  ∑ pq ∈ annularPairs P r s, ((slopeFiber Lambda pq.1 pq.2 r).card : ℝ)

noncomputable def ball (P : Finset Point) (c : Point) (s : ℝ) : Finset Point :=
  P.filter (fun p => distance p c ≤ s)

/-- Normalized original-point Frostman counts at literal metric balls. -/
def PointFrostman (P : Finset Point) (δ K t : ℝ) : Prop :=
  ∀ c s, δ ≤ s → s ≤ 1 → ((ball P c s).card : ℝ) ≤ K * s ^ t * (P.card : ℝ)

/-- Normalized original-slope Frostman counts at literal intervals. -/
def SlopeFrostman (Lambda : Finset ℝ) (δ K t : ℝ) : Prop :=
  ∀ c s : ℝ, δ ≤ s → s ≤ 1 →
    ((Lambda.filter (fun lam => |lam - c| ≤ s)).card : ℝ) ≤ K * s ^ t * (Lambda.card : ℝ)

def mesh (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def annulusScale (j : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ j

lemma distance_nonneg (p q : Point) : 0 ≤ distance p q := le_max_of_le_left (abs_nonneg _)

lemma distance_comm (p q : Point) : distance p q = distance q p := by
  simp only [distance, pairDistance, abs_sub_comm]

lemma distance_le_two {P : Finset Point}
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    {p q : Point} (hp : p ∈ P) (hq : q ∈ P) : distance p q ≤ 2 := by
  obtain ⟨hp₁, hp₂⟩ := hP p hp
  obtain ⟨hq₁, hq₂⟩ := hP q hq
  exact max_le ((abs_sub _ _).trans (by linarith)) ((abs_sub _ _).trans (by linarith))

lemma mesh_pos (n : ℕ) : 0 < mesh n := by unfold mesh; positivity

lemma annulusScale_pos (j : ℕ) : 0 < annulusScale j := by unfold annulusScale; positivity

lemma mesh_le_annulusScale {n j : ℕ} (hj : j ≤ n) : mesh n ≤ annulusScale j := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hj
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  dsimp [mesh, annulusScale]
  linarith

/-- Select an actual annulus by the least dyadic lower radius below d. -/
theorem exists_annulus (n : ℕ) {d : ℝ} (hsmall : mesh n < d) (htop : d ≤ 2) :
    ∃ j ∈ Finset.range (n + 1), annulusScale j / 2 < d ∧ d ≤ annulusScale j := by
  classical
  have hex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j < d := ⟨n, hsmall⟩
  let j := Nat.find hex
  have hj : j ≤ n := Nat.find_min' hex hsmall
  have hlo : (1 / 2 : ℝ) ^ j < d := Nat.find_spec hex
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, ?_⟩
  · dsimp [annulusScale]
    have he : 2 * (1 / 2 : ℝ) ^ j / 2 = (1 / 2 : ℝ) ^ j := by ring
    rwa [he]
  · by_cases hz : j = 0
    · simpa [annulusScale, hz] using htop
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hnot : ¬(1 / 2 : ℝ) ^ k < d := Nat.find_min hex (by dsimp [j] at hk ⊢; omega)
      have hd : d ≤ (1 / 2 : ℝ) ^ k := le_of_not_gt hnot
      have he : annulusScale j = (1 / 2 : ℝ) ^ k := by rw [hk]; simp [annulusScale, pow_succ]; ring
      rwa [he]

/-- Above scale one, normalized point Frostman follows from the literal total
population, rather than an assumed extended-scale count. -/
theorem point_ball_bound_all (P : Finset Point) {δ K t s : ℝ}
    (_hδ : 0 < δ) (hδs : δ ≤ s) (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hF : PointFrostman P δ K t) (c : Point) :
    ((ball P c s).card : ℝ) ≤ K * s ^ t * (P.card : ℝ) := by
  by_cases hs : s ≤ 1
  · exact hF c s hδs hs
  · have hsone : 1 ≤ s := le_of_lt (lt_of_not_ge hs)
    have hp : 1 ≤ s ^ t := Real.one_le_rpow hsone ht
    have hfactor : 1 ≤ K * s ^ t := by nlinarith only [hK, hp]
    have hc : ((ball P c s).card : ℝ) ≤ (P.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    exact hc.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg P.card))

/-- Sum actual point-centered Frostman bounds to count ordered pairs. -/
theorem annular_pairs_card_bound (P : Finset Point) {δ K t r s : ℝ}
    (hδ : 0 < δ) (hδs : δ ≤ s) (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hF : PointFrostman P δ K t) :
    ((annularPairs P r s).card : ℝ) ≤ K * s ^ t * (P.card : ℝ) ^ 2 := by
  classical
  let C := (P.product P).filter (fun pq => distance pq.1 pq.2 ≤ s)
  have hsub : annularPairs P r s ⊆ C := by
    intro pq hpq
    obtain ⟨hPQ, _, hupper, _⟩ := Finset.mem_filter.mp hpq
    exact Finset.mem_filter.mpr ⟨hPQ, hupper⟩
  have hsum : C.card = ∑ p ∈ P, (ball P p s).card := by
    simp only [C, ball, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product, Finset.product_eq_sprod]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [distance_comm p q]
  have hc : ((annularPairs P r s).card : ℝ) ≤
      ∑ p ∈ P, ((ball P p s).card : ℝ) := by
    have hnat := Finset.card_le_card hsub
    rw [hsum] at hnat
    exact_mod_cast hnat
  calc
    _ ≤ ∑ p ∈ P, ((ball P p s).card : ℝ) := hc
    _ ≤ ∑ _p ∈ P, K * s ^ t * (P.card : ℝ) :=
      Finset.sum_le_sum (fun p _ => point_ball_bound_all P hδ hδs hK ht hF p)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The slope fiber count uses the actual pair-projection interval, then the
annulus bounds. No slope-fiber cap is an input. -/
theorem annular_slope_fiber_bound (P : Finset Point) (Lambda : Finset ℝ)
    {δ KL t r s : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hs : 0 < s) (hKL : 0 ≤ KL) (ht : 0 ≤ t)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hF : SlopeFrostman Lambda δ KL t)
    {pq : Point × Point} (hpq : pq ∈ annularPairs P r s) :
    ((slopeFiber Lambda pq.1 pq.2 r).card : ℝ) ≤
      KL * (4 * r / s) ^ t * (Lambda.card : ℝ) := by
  classical
  obtain ⟨hPQ, hlo, hhi, hfar⟩ := Finset.mem_filter.mp hpq
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hPQ
  have htop := distance_le_two hP hp hq
  have hd : 0 < distance pq.1 pq.2 := by linarith
  have hcard := actual_slope_fiber_card_le Lambda hLambda hδ hδr hfar htop hF
  have heq : (Lambda.filter (fun lam =>
      |(pq.1.1 - pq.2.1) - lam * (pq.1.2 - pq.2.2)| ≤ r)) =
      slopeFiber Lambda pq.1 pq.2 r := by
    have hid (lam : ℝ) : (pq.1.1 - pq.2.1) - lam * (pq.1.2 - pq.2.2) =
        projection lam pq.1 - projection lam pq.2 := by dsimp [projection]; ring
    simp only [slopeFiber, hid]
  rw [heq] at hcard
  have hbase : 2 * r / distance pq.1 pq.2 ≤ 4 * r / s := by
    apply (div_le_div_iff₀ hd hs).mpr
    have hr : 0 ≤ r := (hδ.trans_le hδr).le
    nlinarith only [mul_nonneg hr (show 0 ≤ 2 * distance pq.1 pq.2 - s by linarith only [hlo])]
  have hrpos : 0 < r := hδ.trans_le hδr
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * r / distance pq.1 pq.2) hbase ht
  exact hcard.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKL) (Nat.cast_nonneg _))

/-- Actual point and slope Frostman imply the annular contribution bound. -/
theorem annular_energy_bound (P : Finset Point) (Lambda : Finset ℝ)
    {δ KP KL t r s : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hδs : δ ≤ s)
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (ht : 0 ≤ t) (htone : t ≤ 1)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : PointFrostman P δ KP t) (hFL : SlopeFrostman Lambda δ KL t) :
    annularEnergy P Lambda r s ≤
      4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by
  have hs : 0 < s := hδ.trans_le hδs
  have hr : 0 < r := hδ.trans_le hδr
  have hKP0 : 0 ≤ KP := by linarith only [hKP]
  have hKL0 : 0 ≤ KL := by linarith only [hKL]
  have hpairs := annular_pairs_card_bound P hδ hδs hKP ht hFP (r := r)
  have hsum : annularEnergy P Lambda r s ≤
      ((annularPairs P r s).card : ℝ) * (KL * (4 * r / s) ^ t * (Lambda.card : ℝ)) := by
    unfold annularEnergy
    calc
      _ ≤ ∑ _pq ∈ annularPairs P r s, KL * (4 * r / s) ^ t * (Lambda.card : ℝ) :=
        Finset.sum_le_sum (fun _ hpq => annular_slope_fiber_bound P Lambda hδ hδr hs hKL0 ht hP hLambda hFL hpq)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hproduct : s ^ t * (4 * r / s) ^ t = (4 : ℝ) ^ t * r ^ t := by
    rw [← Real.mul_rpow hs.le (by positivity)]
    have he : s * (4 * r / s) = 4 * r := by field_simp
    rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le]
  have hfour : (4 : ℝ) ^ t ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) htone
  calc
    _ ≤ ((annularPairs P r s).card : ℝ) * (KL * (4 * r / s) ^ t * (Lambda.card : ℝ)) := hsum
    _ ≤ (KP * s ^ t * (P.card : ℝ) ^ 2) * (KL * (4 * r / s) ^ t * (Lambda.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = KP * KL * (s ^ t * (4 * r / s) ^ t) * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by ring
    _ = KP * KL * ((4 : ℝ) ^ t * r ^ t) * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by rw [hproduct]
    _ ≤ KP * KL * (4 * r ^ t) * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by
      gcongr
    _ = _ := by ring

/-- The near-point estimate used by the heavy-cell construction. It is derived
from original point Frostman even when 4*r exceeds the stated top scale. -/
theorem near_pairs_bound (P : Finset Point) {δ K t r : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hK : 1 ≤ K) (ht : 0 ≤ t) (htone : t ≤ 1)
    (hF : PointFrostman P δ K t) (p : Point) :
    ((P.filter (fun q => distance p q < 4 * r)).card : ℝ) ≤
      4 * K * r ^ t * (P.card : ℝ) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  have hsub : P.filter (fun q => distance p q < 4 * r) ⊆ ball P p (4 * r) := by
    intro q hq
    obtain ⟨hqP, hnear⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqP, by rw [distance_comm q p]; exact hnear.le⟩
  have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (point_ball_bound_all P hδ (show δ ≤ 4 * r by linarith only [hδr, hr]) hK ht hF p)
  have hfour : (4 : ℝ) ^ t ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) htone
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr.le] at hc
  have hK0 : 0 ≤ K := by linarith only [hK]
  calc
    _ ≤ K * ((4 : ℝ) ^ t * r ^ t) * (P.card : ℝ) := hc
    _ ≤ K * (4 * r ^ t) * (P.card : ℝ) := by gcongr
    _ = _ := by ring

/-- Finite Fubini counts the same ORIGINAL triples in the opposite order. -/
theorem energy_eq_pair_sum (P : Finset Point) (Lambda : Finset ℝ) (r : ℝ) :
    energy P Lambda r = ∑ pq ∈ P.product P,
      if 4 * r ≤ distance pq.1 pq.2 then ((slopeFiber Lambda pq.1 pq.2 r).card : ℝ) else 0 := by
  classical
  unfold energy farPairs slopeFiber
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pq _
  by_cases hfar : 4 * r ≤ distance pq.1 pq.2 <;> simp [hfar]

/-- Constructed dyadic annuli cover every actual far pair. No annular
partition or pair-energy certificate is assumed. -/
theorem energy_le_annular_sum (P : Finset Point) (Lambda : Finset ℝ) (n : ℕ) (r : ℝ)
    (hr : mesh n ≤ r) (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1) :
    energy P Lambda r ≤ ∑ j ∈ Finset.range (n + 1),
      annularEnergy P Lambda r (annulusScale j) := by
  classical
  let f : Point × Point → ℝ := fun pq => ((slopeFiber Lambda pq.1 pq.2 r).card : ℝ)
  have hf : ∀ pq, 0 ≤ f pq := fun _ => Nat.cast_nonneg _
  have hper : ∀ pq ∈ P.product P,
      (if 4 * r ≤ distance pq.1 pq.2 then f pq else 0) ≤
        ∑ j ∈ Finset.range (n + 1), if pq ∈ annularPairs P r (annulusScale j) then f pq else 0 := by
    intro pq hpq
    by_cases hfar : 4 * r ≤ distance pq.1 pq.2
    · obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      have hsmall : mesh n < distance pq.1 pq.2 := by linarith only [mesh_pos n, hr, hfar]
      obtain ⟨j, hj, hlo, hhi⟩ := exists_annulus n hsmall (distance_le_two hP hp hq)
      have hmem : pq ∈ annularPairs P r (annulusScale j) :=
        Finset.mem_filter.mpr ⟨hpq, hlo, hhi, hfar⟩
      have hsingle := Finset.single_le_sum
        (f := fun j => if pq ∈ annularPairs P r (annulusScale j) then f pq else 0)
        (fun _ _ => by split_ifs <;> first | exact hf pq | exact le_rfl) hj
      simpa only [hfar, hmem, if_true] using hsingle
    · rw [if_neg hfar]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> first | exact hf pq | exact le_rfl)
  rw [energy_eq_pair_sum]
  change (∑ pq ∈ P.product P, if 4 * r ≤ distance pq.1 pq.2 then f pq else 0) ≤ _
  calc
    _ ≤ ∑ pq ∈ P.product P, ∑ j ∈ Finset.range (n + 1),
        if pq ∈ annularPairs P r (annulusScale j) then f pq else 0 := Finset.sum_le_sum hper
    _ = ∑ j ∈ Finset.range (n + 1), ∑ pq ∈ P.product P,
        if pq ∈ annularPairs P r (annulusScale j) then f pq else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      unfold annularEnergy annularPairs
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro pq hpq
      simp only [Finset.mem_filter, hpq, true_and, f]

/-- Full finite Kaufman far-pair energy, derived from actual bounded points,
actual bounded slopes and their literal normalized Frostman counts. -/
theorem kaufman_pair_energy (P : Finset Point) (Lambda : Finset ℝ)
    (n : ℕ) (KP KL t r : ℝ)
    (hKP : 1 ≤ KP) (hKL : 1 ≤ KL) (ht : 0 ≤ t) (htone : t ≤ 1)
    (hr : mesh n ≤ r)
    (hP : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hLambda : ∀ lam ∈ Lambda, |lam| ≤ 1)
    (hFP : PointFrostman P (mesh n) KP t) (hFL : SlopeFrostman Lambda (mesh n) KL t) :
    energy P Lambda r ≤
      4 * KP * KL * ((n : ℝ) + 3) * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by
  have hrpos : 0 < r := (mesh_pos n).trans_le hr
  have hKP0 : 0 ≤ KP := by linarith only [hKP]
  have hKL0 : 0 ≤ KL := by linarith only [hKL]
  have hc : 0 ≤ 4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by positivity
  have hsum := energy_le_annular_sum P Lambda n r hr hP
  have hbound : energy P Lambda r ≤ ((n : ℝ) + 1) *
      (4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), annularEnergy P Lambda r (annulusScale j) := hsum
      _ ≤ ∑ _j ∈ Finset.range (n + 1),
          4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        exact annular_energy_bound P Lambda (mesh_pos n) hr (mesh_le_annulusScale hjn)
          hKP hKL ht htone hP hLambda hFP hFL
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((n : ℝ) + 1) * (4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ)) := hbound
    _ ≤ ((n : ℝ) + 3) * (4 * KP * KL * r ^ t * (P.card : ℝ) ^ 2 * (Lambda.card : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    _ = _ := by ring

end
end ProjectionAnnulusEnergy
