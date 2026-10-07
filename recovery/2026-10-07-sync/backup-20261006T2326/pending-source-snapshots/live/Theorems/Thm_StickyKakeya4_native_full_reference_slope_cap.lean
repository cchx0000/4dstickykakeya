import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFullReferenceSlopeCap
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeOriginalSlopeCubePacking
open NativeCoarseDirectionThinning NativeCoarseCellSource NativeCoarseRepresentativeGeometry
open NativeFullCoarseShadow
open scoped BigOperators

/-- The complete fine fibers of occupied parameter cells supply angular
packing for their actual representatives. No separation of the representatives
is assumed, and no occupied parent is removed. -/
theorem representative_cube_card {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a N i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a N i = p)).card : ℝ))
    (Q : Finset Parent) (hQ : Q ⊆ R.image (parentLabel D a N))
    (rep : Parent → Fin n) (hrep : ∀ p ∈ Q, parentLabel D a N (rep p) = p)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (c : Fin 3 → ℝ)
    (hbox : ∀ p ∈ Q, ∀ j : Fin 3,
      c j ≤ slope (D.line (rep p)) j ∧ slope (D.line (rep p)) j ≤ c j + sigma) :
    (Q.card : ℝ) ≤ 5832 * D.thickness ^ (-zeta) * ((N : ℝ) * sigma + 2) ^ 3 := by
  let F := parentLabel D a N
  let A := R.filter (fun i => F i ∈ Q)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := h.1.2.1
  have htwo : 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
  have hAQ : A.image F = Q := by
    ext p
    constructor
    · rintro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact (mem_filter.mp hi).2
    · intro hp
      obtain ⟨i, hi, hip⟩ := mem_image.mp (hQ hp)
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, by simpa only [F, hip] using hp⟩, hip⟩
  have hsame (p : Parent) (hp : p ∈ Q) :
      A.filter (fun i => F i = p) = R.filter (fun i => F i = p) := by
    ext i
    simp only [A, mem_filter]
    constructor
    · exact fun hi => ⟨hi.1.1, hi.2⟩
    · intro hi
      exact ⟨⟨hi.1, by rw [hi.2]; exact hp⟩, hi.2⟩
  have hwide : ∀ i ∈ A, ∀ j : Fin 3,
      c j - 1 / (N : ℝ) ≤ slope (D.line i) j ∧
        slope (D.line i) j ≤ (c j - 1 / (N : ℝ)) + (sigma + 2 / (N : ℝ)) := by
    intro i hi j
    have hp : F i ∈ Q := (mem_filter.mp hi).2
    have he : parentLabel D a N i = parentLabel D a N (rep (F i)) :=
      (hrep (F i) hp).symm
    have hclose := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (slope (D.line i) j) (slope (D.line (rep (F i))) j) N hN
      (congrFun (congrArg Prod.fst he) j)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hclose
    obtain ⟨hleft, hright⟩ := hbox (F i) hp j
    rw [htwo]
    constructor <;> linarith
  have hdelta : D.thickness ≤ 1 / (N : ℝ) :=
    (le_div_iff₀ hNr).mpr (by nlinarith only [hscale])
  have hcap := native_cube_card_le_ratio h A
    (show D.thickness ≤ sigma + 2 / (N : ℝ) by
      have hpos : 0 < 1 / (N : ℝ) := by positivity
      rw [htwo]
      linarith)
    (fun j => c j - 1 / (N : ℝ)) hwide
  have hsum : (A.card : ℝ) =
      ∑ p ∈ A.image F, ((A.filter (fun i => F i = p)).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image F A
  have hratio : (sigma + 2 / (N : ℝ)) / D.thickness =
      ((N : ℝ) * sigma + 2) * ((1 / (N : ℝ)) / D.thickness) := by
    field_simp [ne_of_gt hNr, ne_of_gt hd]
  have hlow : (Q.card : ℝ) * D.thickness ^ zeta * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
      (5832 * ((N : ℝ) * sigma + 2) ^ 3) * ((1 / (N : ℝ)) / D.thickness) ^ 3 := by
    calc
      _ = ∑ _p ∈ Q, D.thickness ^ zeta * ((1 / (N : ℝ)) / D.thickness) ^ 3 := by
        simp [mul_assoc]
      _ ≤ ∑ p ∈ Q, ((A.filter (fun i => F i = p)).card : ℝ) := by
        apply sum_le_sum
        intro p hp
        rw [hsame p hp]
        obtain ⟨i, hi, hip⟩ := mem_image.mp (hQ hp)
        exact H p ⟨i, mem_filter.mpr ⟨hi, hip⟩⟩
      _ = (A.card : ℝ) := by rw [← hAQ]; exact hsum.symm
      _ ≤ 5832 * ((sigma + 2 / (N : ℝ)) / D.thickness) ^ 3 := hcap
      _ = _ := by rw [hratio, mul_pow]; ring
  have hfactor : 0 < ((1 / (N : ℝ)) / D.thickness) ^ 3 := by positivity
  have hc : (Q.card : ℝ) * D.thickness ^ zeta ≤ 5832 * ((N : ℝ) * sigma + 2) ^ 3 :=
    (mul_le_mul_iff_left₀ hfactor).mp hlow
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hd zeta)).mpr hc
  calc
    _ ≤ (5832 * ((N : ℝ) * sigma + 2) ^ 3) / D.thickness ^ zeta := hdiv
    _ = _ := by rw [Real.rpow_neg hd.le]; ring

/-- Exact line readback for the full ambient coarse source. -/
lemma full_line {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) :
    (fullSource h R a level b E).line i =
      NativeContractedUnitParent.line D a (0, 0)
        (representative h R a (2 ^ b) (parentIndex (R.image (parentLabel D a (2 ^ b))) i)) := rfl

/-- The common 1/512 point contraction leaves each actual unit direction
unchanged. It does not create direction separation in the coarse family. -/
lemma full_direction {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) :
    direction ((fullSource h R a level b E).line i) =
      direction (D.line (representative h R a (2 ^ b)
        (parentIndex (R.image (parentLabel D a (2 ^ b))) i))) := by
  rw [full_line, direction_zero_parent h a]

/-- Graph slopes have no contraction factor either. -/
lemma full_slope {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) (j : Fin 3) :
    slope ((fullSource h R a level b E).line i) j =
      slope (D.line (representative h R a (2 ^ b)
        (parentIndex (R.image (parentLabel D a (2 ^ b))) i))) j := by
  simp only [NativeOriginalCellChartGeometry.slope, full_direction]

/-- Every literal subset of the full source inherits the representative
slope-cube count by its injective original-parent enumeration. -/
theorem full_subset_cube_card {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a (2 ^ b) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / ((2 ^ b : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (2 ^ b) i = p)).card : ℝ))
    (A : Finset (Fin (R.image (parentLabel D a (2 ^ b))).card))
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (c : Fin 3 → ℝ)
    (hbox : ∀ i ∈ A, ∀ j : Fin 3,
      c j ≤ slope ((fullSource h R a level b E).line i) j ∧
        slope ((fullSource h R a level b E).line i) j ≤ c j + sigma) :
    (A.card : ℝ) ≤ 5832 * D.thickness ^ (-zeta) * (((2 ^ b : ℕ) : ℝ) * sigma + 2) ^ 3 := by
  let P := R.image (parentLabel D a (2 ^ b))
  let Q := A.image (parentIndex P)
  have hQ : Q ⊆ P := by
    rintro p hp
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hp
    exact parentIndex_mem P i
  have hb := representative_cube_card h R (2 ^ b) (by positivity) hscale H Q hQ
    (representative h R a (2 ^ b))
    (fun p hp => (representative_spec h R a (2 ^ b) (hQ hp)).2) hsigma c
    (by
      intro p hp j
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      simpa only [full_slope] using hbox i hi j)
  have hcard : Q.card = A.card := card_image_of_injective A (parentIndex_injective P)
  simpa only [hcard] using hb

/-- The full ambient family has an actual carrier-ball upper estimate even
though it need not be direction separated at its output thickness. The only
small-power cost here comes from the original occupied-parent lower law. -/
theorem full_carrier_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (level b : ℕ) (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a (2 ^ b) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / ((2 ^ b : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (2 ^ b) i = p)).card : ℝ))
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) {r : ℝ}
    (hr : (fullSource h R a level b E).thickness ≤ r) :
    (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) ≤
      (5832 * 770 ^ 3) * D.thickness ^ (-zeta) *
        (r / (fullSource h R a level b E).thickness) ^ 3 := by
  let S := fullSource h R a level b E
  let A := (univ : Finset (Fin (R.image (parentLabel D a (2 ^ b))).card)).filter
    (fun j => dist (wzCarrierPoint S j) (wzCarrierPoint S i) ≤ r)
  have hN : (0 : ℝ) < ((2 ^ b : ℕ) : ℝ) := by positivity
  have hthick : S.thickness = 64 / ((2 ^ b : ℕ) : ℝ) := rfl
  have hd : 0 < S.thickness := by rw [hthick]; positivity
  have hrp : 0 < r := hd.trans_le hr
  have hg (j : Fin (R.image (parentLabel D a (2 ^ b))).card) :
      IsValidLine (S.line j) ∧ (1 / 2 : ℝ) ≤ direction (S.line j) (3 : Fin 4) := by
    have hh := zero_parent_valid_slab h a
      (representative h R a (2 ^ b) (parentIndex (R.image (parentLabel D a (2 ^ b))) j))
    exact ⟨hh.1, hh.2.1⟩
  have hbox (j : Fin (R.image (parentLabel D a (2 ^ b))).card) (hj : j ∈ A) (k : Fin 3) :
      slope (S.line i) k - 6 * r ≤ slope (S.line j) k ∧
        slope (S.line j) k ≤ (slope (S.line i) k - 6 * r) + 12 * r := by
    have hdir : dist (direction (S.line j)) (direction (S.line i)) ≤ r :=
      (show dist (direction (S.line j)) (direction (S.line i)) ≤
        dist (wzCarrierPoint S j) (wzCarrierPoint S i) from le_max_left _ _).trans
        (mem_filter.mp hj).2
    have hh := (NativeUnitParentDirections.slope_sub_le_direction_dist
      (S.line j) (S.line i) (hg i).1 (hg j).2 (hg i).2 k).trans
      (mul_le_mul_of_nonneg_left hdir (by norm_num : (0 : ℝ) ≤ 6))
    obtain ⟨hlo, hhi⟩ := abs_le.mp hh
    constructor <;> linarith
  have hb := full_subset_cube_card h R level b E hscale H A
    (show 0 ≤ 12 * r by positivity) (fun k => slope (S.line i) k - 6 * r) hbox
  have ht : 1 ≤ r / S.thickness := (le_div_iff₀ hd).mpr (by simpa using hr)
  have hratio : ((2 ^ b : ℕ) : ℝ) * r = 64 * (r / S.thickness) := by
    rw [hthick]
    field_simp [ne_of_gt hN]
  have hside : ((2 ^ b : ℕ) : ℝ) * (12 * r) + 2 ≤ 770 * (r / S.thickness) := by
    calc
      _ = 768 * (r / S.thickness) + 2 := by nlinarith only [hratio]
      _ ≤ _ := by linarith only [ht]
  have hpow := pow_le_pow_left₀
    (show 0 ≤ ((2 ^ b : ℕ) : ℝ) * (12 * r) + 2 by positivity) hside 3
  have hcost : 0 ≤ 5832 * D.thickness ^ (-zeta) :=
    mul_nonneg (by norm_num) (Real.rpow_pos_of_pos h.1.2.1 (-zeta)).le
  change (A.card : ℝ) ≤ _
  calc
    _ ≤ 5832 * D.thickness ^ (-zeta) * (((2 ^ b : ℕ) : ℝ) * (12 * r) + 2) ^ 3 := hb
    _ ≤ 5832 * D.thickness ^ (-zeta) * (770 * (r / S.thickness)) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow hcost
    _ = _ := by ring

end NativeFullReferenceSlopeCap
