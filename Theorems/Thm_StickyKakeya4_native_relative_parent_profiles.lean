import Theorems.Thm_StickyKakeya4_native_relative_parent_labels
import Theorems.Thm_StickyKakeya4_native_actual_local_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRelativeParentProfiles
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeRelativeParentLabels
open NativeLocalParentSource NativeLocalParentSourceCounts
open scoped BigOperators ENNReal

/-- A relative atom on the full, unchanged original parent backbone. -/
def relativeAtom {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) (M : ℕ) (q : Parent) : Finset (Fin n) :=
  (parentLabels D R a N p).filter (fun i => relativeLabel D a N p M i = q)

def relativeParents {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) (M : ℕ) : Finset Parent :=
  (parentLabels D R a N p).image (relativeLabel D a N p M)

/-- An occupied original product-scale atom is retained in its entirety.
Dyadic nesting, rather than a ball about a boundary point, proves this. -/
lemma original_atom_in_parent {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (m ell : ℕ) (p z : Parent)
    (hne : ((parentLabels D R a (2^m) p).filter
      (fun i => parentLabel D a ((2^ell)*(2^m)) i = z)).Nonempty) :
    (parentLabels D R a (2^m) p).filter
      (fun i => parentLabel D a ((2^ell)*(2^m)) i = z) =
        R.filter (fun i => parentLabel D a ((2^ell)*(2^m)) i = z) := by
  have he : (2:ℕ)^ell * 2^m = 2^(m+ell) := by rw [pow_add, Nat.mul_comm]
  simp only [he, parentLabels] at hne ⊢
  exact NativeCoarseAncestorCounts.fiber_in_ancestor_eq D R a (by omega) p z hne

/-- Every occupied actual relative atom contains an entire occupied original
MN atom and is a union of at most 512^3 such atoms. R is never replaced. -/
theorem relative_population_bounds {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (m ell : ℕ) (p : Parent)
    {L U : ℝ} (hU : 0 ≤ U)
    (H : ∀ z, (R.filter (fun i => parentLabel D a ((2^ell)*(2^m)) i = z)).Nonempty →
      L ≤ ((R.filter (fun i => parentLabel D a ((2^ell)*(2^m)) i = z)).card : ℝ) ∧
      ((R.filter (fun i => parentLabel D a ((2^ell)*(2^m)) i = z)).card : ℝ) ≤ U)
    (q : Parent) (hq : (relativeAtom D R a (2^m) p (2^ell) q).Nonempty) :
    L ≤ ((relativeAtom D R a (2^m) p (2^ell) q).card : ℝ) ∧
      ((relativeAtom D R a (2^m) p (2^ell) q).card : ℝ) ≤ (512:ℝ)^3 * U := by
  let Q := parentLabels D R a (2^m) p
  let S := relativeAtom D R a (2^m) p (2^ell) q
  let f := parentLabel D a ((2^ell)*(2^m))
  obtain ⟨i,hi⟩ := hq
  have hiQ : i ∈ Q := (mem_filter.mp hi).1
  have hiR : i ∈ R := (mem_filter.mp hiQ).1
  have hip : NativeRelativeParentLabels.projection p (2^ell) (f i) = q := by
    rw [←relativeLabel_eq_projection]
    exact (mem_filter.mp hi).2
  have hfiber : Q.filter (fun k => f k = f i) = R.filter (fun k => f k = f i) :=
    original_atom_in_parent D R a m ell p (f i) ⟨i,mem_filter.mpr ⟨hiQ,rfl⟩⟩
  have hold : R.filter (fun k => f k = f i) ⊆ S := by
    rw [←hfiber]
    intro k hk
    refine mem_filter.mpr ⟨(mem_filter.mp hk).1,?_⟩
    rw [relativeLabel_eq_projection]
    change NativeRelativeParentLabels.projection p (2^ell) (f k) = q
    rw [(mem_filter.mp hk).2]
    exact hip
  have hlow := (H _ ⟨i,mem_filter.mpr ⟨hiR,rfl⟩⟩).1
  have hc : ((S.image f).card : ℝ) ≤ (512:ℝ)^3 := by
    exact_mod_cast relative_atom_original_labels D Q a (2^m) p (2^ell) q
  refine ⟨hlow.trans (by exact_mod_cast card_le_card hold),?_⟩
  have hs : (S.card : ℝ) = ∑ z ∈ S.image f, ((S.filter (fun i => f i = z)).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image f S
  change (S.card : ℝ) ≤ (512:ℝ)^3 * U
  rw [hs]
  calc
    _ ≤ ∑ _z ∈ S.image f, U := by
      apply sum_le_sum
      intro z hz
      obtain ⟨k,hk,hkz⟩ := mem_image.mp hz
      have hkR : k ∈ R := (mem_filter.mp (mem_filter.mp hk).1).1
      have hu := (H z ⟨k,mem_filter.mpr ⟨hkR,hkz⟩⟩).2
      have hsub : S.filter (fun i => f i = z) ⊆ R.filter (fun i => f i = z) := by
        intro k hk
        exact mem_filter.mpr
          ⟨(mem_filter.mp (mem_filter.mp (mem_filter.mp hk).1).1).1,(mem_filter.mp hk).2⟩
      exact (show ((S.filter (fun i => f i = z)).card : ℝ) ≤
        (R.filter (fun i => f i = z)).card by exact_mod_cast card_le_card hsub).trans hu
    _ = ((S.image f).card : ℝ) * U := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hU

/-- The original all-dyadic occupancy laws give the relative populations at
every product scale within the original level. -/
theorem dyadic_relative_population {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (R : Finset (Fin n)) (a zeta : ℝ) (level : ℕ)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m ell : ℕ) (hlevel : m+ell ≤ level) (p q : Parent)
    (hq : (relativeAtom D R a (2^m) p (2^ell) q).Nonempty) :
    D.thickness^zeta*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3 ≤
      ((relativeAtom D R a (2^m) p (2^ell) q).card : ℝ) ∧
    ((relativeAtom D R a (2^m) p (2^ell) q).card : ℝ) ≤
      (512:ℝ)^3 * D.thickness^(-zeta)*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3 := by
  have he : (2:ℕ)^ell * 2^m = 2^(m+ell) := by rw [pow_add, Nat.mul_comm]
  have hh := relative_population_bounds D R a m ell p
    (L := D.thickness^zeta*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3)
    (U := D.thickness^(-zeta)*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3)
    (by positivity) (by simpa only [he] using H ⟨m+ell,by omega⟩) q hq
  simpa only [mul_assoc] using hh

/-- At zero height the actual source uses exactly the relative parameter
label above, including the quarter-intercept normalization. -/
lemma source_parentLabel {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ) (m : ℕ)
    (p : Parent) (M : ℕ) (i : Fin (parentLabels D R a (2^m) p).card) :
    parentLabel (source h R E a m p) 0 M i = relativeLabel D a (2^m) p M
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) := by
  simp only [parentLabel, relativeLabel, source_line, shift, zero_div, Int.floor_zero,
    shiftedIntercept, Int.cast_zero, zero_mul, mul_zero, add_zero]

lemma source_parent_population {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ) (m : ℕ)
    (p : Parent) (M : ℕ) (q : Parent) :
    (backbone (source h R E a m p) 0 M q).card =
      (relativeAtom D R a (2^m) p M q).card := by
  simp only [backbone,source_parentLabel]
  exact card_filter_originalLabel (parentLabels D R a (2^m) p)
    (fun i => relativeLabel D a (2^m) p M i = q)

lemma source_parents_eq {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ) (m : ℕ)
    (p : Parent) (M : ℕ) :
    parents (source h R E a m p) 0 M = relativeParents D R a (2^m) p M := by
  ext q
  simp only [parents,relativeParents,mem_image,mem_univ,true_and,source_parentLabel]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,NativePaddedCellSource.originalLabel_mem _ i,hi⟩
  · rintro ⟨i,hi,hiq⟩
    have hir : i ∈ Set.range (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)) := by
      rw [NativePaddedCellSource.originalLabel_range]
      exact hi
    obtain ⟨j,hj⟩ := hir
    exact ⟨j,by rw [hj]; exact hiq⟩

lemma relative_population_sum {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) (M : ℕ)
    {L U : ℝ}
    (H : ∀ q, (relativeAtom D R a N p M q).Nonempty →
      L ≤ ((relativeAtom D R a N p M q).card : ℝ) ∧
      ((relativeAtom D R a N p M q).card : ℝ) ≤ U) :
    L * (relativeParents D R a N p M).card ≤ (parentLabels D R a N p).card ∧
      ((parentLabels D R a N p).card : ℝ) ≤ U * (relativeParents D R a N p M).card := by
  have hsum : ((parentLabels D R a N p).card : ℝ) =
      ∑ q ∈ relativeParents D R a N p M, ((relativeAtom D R a N p M q).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image (relativeLabel D a N p M) (parentLabels D R a N p)
  have hne (q : Parent) (hq : q ∈ relativeParents D R a N p M) :
      (relativeAtom D R a N p M q).Nonempty := by
    obtain ⟨i,hi,hiq⟩ := mem_image.mp hq
    exact ⟨i,mem_filter.mpr ⟨hi,hiq⟩⟩
  constructor
  · rw [hsum]
    calc
      _ = ∑ _q ∈ relativeParents D R a N p M, L := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun q hq => (H q (hne q hq)).1)
  · rw [hsum]
    calc
      _ ≤ ∑ _q ∈ relativeParents D R a N p M, U :=
        sum_le_sum (fun q hq => (H q (hne q hq)).2)
      _ = _ := by simp [mul_comm]

/-- Actual occupied relative labels have the expected M^3 population.
The only additional loss is the fixed projection multiplicity 512^3. -/
theorem dyadic_relative_parent_count {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (R : Finset (Fin n)) (a zeta : ℝ) (level : ℕ)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m ell : ℕ) (hlevel : m+ell ≤ level) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty) :
    D.thickness^(2*zeta)*((2^ell:ℕ):ℝ)^3/(512:ℝ)^3 ≤
      ((relativeParents D R a (2^m) p (2^ell)).card : ℝ) ∧
    ((relativeParents D R a (2^m) p (2^ell)).card : ℝ) ≤
      D.thickness^(-2*zeta)*((2^ell:ℕ):ℝ)^3 := by
  have hs := relative_population_sum D R a (2^m) p (2^ell)
    (dyadic_relative_population D hd R a zeta level H m ell hlevel p)
  have hc := H ⟨m,by omega⟩ p hp
  have hpos : 0 < D.thickness^zeta*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3 := by
    positivity
  have hpos' : 0 < (512:ℝ)^3*D.thickness^(-zeta)*
      ((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3 := by positivity
  have hr : 0 < (1/(((2^ell)*(2^m):ℕ):ℝ)) := by positivity
  have hratio : (1/((2^m:ℕ):ℝ))/(1/(((2^ell)*(2^m):ℕ):ℝ)) = ((2^ell:ℕ):ℝ) := by
    push_cast
    field_simp
  have hl : (D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3)/
      ((512:ℝ)^3*D.thickness^(-zeta)*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3) ≤
      ((relativeParents D R a (2^m) p (2^ell)).card : ℝ) :=
    (div_le_iff₀ hpos').mpr (by simpa only [mul_comm] using hc.1.trans hs.2)
  have hu : ((relativeParents D R a (2^m) p (2^ell)).card : ℝ) ≤
      (D.thickness^(-zeta)*((1/((2^m:ℕ):ℝ))/D.thickness)^3)/
      (D.thickness^zeta*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hs.1.trans hc.2)
  rw [mul_assoc,div_mul_eq_div_div_swap,
    NativeCoarseAncestorCounts.scale_ratio D.thickness _ _ zeta (-zeta) hd hr,
    hratio,show zeta-(-zeta)=2*zeta by ring] at hl
  rw [NativeCoarseAncestorCounts.scale_ratio D.thickness _ _ (-zeta) zeta hd hr,
    hratio,show -zeta-zeta= -2*zeta by ring] at hu
  exact ⟨hl,hu⟩

/-- Population readback for the actual admitted source, with its fixed
zero-height chart and full original parent. No new local profile is assumed. -/
theorem source_dyadic_population {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a zeta : ℝ) (level : ℕ)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m ell : ℕ) (hlevel : m+ell ≤ level) (p q : Parent)
    (hq : (backbone (source h R E a m p) 0 (2^ell) q).Nonempty) :
    let S := source h R E a m p
    D.thickness^zeta/(64:ℝ)^3*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤
      ((backbone S 0 (2^ell) q).card : ℝ) ∧
    ((backbone S 0 (2^ell) q).card : ℝ) ≤
      (8:ℝ)^3*D.thickness^(-zeta)*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 := by
  have hne : (relativeAtom D R a (2^m) p (2^ell) q).Nonempty := by
    apply card_pos.mp
    rw [←source_parent_population h R E a m p (2^ell) q]
    exact card_pos.mpr hq
  obtain ⟨hl,hu⟩ := dyadic_relative_population D h.1.2.1 R a zeta level H m ell hlevel p q hne
  dsimp only
  rw [source_parent_population,source_thickness]
  have he : ((1/((2^ell:ℕ):ℝ))/(((2^m:ℕ):ℝ)*D.thickness/64))^3 =
      (64:ℝ)^3*((1/(((2^ell)*(2^m):ℕ):ℝ))/D.thickness)^3 := by
    push_cast
    ring
  rw [he]
  constructor
  · convert hl using 1; ring
  · convert hu using 1; ring

/-- One explicit scalar budget absorbs both fixed normalization losses into
the native local exponent. This budget never changes the source or its R. -/
theorem source_dyadic_population_power {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a zeta : ℝ) (level : ℕ)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m ell : ℕ) (hlevel : m+ell ≤ level) (p q : Parent)
    (hbudget : (64:ℝ)^3*(source h R E a m p).thickness^e ≤ D.thickness^zeta)
    (hq : (backbone (source h R E a m p) 0 (2^ell) q).Nonempty) :
    let S := source h R E a m p
    S.thickness^e*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤
      ((backbone S 0 (2^ell) q).card : ℝ) ∧
    ((backbone S 0 (2^ell) q).card : ℝ) ≤
      S.thickness^(-e)*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 := by
  let S := source h R E a m p
  have heps : 0 < S.thickness := by rw [source_thickness]; have hd := h.1.2.1; positivity
  obtain ⟨hl,hu⟩ := source_dyadic_population h R E a zeta level H m ell hlevel p q hq
  have hlo : S.thickness^e ≤ D.thickness^zeta/(64:ℝ)^3 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < (64:ℝ)^3)).mpr
    simpa only [mul_comm] using hbudget
  have hb8 : (8:ℝ)^3*S.thickness^e ≤ D.thickness^zeta := by
    exact (mul_le_mul_of_nonneg_right (by norm_num : (8:ℝ)^3 ≤ (64:ℝ)^3)
      (Real.rpow_pos_of_pos heps e).le).trans hbudget
  have hup := NativeActualLocalAdmission.negative_coefficient h.1.2.1 heps hb8
  exact ⟨(mul_le_mul_of_nonneg_right hlo (by positivity)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right hup (by positivity))⟩

/-- Literal dyadic profiles of a finite source in its fixed zero-height
chart. The population law and occupied-parent count are both included. -/
def HasRelativeProfile {n : ℕ} (delta zeta : ℝ) (S : FiniteScaleSource n)
    (remaining : ℕ) : Prop :=
  ∀ ell : ℕ, ell ≤ remaining →
    (delta^(2*zeta)*((2^ell:ℕ):ℝ)^3/(512:ℝ)^3 ≤ ((parents S 0 (2^ell)).card : ℝ) ∧
      ((parents S 0 (2^ell)).card : ℝ) ≤ delta^(-2*zeta)*((2^ell:ℕ):ℝ)^3) ∧
    ∀ q : Parent, (backbone S 0 (2^ell) q).Nonempty →
      delta^zeta/(64:ℝ)^3*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤
        ((backbone S 0 (2^ell) q).card : ℝ) ∧
      ((backbone S 0 (2^ell) q).card : ℝ) ≤
        (8:ℝ)^3*delta^(-zeta)*((1/((2^ell:ℕ):ℝ))/S.thickness)^3

theorem source_relative_profile {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a zeta : ℝ) (level : ℕ)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m : ℕ) (hm : m ≤ level) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty) :
    HasRelativeProfile D.thickness zeta (source h R E a m p) (level-m) := by
  intro ell hell
  have hlevel : m+ell ≤ level := by omega
  refine ⟨?_,fun q hq => source_dyadic_population h R E a zeta level H m ell hlevel p q hq⟩
  rw [source_parents_eq]
  exact dyadic_relative_parent_count D h.1.2.1 R a zeta level H m ell hlevel p hp

/-- The existing admission construction is invoked ONCE. Every relative
profile is derived on its exact R and exact selected E, for the literal
admitted local source. No profile, regularized local R, or replacement
shading is a hypothesis of this source-facing endpoint. -/
theorem compact_original_scheduled_native_relative_profiles
    (K : Set MarkedLine) (hK : IsCompact K) (e alpha : ℝ)
    (he : 0 < e) (halpha : 0 < alpha) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < zeta ∧ 0 < L ∧ 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ K) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset NativeCommonCubicalMesh.Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n ≤ 2*R.card ∧
          wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ (Rel : Fin d → (Fin n × NativeCommonCubicalMesh.Index) →
            (Fin n × NativeCommonCubicalMesh.Index) → Prop),
            (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
            ∀ schedule : Fin g → Fin (level+1),
              (∀j,((2^(schedule j).val:ℕ):ℝ)*D.thickness ≤ D.thickness^alpha) →
              ∃ E, NativeOriginalParentDensityCore.IsCore D original R a eta zeta d g L Rel
                (fun j => 2^(schedule j).val) E ∧
                ∀j p,(NativeOriginalParentDensityCore.parentEdges D a (2^(schedule j).val) E p).Nonempty →
                  let Ep := NativeOriginalParentDensityCore.parentEdges D a (2^(schedule j).val) E p
                  let S := source h R Ep a (schedule j).val p
                  IsWangZakharovNativeFiniteInput S e ∧
                    (∀i,S.line i ∈ NativeUnitParentNormalization.fixedCompactClass) ∧
                    NativeActualLocalAdmission.HasExactTrace h R Ep a (schedule j).val p ∧
                    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
                      (125*175616*16384:ℝ)*(NativeOriginalParentDensityCore.factor d g L:ℝ)*
                        (NativeOriginalParentDensityCore.coreRadix original R L:ℝ)^2*
                        D.thickness^(-eta)*(NativeFiniteKakeyaCounts.multiplicity S).toReal ∧
                    HasRelativeProfile D.thickness zeta S (level-(schedule j).val) := by
  obtain ⟨zeta,L,eta0,delta0,hzeta,hL,heta0,hdelta0,hbase⟩ :=
    NativeActualLocalAdmission.compact_original_scheduled_native_admission K hK e alpha he halpha d g hdg
  refine ⟨zeta,L,eta0,delta0,hzeta,hL,heta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hden,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hden,hCW,H,?_⟩
  intro Rel hrefl hsym schedule hwindow
  obtain ⟨E,hEcore,hlocal⟩ := hcore Rel hrefl hsym schedule hwindow
  refine ⟨E,hEcore,?_⟩
  intro j p hp
  obtain ⟨hnative,hfixed,htrace,hmult⟩ := hlocal j p hp
  refine ⟨hnative,hfixed,htrace,hmult,?_⟩
  have hparent : (parentLabels D R a (2^(schedule j).val) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    have hzR : z.1 ∈ R := (mem_filter.mp (hEcore.1 hzE)).2
    exact ⟨z.1,mem_filter.mpr ⟨hzR,hzp⟩⟩
  exact source_relative_profile h R _ a zeta level H (schedule j).val
    (Nat.le_of_lt_succ (schedule j).isLt) p hparent

end NativeRelativeParentProfiles
