import Theorems.Thm_StickyKakeya4_native_local_pair_uniform_core
import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeOriginalParentDensityCore
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalPrunedMass
open NativeLocalPairFibers NativeLocalPairUniformCore SelfUniform
open scoped ENNReal BigOperators

/-- Literal original incidences on the retained original labels. Empty rows
remain in R and in every parent backbone throughout this construction. -/
def retained {n : ℕ} (original : Fin n → Finset Index) (R : Finset (Fin n)) :
    Finset (Fin n × Index) := (incidences original).filter (fun e => e.1 ∈ R)

def parentEdges {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) : Finset (Fin n × Index) :=
  E.filter (fun e => parentLabel D a N e.1 = p)

lemma retained_card {n : ℕ} (original : Fin n → Finset Index) (R : Finset (Fin n)) :
    (retained original R).card = ∑ i ∈ R, (original i).card := by
  rw [card_eq_sum_card_fiberwise (s := retained original R) (f := Prod.fst) (t := R)
    (fun e he => (mem_filter.mp he).2)]
  apply sum_congr rfl
  intro i hi
  have he : (retained original R).filter (fun e => e.1 = i) =
      (original i).image (fun k => (i, k)) := by
    ext e
    rcases e with ⟨j, k⟩
    simp only [retained, mem_filter, mem_incidences, mem_image, Prod.mk.injEq]
    aesop
  rw [he, card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]

/-- Exact cubical volume, with all original cells on R. -/
lemma retained_shading_eq {n : ℕ} (D : FiniteScaleSource n) (hd : 0 < D.thickness)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) :
    shadingMass D R = (retained original R).card * (ENNReal.ofReal (mesh D)) ^ 4 := by
  unfold shadingMass
  simp_rw [horiginal]
  simp_rw [volume_wzCellShading (show 0 < mesh D from half_pos hd)]
  rw [← sum_mul]
  congr 1
  exact_mod_cast (retained_card original R).symm

/-- Half of the ORIGINAL shading volume is exactly half of the original
incidence mass on the common mesh. This supplies the factor two in F. -/
lemma original_card_le_twice_retained {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) (hshade : wzTotalShadingVolume D ≤ 2 * shadingMass D R) :
    (incidences original).card ≤ 2 * (retained original R).card := by
  rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal,
    retained_shading_eq D hd original horiginal R] at hshade
  have hr := ENNReal.toReal_mono (by finiteness) hshade
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, mesh, ENNReal.toReal_ofReal (half_pos hd).le] at hr
  have hh : ((incidences original).card : ℝ) ≤ 2 * (retained original R).card := by
    apply (mul_le_mul_iff_left₀ (pow_pos (half_pos hd) 4)).mp
    simpa only [mesh, mul_assoc] using hr
  exact_mod_cast hh

lemma unit_degree_eq_parentEdges {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (E : Finset (Fin n × Index)) (e : Fin n × Index) :
    degree (fun _ : Fin n × Index => 1)
      (fun f g => parentLabel D a N f.1 = parentLabel D a N g.1) E e =
      (parentEdges D a N E (parentLabel D a N e.1)).card := by
  rw [degree, parentEdges, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro f _hf
  by_cases hp : parentLabel D a N e.1 = parentLabel D a N f.1
  · simp only [if_pos hp, if_pos hp.symm]
  · simp only [if_neg hp, if_neg (Ne.symm hp)]

/-- Source population laws bound the total number of R parents times the
FULL R population of any occupied parent. No incidence-active tube cut occurs. -/
lemma parent_population_product {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a zeta : ℝ) (N : ℕ)
    (hd : 0 < D.thickness) (hN : 0 < N)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a N i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a N i = p)).card : ℝ) ∧
      ((R.filter (fun i => parentLabel D a N i = p)).card : ℝ) ≤
        D.thickness ^ (-zeta) * ((1 / (N : ℝ)) / D.thickness) ^ 3)
    (p : Parent) (hp : (R.filter (fun i => parentLabel D a N i = p)).Nonempty) :
    ((R.image (parentLabel D a N)).card : ℝ) *
        (R.filter (fun i => parentLabel D a N i = p)).card ≤
      n * D.thickness ^ (-(2 * zeta)) := by
  let v : ℝ := ((1 / (N : ℝ)) / D.thickness) ^ 3
  have hv : 0 < v := by dsimp [v]; positivity
  have hsum : ((R.image (parentLabel D a N)).card : ℝ) * (D.thickness ^ zeta * v) ≤ n := by
    calc
      _ = ∑ _q ∈ R.image (parentLabel D a N), D.thickness ^ zeta * v := by simp
      _ ≤ ∑ q ∈ R.image (parentLabel D a N),
          ((R.filter (fun i => parentLabel D a N i = q)).card : ℝ) := by
        apply sum_le_sum
        intro q hq
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
        exact (H _ ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩).1
      _ = R.card := by exact_mod_cast (card_eq_sum_card_image (parentLabel D a N) R).symm
      _ ≤ n := by exact_mod_cast (show R.card ≤ n by simpa using card_le_univ R)
  have hcancel : D.thickness ^ (-zeta) =
      D.thickness ^ zeta * D.thickness ^ (-(2 * zeta)) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ hv).mp
  calc
    _ ≤ (((R.image (parentLabel D a N)).card : ℝ) *
        (D.thickness ^ (-zeta) * v)) * v :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (H p hp).2 (by positivity)) hv.le
    _ = (((R.image (parentLabel D a N)).card : ℝ) *
        (D.thickness ^ zeta * v)) * D.thickness ^ (-(2 * zeta)) * v := by
      rw [hcancel]
      ring
    _ ≤ (n * D.thickness ^ (-(2 * zeta))) * v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (Real.rpow_pos_of_pos hd _).le) hv.le

/-- Uniform parent fibers control the SAME retained edge set at every active
parent, using all R parents in the counting bound. -/
lemma cardinal_le_parent_fiber {n : ℕ} (D : FiniteScaleSource n)
    (R : Finset (Fin n)) (a : ℝ) (N Q : ℕ) (E : Finset (Fin n × Index))
    (hER : ∀ e ∈ E, e.1 ∈ R)
    (hcomp : ∀ e f, e ∈ E → f ∈ E →
      (parentEdges D a N E (parentLabel D a N e.1)).card ≤
        Q ^ 2 * (parentEdges D a N E (parentLabel D a N f.1)).card)
    (p : Parent) (hp : (parentEdges D a N E p).Nonempty) :
    E.card ≤ Q ^ 2 * (R.image (parentLabel D a N)).card * (parentEdges D a N E p).card := by
  obtain ⟨hf, hfp⟩ := mem_filter.mp hp.choose_spec
  have hbound : ∀ q ∈ R.image (parentLabel D a N),
      (parentEdges D a N E q).card ≤ Q ^ 2 * (parentEdges D a N E p).card := by
    intro q _hq
    by_cases hq : (parentEdges D a N E q).Nonempty
    · obtain ⟨e, he⟩ := hq
      obtain ⟨heE, heq⟩ := mem_filter.mp he
      simpa only [heq, hfp] using hcomp e hp.choose heE hf
    · simp only [not_nonempty_iff_eq_empty.mp hq, card_empty, Nat.zero_le]
  calc
    E.card = ∑ q ∈ R.image (parentLabel D a N), (parentEdges D a N E q).card :=
      card_eq_sum_card_fiberwise (fun e he => mem_image_of_mem _ (hER e he))
    _ ≤ ∑ _q ∈ R.image (parentLabel D a N), Q ^ 2 * (parentEdges D a N E p).card :=
      sum_le_sum hbound
    _ = _ := by simp [Nat.mul_left_comm, Nat.mul_assoc]

/-- The global native average density cancels the ACTUAL original n against
the all-parent population comparison. It is an aggregate parent statement. -/
theorem parent_average_density {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (hsmall : D.thickness ≤ 1 / 8) (R : Finset (Fin n))
    (N Q F : ℕ) (hN : 0 < N) (E : Finset (Fin n × Index))
    (hER : ∀ e ∈ E, e.1 ∈ R)
    (hret : (incidences original).card ≤ F * E.card)
    (hcomp : ∀ e f, e ∈ E → f ∈ E →
      (parentEdges D a N E (parentLabel D a N e.1)).card ≤
        Q ^ 2 * (parentEdges D a N E (parentLabel D a N f.1)).card)
    (H : ∀ p : Parent, (R.filter (fun i => parentLabel D a N i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a N i = p)).card : ℝ) ∧
      ((R.filter (fun i => parentLabel D a N i = p)).card : ℝ) ≤
        D.thickness ^ (-zeta) * ((1 / (N : ℝ)) / D.thickness) ^ 3)
    (p : Parent) (hp : (parentEdges D a N E p).Nonempty) :
    D.thickness ^ (eta + 2 * zeta) *
        (R.filter (fun i => parentLabel D a N i = p)).card ≤
      D.thickness * F * (Q : ℝ) ^ 2 * (parentEdges D a N E p).card := by
  have hd := h.1.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast h.1.1
  have hback : (R.filter (fun i => parentLabel D a N i = p)).Nonempty := by
    obtain ⟨e, he⟩ := hp
    obtain ⟨heE, hep⟩ := mem_filter.mp he
    exact ⟨e.1, mem_filter.mpr ⟨hER e heE, hep⟩⟩
  have hpop := parent_population_product D R a zeta N hd hN H p hback
  have hcard : (E.card : ℝ) ≤ (Q : ℝ) ^ 2 *
      (R.image (parentLabel D a N)).card * (parentEdges D a N E p).card := by
    exact_mod_cast cardinal_le_parent_fiber D R a N Q E hER hcomp p hp
  have hret' : ((incidences original).card : ℝ) ≤ (F : ℝ) * E.card := by
    exact_mod_cast hret
  have hmass := (original_incidence_lower_weak h original horiginal hsmall).trans
    (mul_le_mul_of_nonneg_left hret' hd.le)
  have hcancel : D.thickness ^ (-(2 * zeta)) * D.thickness ^ (2 * zeta) = 1 := by
    rw [← Real.rpow_add hd]
    simp
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    _ = (D.thickness ^ eta * n) * D.thickness ^ (2 * zeta) *
        (R.filter (fun i => parentLabel D a N i = p)).card := by
      rw [Real.rpow_add hd]
      ring
    _ ≤ (D.thickness * ((F : ℝ) * E.card)) * D.thickness ^ (2 * zeta) *
        (R.filter (fun i => parentLabel D a N i = p)).card := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmass (Real.rpow_pos_of_pos hd _).le) (by positivity)
    _ ≤ (D.thickness * ((F : ℝ) * ((Q : ℝ) ^ 2 *
        (R.image (parentLabel D a N)).card * (parentEdges D a N E p).card))) *
        D.thickness ^ (2 * zeta) * (R.filter (fun i => parentLabel D a N i = p)).card := by
      gcongr
    _ = (D.thickness * (F : ℝ) * (Q : ℝ) ^ 2 * (parentEdges D a N E p).card) *
        (((R.image (parentLabel D a N)).card : ℝ) *
          (R.filter (fun i => parentLabel D a N i = p)).card) * D.thickness ^ (2 * zeta) := by ring
    _ ≤ (D.thickness * (F : ℝ) * (Q : ℝ) ^ 2 * (parentEdges D a N E p).card) *
        (n * D.thickness ^ (-(2 * zeta))) * D.thickness ^ (2 * zeta) := by
      gcongr
    _ = _ := by simp only [mul_assoc, hcancel, mul_one]

/-- Original-incidence retention includes the canonical half-shading loss. -/
def factor (d g L : ℕ) : ℕ := 2 * retentionCost (d + g) g L

def coreRadix {n : ℕ} (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (L : ℕ) : ℕ := NativeSourceSizeBounds.radix (retained original R).card L

/-- Every property is asserted about one literal original edge set E. -/
def IsCore {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a eta zeta : ℝ) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (scales : Fin g → ℕ) (E : Finset (Fin n × Index)) : Prop :=
  let Q := coreRadix original R L
  E ⊆ retained original R ∧ E.Nonempty ∧
  (incidences original).card ≤ factor d g L * E.card ∧
  (∀ j e f, e ∈ E → f ∈ E →
    degree (fun _ : Fin n × Index => 1) (Rel j) E e ≤
      Q ^ 2 * degree (fun _ : Fin n × Index => 1) (Rel j) E f) ∧
  (∀ j e f, e ∈ E → f ∈ E →
    (parentEdges D a (scales j) E (parentLabel D a (scales j) e.1)).card ≤
      Q ^ 2 * (parentEdges D a (scales j) E (parentLabel D a (scales j) f.1)).card) ∧
  (∀ j p, (parentEdges D a (scales j) E p).Nonempty →
    D.thickness ^ (eta + 2 * zeta) *
        (R.filter (fun i => parentLabel D a (scales j) i = p)).card ≤
      D.thickness * (factor d g L : ℝ) * (Q : ℝ) ^ 2 * (parentEdges D a (scales j) E p).card) ∧
  (∀ j e, e ∈ E →
    D.thickness ^ eta * scales j /
      (16384 * (factor d g L : ℝ) * (Q : ℝ) ^ 2) ≤
        (pairFiber D a (scales j) E (localPair D a (scales j) e)).card)

/-- One use of the verified scheduled constructor: actual parent relations
are appended to the old relation menu before its single uniformization. -/
theorem exists_retained_parent_density_core {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8) (R : Finset (Fin n))
    (hshade : wzTotalShadingVolume D ≤ 2 * shadingMass D R)
    (d g L : ℕ) (hdg : 0 < d + g) (hL : 0 < L)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀ j x, Rel j x x) (hsym : ∀ j x y, Rel j x y → Rel j y x)
    (scales : Fin g → ℕ) (hN : ∀ j, 0 < scales j)
    (hscale : ∀ j, (scales j : ℝ) * D.thickness / 64 ≤ 1)
    (H : ∀ j p, (R.filter (fun i => parentLabel D a (scales j) i = p)).Nonempty →
      D.thickness ^ zeta * ((1 / (scales j : ℝ)) / D.thickness) ^ 3 ≤
        ((R.filter (fun i => parentLabel D a (scales j) i = p)).card : ℝ) ∧
      ((R.filter (fun i => parentLabel D a (scales j) i = p)).card : ℝ) ≤
        D.thickness ^ (-zeta) * ((1 / (scales j : ℝ)) / D.thickness) ^ 3) :
    ∃ E, IsCore D original R a eta zeta d g L Rel scales E := by
  let A := retained original R
  have hhalf := original_card_le_twice_retained D h.1.2.1 original horiginal R hshade
  have hA : A ⊆ incidences original := filter_subset _ _
  have hAne : A.Nonempty := by
    have hn : (0 : ℝ) < n := by exact_mod_cast h.1.1
    have hm := original_incidence_lower_weak h original horiginal hsmall
    apply card_pos.mp
    by_contra hz
    have hc : A.card = 0 := by omega
    have hi : (incidences original).card = 0 := by change _ ≤ 2 * A.card at hhalf; omega
    rw [hi, Nat.cast_zero, mul_zero] at hm
    exact (not_le_of_gt (mul_pos (Real.rpow_pos_of_pos h.1.2.1 eta) hn)) hm
  let T : Fin (d + g) → (Fin n × Index) → (Fin n × Index) → Prop :=
    Fin.addCases Rel (fun j e f => parentLabel D a (scales j) e.1 = parentLabel D a (scales j) f.1)
  have hTrefl : ∀ j x, T j x x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x
      simpa only [T, Fin.addCases_left] using hrefl k x
    · intro k x
      simp only [T, Fin.addCases_right]
  have hTsym : ∀ j x y, T j x y → T j y x := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro k x y
      simpa only [T, Fin.addCases_left] using hsym k x y
    · intro k x y
      simpa only [T, Fin.addCases_right] using
        (fun hh : parentLabel D a (scales k) x.1 = parentLabel D a (scales k) y.1 => hh.symm)
  obtain ⟨E, hEA, hEne, hret, hUniform, hPair⟩ :=
    exists_retained_scheduled_pair_core h original horiginal ha hsmall A hA hAne
      (F0 := 2) (by norm_num) (by exact_mod_cast hhalf)
      (d + g) g L (by omega) hL T hTrefl hTsym scales hN hscale
  have hretOriginal : (incidences original).card ≤ factor d g L * E.card := by
    calc
      _ ≤ 2 * A.card := hhalf
      _ ≤ 2 * (retentionCost (d + g) g L * E.card) := Nat.mul_le_mul_left 2 hret
      _ = _ := by dsimp [factor]; ring
  have hER : ∀ e ∈ E, e.1 ∈ R := fun e he => (mem_filter.mp (hEA he)).2
  have hParent : ∀ j e f, e ∈ E → f ∈ E →
      (parentEdges D a (scales j) E (parentLabel D a (scales j) e.1)).card ≤
        (coreRadix original R L) ^ 2 *
          (parentEdges D a (scales j) E (parentLabel D a (scales j) f.1)).card := by
    intro j e f he hf
    have hh := hUniform (Fin.natAdd d j) e f he hf
    simpa only [T, Fin.addCases_right, unit_degree_eq_parentEdges, coreRadix, A] using hh
  refine ⟨E, hEA, hEne, hretOriginal, ?_, hParent, ?_, ?_⟩
  · intro j e f he hf
    simpa only [T, Fin.addCases_left, coreRadix, A] using hUniform (Fin.castAdd g j) e f he hf
  · intro j p hp
    exact parent_average_density h original horiginal hsmall R (scales j)
      (coreRadix original R L) (factor d g L) (hN j) E hER hretOriginal (hParent j) (H j) p hp
  · intro j e he
    simpa only [factor, Nat.cast_mul, Nat.cast_ofNat, coreRadix, A] using hPair j e he

/-- Source-facing finite-schedule endpoint. The canonical compact theorem
chooses R ONCE; its original mass, CW and every dyadic population law are
preserved. For each finite relation/scale menu a SINGLE original incidence
core carries old uniformity, all active-parent average density, and every
native local-pair fiber lower bound simultaneously. -/
theorem compact_original_scheduled_parent_density_core
    (K : Set MarkedLine) (hK : IsCompact K) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i, D.line i ∈ K) →
      D.thickness ≤ delta0 → eta ≤ zeta / 16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
        (∀ i, D.shading i = wzCellShading (mesh D) original i) ∧
        D.thickness = (2 : ℝ)⁻¹ ^ level ∧
        (∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
          Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) ∧
        R.Nonempty ∧ n ≤ 2 * R.card ∧
        wzTotalShadingVolume D ≤ 2 * shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta * tubeMass D R ≤ shadingMass D R ∧
        (∀ U : Set E4, Convex ℝ U →
          ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card : ℝ≥0∞) ≤
            (ENNReal.ofReal D.thickness).rpow (-zeta) * volume U * R.card) ∧
        (∀ (ell : Fin (level + 1)) (p : Parent),
          (R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).Nonempty →
            D.thickness ^ zeta * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
              ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ≤
              D.thickness ^ (-zeta) * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3) ∧
        ∀ (d g L : ℕ), 0 < d + g → 0 < L →
          ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
            (∀ j x, Rel j x x) → (∀ j x y, Rel j x y → Rel j y x) →
            ∀ schedule : Fin g → Fin (level + 1),
              ∃ E, IsCore D original R a eta zeta d g L Rel
                (fun j => 2 ^ (schedule j).val) E := by
  obtain ⟨db, hdb, hbase⟩ :=
    NativeCompactAncestorRegularity.compact_original_ancestor_regularization K hK hzeta
  refine ⟨min db (1 / 8), lt_min hdb (by norm_num), ?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a, level, R, hdy, ha, hR, hhalf, hshade, hden, hCW, H⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) heta
  obtain ⟨original, horiginal⟩ := input_exists_common_cells h
  refine ⟨a, level, R, original, horiginal, hdy, ha, hR, hhalf, hshade, hden, hCW, H, ?_⟩
  intro d g L hdg hL Rel hrefl hsym schedule
  apply exists_retained_parent_density_core h original horiginal ha
    (hsmall.trans (min_le_right _ _)) R hshade d g L hdg hL Rel hrefl hsym
    (fun j => 2 ^ (schedule j).val) (fun _ => by positivity)
  · intro j
    have hh := NativeCompactAncestorRegularity.dyadic_parent_scale hdy (schedule j)
    linarith
  · intro j p hp
    exact H (schedule j) p hp

end NativeOriginalParentDensityCore
