import Theorems.Thm_StickyKakeya4_native_local_parent_cells
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
import Theorems.Thm_StickyKakeya4_uniform_grain_partitions

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section

namespace NativeLocalPairFibers

open Classical Finset MeasureTheory StickyKakeya4
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentSelection
open NativeOriginalPrunedMass
open scoped ENNReal BigOperators

/-- Each original labelled edge is sent to its own original tube label and
the genuine local front cube in that tube's original integer parent. -/
def localPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (e : Fin n × Index) : Fin n × Index :=
  (e.1, NativeLocalParentCells.cellLabel D a N (parentLabel D a N e.1) e.1 e.2)

def localCells {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (a : ℝ) (N : ℕ) (i : Fin n) : Finset Index :=
  NativeLocalParentCells.cells D original a N (parentLabel D a N i) i

def pairFiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (q : Fin n × Index) : Finset (Fin n × Index) :=
  E.filter (fun e => localPair D a N e = q)

/-- This is an ordinary finite relation that can be included, at each
scheduled scale, in the same simultaneous finite uniformization as the
other incidence relations. It does not discard any additional edge. -/
def pairRelation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (e f : Fin n × Index) : Prop := localPair D a N e = localPair D a N f

lemma pairFiber_at_edge {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (e : Fin n × Index) :
    pairFiber D a N E (localPair D a N e) = E.filter (fun f => pairRelation D a N f e) := by
  unfold pairFiber
  apply filter_congr
  intro f _hf
  rfl

/-- Uniformity of this relation on the retained original edge set is
exactly the needed global comparability of its occupied output fibers. -/
lemma comparable_of_relation_uniformity {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (E : Finset (Fin n × Index)) {Q : ℝ}
    (hrel : ∀ e ∈ E, ∀ f ∈ E,
      ((E.filter (fun g => pairRelation D a N g e)).card : ℝ) ≤
        Q * (E.filter (fun g => pairRelation D a N g f)).card) :
    ∀ q ∈ E.image (localPair D a N), ∀ r ∈ E.image (localPair D a N),
      ((pairFiber D a N E q).card : ℝ) ≤ Q * (pairFiber D a N E r).card := by
  intro q hq r hr
  obtain ⟨e, he, rfl⟩ := mem_image.mp hq
  obtain ⟨f, hf, rfl⟩ := mem_image.mp hr
  simpa only [pairFiber_at_edge] using hrel e he f hf

/-- The actual local cube count is bounded by tube volume. There is no
output-count assumption: the front-meeting cubes have mesh N delta / 128
and are contained in the valid tube of thickness N delta / 64. -/
theorem local_cells_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness / 64 ≤ 1)
    (i : Fin n) :
    ((N : ℝ) * D.thickness) * (localCells D original a N i).card ≤
      1024 * volumeConstant := by
  have hd := h.1.2.1
  have hr : 0 < (N : ℝ) * D.thickness := by positivity
  have hs := NativeLocalParentCells.shading_subset_tube h original horiginal ha N hN
    (parentLabel D a N i) i rfl
  have hv := (NativeLocalParentGeometry.valid_slab D a N (parentLabel D a N i) i rfl).1
  have ht := volume_markedUnitTube_upper_bound hv (by positivity :
    0 < (N : ℝ) * D.thickness / 64) hscale
  have hh := (measure_mono hs).trans ht
  rw [volume_wzCellShading (by positivity)] at hh
  have hreal := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (N : ℝ) * D.thickness / 128),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (N : ℝ) * D.thickness / 64),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 2 / 2)] at hreal
  change (localCells D original a N i).card * ((N : ℝ) * D.thickness / 128) ^ 4 ≤
    32 * ((N : ℝ) * D.thickness / 64) ^ 3 * (Real.pi ^ 2 / 2) at hreal
  apply (mul_le_mul_iff_right₀ (pow_pos hr 3)).mp
  calc
    _ = 128 ^ 4 * ((localCells D original a N i).card *
        ((N : ℝ) * D.thickness / 128) ^ 4) := by ring
    _ ≤ 128 ^ 4 * (32 * ((N : ℝ) * D.thickness / 64) ^ 3 * (Real.pi ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hreal (by norm_num)
    _ = _ := by dsimp [volumeConstant]; ring

lemma pair_image_subset {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) :
    E.image (localPair D a N) ⊆ incidences (localCells D original a N) := by
  intro q hq
  obtain ⟨⟨i, k⟩, he, rfl⟩ := mem_image.mp hq
  apply (mem_incidences (localCells D original a N) i _).mpr
  exact mem_image_of_mem _ ((mem_incidences original i k).mp (hE he))

/-- Summing the actual per-tube capacity over the original n labels bounds
the global pair image of every retained subset of original incidences. -/
theorem pair_image_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness / 64 ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) :
    ((N : ℝ) * D.thickness) * (E.image (localPair D a N)).card ≤
      (1024 * volumeConstant) * n := by
  have hd := h.1.2.1
  have hcard : ((E.image (localPair D a N)).card : ℝ) ≤
      (incidences (localCells D original a N)).card := by
    exact_mod_cast card_le_card (pair_image_subset D original a N E hE)
  calc
    _ ≤ ((N : ℝ) * D.thickness) * (incidences (localCells D original a N)).card :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = ∑ i : Fin n, ((N : ℝ) * D.thickness) * (localCells D original a N i).card := by
      rw [card_incidences, Nat.cast_sum, mul_sum]
    _ ≤ ∑ _i : Fin n, 1024 * volumeConstant := sum_le_sum (fun i _ =>
      local_cells_capacity h original horiginal ha N hN hscale i)
    _ = _ := by simp [mul_comm]

/-- Average native shading density and the genuine lower tube-volume
bound give a lower bound on the original labelled incidence count. -/
theorem original_incidence_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (hsmall : D.thickness ≤ 1 / 8) :
    Real.pi ^ 2 * D.thickness ^ eta * n ≤ D.thickness * (incidences original).card := by
  have hd := h.1.2.1
  have htube : (n : ℝ≥0∞) * (ENNReal.ofReal (1 / 8 : ℝ) *
      (ENNReal.ofReal D.thickness) ^ 3 * ENNReal.ofReal (Real.pi ^ 2 / 2)) ≤
      wzTotalTubeVolume D := by
    simpa only [wzTotalTubeVolume, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ =>
        volume_markedUnitTube_lower_bound (h.1.2.2.2.2.1 i) hd hsmall)
  have hh := (mul_le_mul' (le_refl ((ENNReal.ofReal D.thickness).rpow eta)) htube).trans
    h.1.2.2.2.2.2.2.2.2.2.2.2.2
  rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal] at hh
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.rpow_eq_pow] at hr
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le,
    ENNReal.toReal_ofReal (half_pos hd).le,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 8),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 2 / 2)] at hr
  change D.thickness ^ eta * ((n : ℝ) * ((1 / 8) * D.thickness ^ 3 * (Real.pi ^ 2 / 2))) ≤
    (incidences original).card * (D.thickness / 2) ^ 4 at hr
  apply (mul_le_mul_iff_right₀ (pow_pos hd 3)).mp
  calc
    _ = 16 * (D.thickness ^ eta * ((n : ℝ) *
        ((1 / 8) * D.thickness ^ 3 * (Real.pi ^ 2 / 2)))) := by ring
    _ ≤ 16 * ((incidences original).card * (D.thickness / 2) ^ 4) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

/-- A version with coefficient one, useful when an exact geometric
constant is unnecessary. The source remains the native input itself. -/
lemma original_incidence_lower_weak {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (hsmall : D.thickness ≤ 1 / 8) :
    D.thickness ^ eta * n ≤ D.thickness * (incidences original).card := by
  have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hd := h.1.2.1
  calc
    _ = 1 * (D.thickness ^ eta * n) := by ring
    _ ≤ Real.pi ^ 2 * (D.thickness ^ eta * n) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = Real.pi ^ 2 * D.thickness ^ eta * n := by ring
    _ ≤ _ := original_incidence_lower h original horiginal hsmall

/-- Global comparability gives this estimate for every occupied fiber,
without selecting a heavy subfamily after uniformization. -/
lemma cardinal_le_comparable_fiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) {Q : ℝ}
    (hQ : ∀ q ∈ E.image (localPair D a N), ∀ r ∈ E.image (localPair D a N),
      ((pairFiber D a N E q).card : ℝ) ≤ Q * (pairFiber D a N E r).card)
    (q : Fin n × Index) (hq : q ∈ E.image (localPair D a N)) :
    (E.card : ℝ) ≤ (E.image (localPair D a N)).card * Q * (pairFiber D a N E q).card := by
  have hs : (E.card : ℝ) = ∑ r ∈ E.image (localPair D a N),
      ((pairFiber D a N E r).card : ℝ) := by
    exact_mod_cast card_eq_sum_card_image (localPair D a N) E
  calc
    _ = _ := hs
    _ ≤ ∑ _r ∈ E.image (localPair D a N), Q * (pairFiber D a N E q).card :=
      sum_le_sum (fun r hr => hQ r hr q hq)
    _ = _ := by simp [mul_assoc]

/-- A retained original edge family is rich in every pair fiber whenever
the canonical finite refinement gives its image-richness inequality. The
image capacity is taken on the pre-refinement set A, exactly as in the
finite grain-refinement theorem. No new final-fiber uniformity is needed. -/
theorem pair_fiber_lower_of_richness {n : ℕ} {D : FiniteScaleSource n} {eta a F Q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8)
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness / 64 ≤ 1)
    (A : Finset (Fin n × Index)) (hA : A ⊆ incidences original)
    (E : Finset (Fin n × Index))
    (hF : 0 < F) (hQ : 0 < Q)
    (hret : ((incidences original).card : ℝ) ≤ F * E.card)
    (q : Fin n × Index)
    (hrich : (E.card : ℝ) ≤ Q * (A.image (localPair D a N)).card *
      (pairFiber D a N E q).card) :
    D.thickness ^ eta * N / (16384 * F * Q) ≤ (pairFiber D a N E q).card := by
  have hd := h.1.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast h.1.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass := original_incidence_lower h original horiginal hsmall
  have hcapacity := pair_image_capacity h original horiginal ha N hN hscale A hA
  have hret' := hret.trans (mul_le_mul_of_nonneg_left hrich hF.le)
  apply (div_le_iff₀ (by positivity : 0 < 16384 * F * Q)).mpr
  apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos Real.pi_pos) hn)).mp
  calc
    _ = (N : ℝ) * (Real.pi ^ 2 * D.thickness ^ eta * n) := by ring
    _ ≤ (N : ℝ) * (D.thickness * (incidences original).card) :=
      mul_le_mul_of_nonneg_left hmass hNr.le
    _ = ((N : ℝ) * D.thickness) * (incidences original).card := by ring
    _ ≤ ((N : ℝ) * D.thickness) *
        (F * (Q * (A.image (localPair D a N)).card * (pairFiber D a N E q).card)) :=
      mul_le_mul_of_nonneg_left hret' (by positivity)
    _ = (F * Q * (pairFiber D a N E q).card) *
        (((N : ℝ) * D.thickness) * (A.image (localPair D a N)).card) := by ring
    _ ≤ (F * Q * (pairFiber D a N E q).card) * ((1024 * volumeConstant) * n) :=
      mul_le_mul_of_nonneg_left hcapacity (by positivity)
    _ = _ := by dsimp [volumeConstant]; ring

/-- Every occupied actual local pair fiber is large. The only combinatorial
inputs are retained original incidence mass and global fiber comparability.
The fixed constant 16384 comes from cancelling the pi-squared factors in
the genuine native lower and local upper tube-volume bounds. -/
theorem occupied_pair_fiber_lower {n : ℕ} {D : FiniteScaleSource n} {eta a F Q : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8)
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness / 64 ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hF : 0 < F) (hQ : 0 < Q)
    (hret : ((incidences original).card : ℝ) ≤ F * E.card)
    (hcomp : ∀ q ∈ E.image (localPair D a N), ∀ r ∈ E.image (localPair D a N),
      ((pairFiber D a N E q).card : ℝ) ≤ Q * (pairFiber D a N E r).card)
    (q : Fin n × Index) (hq : q ∈ E.image (localPair D a N)) :
    D.thickness ^ eta * N / (16384 * F * Q) ≤ (pairFiber D a N E q).card := by
  apply pair_fiber_lower_of_richness h original horiginal ha hsmall N hN hscale
    E hE E hF hQ hret q
  have hc := cardinal_le_comparable_fiber D a N E hcomp q hq
  calc
    _ ≤ _ := hc
    _ = _ := by ring

/-- Literal readback of the finite uniformization degree at unit weights. -/
lemma unit_degree_eq_pairFiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (e : Fin n × Index) :
    SelfUniform.degree (fun _ : Fin n × Index => 1)
      (fun f g => localPair D a N f = localPair D a N g) E e =
      (pairFiber D a N E (localPair D a N e)).card := by
  rw [SelfUniform.degree, pairFiber, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro f _hf
  by_cases hp : localPair D a N e = localPair D a N f
  · simp only [if_pos hp, if_pos hp.symm]
  · simp only [if_neg hp, if_neg (Ne.symm hp)]

/-- Direct consumer of the exact richness output of
weighted_self_uniform_grain_refinement, with localPair among its label
maps. Both old relation uniformity and this lower bound therefore hold on
the same E; there is no additional selection step. -/
theorem pair_fiber_lower_of_self_uniform_richness {n : ℕ} {D : FiniteScaleSource n}
    {eta a F : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (hsmall : D.thickness ≤ 1 / 8)
    (N : ℕ) (hN : 0 < N) (hscale : (N : ℝ) * D.thickness / 64 ≤ 1)
    (A : Finset (Fin n × Index)) (hA : A ⊆ incidences original)
    (E : Finset (Fin n × Index)) (hF : 0 < F)
    (Q : ℕ) (hQ : 0 < Q)
    (hret : ((incidences original).card : ℝ) ≤ F * E.card)
    (e : Fin n × Index)
    (hrich : SelfUniform.mass (fun _ : Fin n × Index => 1) E ≤
      Q ^ 2 * (A.image (localPair D a N)).card *
        SelfUniform.degree (fun _ : Fin n × Index => 1)
          (fun f g => localPair D a N f = localPair D a N g) E e) :
    D.thickness ^ eta * N / (16384 * F * (Q : ℝ) ^ 2) ≤
      (pairFiber D a N E (localPair D a N e)).card := by
  apply pair_fiber_lower_of_richness h original horiginal ha hsmall N hN hscale
    A hA E hF (by positivity) hret (localPair D a N e)
  have hr : E.card ≤ Q ^ 2 * (A.image (localPair D a N)).card *
      (pairFiber D a N E (localPair D a N e)).card := by
    simpa [SelfUniform.mass, unit_degree_eq_pairFiber] using hrich
  exact_mod_cast hr

end NativeLocalPairFibers
