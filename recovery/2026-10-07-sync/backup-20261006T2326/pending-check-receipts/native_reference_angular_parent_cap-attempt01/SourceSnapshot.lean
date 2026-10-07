/- UNVERIFIED fresh reference-cap proof, separated from pending angular-key readbacks. -/
import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeReferenceAngularParentCap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCoarseDirectionThinning NativeCoarseRepresentativeGeometry
open NativeFullReferenceSlopeCap NativeLocalParentSource NativeLocalParentGeometry
open scoped BigOperators

/-- This cell has the actual final tube width 64/N in all three full slopes. -/
def slopeCell {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (i : Fin n) : Fin 3 → ℤ :=
  fun j => ⌊slope (D.line i) j / (64 / (N : ℝ))⌋

/-- One complete old angular cell can meet only a bounded number of
occupied phase parents, with the explicit fine-reference population loss.
The representative box is derived from its actual same-parent witness. -/
theorem single_cell {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent,
      ((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).Nonempty →
        D.thickness ^ e * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
          (((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).card : ℝ))
    (I : Finset (Fin n)) (q : Fin 3 → ℤ) (hq : ∀ i ∈ I, slopeCell D N i = q) :
    ((I.image (parentLabel D 0 N)).card : ℝ) ≤
      (5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e) := by
  let Q := I.image (parentLabel D 0 N)
  let delta : ℝ := 64 / (N : ℝ)
  let rep := representative h univ 0 N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hQ : Q ⊆ (univ : Finset (Fin n)).image (parentLabel D 0 N) :=
    image_subset_image (subset_univ I)
  have hrep (p : Parent) (hp : p ∈ Q) : parentLabel D 0 N (rep p) = p :=
    (representative_spec h univ 0 N (hQ hp)).2
  have hbox (p : Parent) (hp : p ∈ Q) (j : Fin 3) :
      (q j : ℝ) * delta - delta / 2 ≤ slope (D.line (rep p)) j ∧
      slope (D.line (rep p)) j ≤ ((q j : ℝ) * delta - delta / 2) + 2 * delta := by
    obtain ⟨i, hi, hip⟩ := mem_image.mp hp
    have he : parentLabel D 0 N i = parentLabel D 0 N (rep p) := hip.trans (hrep p hp).symm
    have hclose := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (slope (D.line i) j) (slope (D.line (rep p)) j) N hN
      (congrFun (congrArg Prod.fst he) j)
    have hang : ⌊slope (D.line i) j / delta⌋ = q j := congrFun (hq i hi) j
    have hlo := (le_div_iff₀ hd).mp (Int.floor_le (slope (D.line i) j / delta))
    have hhi := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (slope (D.line i) j / delta))
    rw [hang] at hlo hhi
    have hgap : 1 / (N : ℝ) ≤ delta / 2 := by
      dsimp only [delta]
      have hpos : 0 < 1 / (N : ℝ) := by positivity
      linarith
    obtain ⟨hc0, hc1⟩ := abs_le.mp hclose
    constructor <;> nlinarith only [hlo, hhi, hc0, hc1, hgap]
  have hh := representative_cube_card h univ N hN hscale H Q hQ rep hrep
    (show 0 ≤ 2 * delta by positivity) (fun j => (q j : ℝ) * delta - delta / 2) hbox
  have hside : (N : ℝ) * (2 * delta) + 2 = 130 := by
    dsimp only [delta]
    field_simp [hNr.ne']
    ring
  rw [hside] at hh
  nlinarith only [hh]

/-- Sum the genuine one-cell count over the old full angular union. No
choice of one original point or of one tube per angle is made. -/
theorem phase_card_le_angular_card {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N : ℕ) (hN : 0 < N)
    (hscale : (N : ℝ) * D.thickness ≤ 1)
    (H : ∀ p : Parent,
      ((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).Nonempty →
        D.thickness ^ e * ((1 / (N : ℝ)) / D.thickness) ^ 3 ≤
          (((univ : Finset (Fin n)).filter (fun i => parentLabel D 0 N i = p)).card : ℝ))
    (I : Finset (Fin n)) :
    ((I.image (parentLabel D 0 N)).card : ℝ) ≤
      ((5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e)) * (I.image (slopeCell D N)).card := by
  let angles := I.image (slopeCell D N)
  let parents := fun q => (I.filter (fun i => slopeCell D N i = q)).image (parentLabel D 0 N)
  have he : I.image (parentLabel D 0 N) = angles.biUnion parents := by
    ext p
    constructor
    · rintro hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact mem_biUnion.mpr ⟨slopeCell D N i, mem_image_of_mem _ hi,
        mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, rfl⟩, rfl⟩⟩
    · rintro hp
      obtain ⟨q, _hq, hp⟩ := mem_biUnion.mp hp
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      exact mem_image_of_mem _ (mem_filter.mp hi).1
  calc
    _ = ((angles.biUnion parents).card : ℝ) := by rw [he]
    _ ≤ (∑ q ∈ angles, (parents q).card : ℕ) := by
      exact_mod_cast card_biUnion_le
    _ = ∑ q ∈ angles, ((parents q).card : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ ∑ _q ∈ angles, (5832 * 130 ^ 3 : ℝ) * D.thickness ^ (-e) := by
      apply sum_le_sum
      intro q _hq
      exact single_cell h N hN hscale H (I.filter (fun i => slopeCell D N i = q)) q
        (fun i hi => (mem_filter.mp hi).2)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, angles]; ring

/-- Same admitted E1-parent reader. Its entire population premise is
constructed from the original HB; the incidence set remains arbitrary. -/
theorem same_reference_phase_card {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m + b ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (hbudget : (64 : ℝ)^3 * (source h R Eref a m p).thickness ^ e ≤ D.thickness ^ zeta)
    (I : Finset (Fin (parentLabels D R a (2^m) p).card)) :
    let S := source h R Eref a m p
    ((I.image (parentLabel S 0 (2^b))).card : ℝ) ≤
      ((5832 * 130 ^ 3 : ℝ) * S.thickness ^ (-e)) * (I.image (slopeCell S (2^b))).card := by
  intro S
  have hdy := HB.2.1
  have hscale := NativeSameReferenceChartBounds.source_scale_guard h R Eref level m b p hdy hmb
  have Hpop := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b hmb p hbudget
  exact phase_card_le_angular_card hReferenceNative (2^b) (by positivity) hscale
    (fun q hq => (Hpop ⟨b, by omega⟩ q hq).1) I


end NativeReferenceAngularParentCap
