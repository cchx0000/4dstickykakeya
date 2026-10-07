import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_native_coarse_ancestor_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFullReferenceCarrierLower
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeFullCoarseShadow
open NativeCoarseCarrierGeometry NativeCoarseSourceProfiles NativeDyadicParentCells
open NativeCoarseAncestorCounts

/-- Carrier balls of the full ambient source count the complete original
parent image, with the actual contracted representative in every cell. -/
lemma full_carrier_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (level b : ℕ) (E : Finset (Fin n × Index))
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) (r : ℝ) :
    wzCarrierBallCount (fullSource h R a level b E) i r =
      ((R.image (parentLabel D a (2 ^ b))).filter (fun p =>
        dist (carrier D a (representative h R a (2 ^ b) p))
          (carrier D a (representative h R a (2 ^ b)
            (parentIndex (R.image (parentLabel D a (2 ^ b))) i))) ≤ r)).card := by
  exact card_filter_parentIndex (R.image (parentLabel D a (2 ^ b)))
    (fun p => dist (carrier D a (representative h R a (2 ^ b) p))
      (carrier D a (representative h R a (2 ^ b)
        (parentIndex (R.image (parentLabel D a (2 ^ b))) i))) ≤ r)

/-- Full occupied ancestors, before any coloring or pruning, give the lower
carrier-ball law for every genuine tube of the same full coarse source. -/
theorem full_carrier_lower {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i ∈ fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (level b : ℕ) (hb : b ≤ level)
    (E : Finset (Fin n × Index))
    (H : ∀ ell : Fin (level + 1), ∀ p : Parent,
      (R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).Nonempty →
        D.thickness ^ zeta * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
          ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ≤
          D.thickness ^ (-zeta) * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3)
    (i : Fin (R.image (parentLabel D a (2 ^ b))).card) {r : ℝ}
    (hr : (fullSource h R a level b E).thickness ≤ r) (hr1 : r ≤ 1) :
    D.thickness ^ (2 * zeta) * (r / (fullSource h R a level b E).thickness) ^ 3 ≤
      (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) := by
  rw [full_carrier_count]
  exact pruned_carrier_lower h hK ha b (R.image (parentLabel D a (2 ^ b)))
    (representative h R a (2 ^ b))
    (fun p hp => (representative_spec h R a (2 ^ b) hp).2)
    (fun ell p hp => (coarse_ancestor_AD h R a zeta level H (by omega) hb p hp).1)
    (parentIndex (R.image (parentLabel D a (2 ^ b))) i)
    (parentIndex_mem (R.image (parentLabel D a (2 ^ b))) i) hr hr1

/-- Actual two-sided, all-radius carrier AD for the full reference family.
The shading E is arbitrary and does not enter either geometric constant. -/
theorem full_carrier_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀ i, D.line i ∈ fixedCompactClass)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (R : Finset (Fin n)) (level b : ℕ) (hb : b ≤ level)
    (E : Finset (Fin n × Index))
    (hscale : ((2 ^ b : ℕ) : ℝ) * D.thickness ≤ 1)
    (H : ∀ ell : Fin (level + 1), ∀ p : Parent,
      (R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).Nonempty →
        D.thickness ^ zeta * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3 ≤
          ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2 ^ ell.val) i = p)).card : ℝ) ≤
          D.thickness ^ (-zeta) * ((1 / ((2 ^ ell.val : ℕ) : ℝ)) / D.thickness) ^ 3) :
    ∀ i : Fin (R.image (parentLabel D a (2 ^ b))).card, ∀ r : ℝ,
      (fullSource h R a level b E).thickness ≤ r → r ≤ 1 →
        D.thickness ^ (2 * zeta) * (r / (fullSource h R a level b E).thickness) ^ 3 ≤
          (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) ∧
        (wzCarrierBallCount (fullSource h R a level b E) i r : ℝ) ≤
          (5832 * 770 ^ 3) * D.thickness ^ (-zeta) *
            (r / (fullSource h R a level b E).thickness) ^ 3 := by
  intro i r hr hr1
  exact ⟨full_carrier_lower h hK ha R level b hb E H i hr hr1,
    NativeFullReferenceSlopeCap.full_carrier_upper h R level b E hscale
      (fun p hp => (H ⟨b, by omega⟩ p hp).1) i hr⟩

end NativeFullReferenceCarrierLower
